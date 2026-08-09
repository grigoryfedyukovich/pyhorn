"""Bounded reachability validation for candidates removed by Houdini.

When :class:`.MultiHoudini` removes a candidate, it does so because a single
CHC rule's *transition relation* -- rule body plus the active candidates for
the source and destination predicates -- has a model where the candidate
fails. That model is a counterexample to induction (a "CTI"): a valid
witness of the *local* induction check, but not necessarily anything a real,
concrete unrolling of the program from ``ENTRY`` can ever actually trigger.
Houdini itself never checks that: it is sound (a removed candidate really is
not inductive as stated) but its local reasoning can flag a candidate as
non-inductive even when nothing in the actual program ever falsifies it --
typically because the candidate is true, but only in conjunction with a
second invariant ("helper lemma") that Houdini did not have available as a
separate candidate.

This module does **not** validate the CTI. A CTI is one satisfying
assignment of ``source_candidates(src_args) AND rule.body AND NOT
candidate(dst_args)`` -- a single point picked by whichever solver happened
to run, including arbitrary values for any variable the active candidate set
at the time did not constrain (e.g. a loop counter no retained candidate
mentions). Checking whether *that specific point* is reachable would make
the answer depend on solver internals rather than on the program: the same
genuinely-bad candidate could come back "not found" on one run and
"reachable" on another, purely because an irrelevant variable's reported
value happened to differ. What is actually being validated is the
**candidate itself**: does some real, bounded execution of the program
reaching the candidate's relation -- via any sequence of rules that can
produce it, not only whichever one rule Houdini's countermodel happened to
come from -- land in a state where the candidate does not hold? That is a
property of the formula, existentially quantified over every variable except
the candidate's own, not of any one witness. This is exactly the question
:func:`render_candidate_verification_smt2` (``--dump-promising-candidates``)
asks in full, unbounded generality via ``forall``; this module asks the same
question bounded, for a quick, incremental first check (the same
``ENTRY``-to-relation trace machinery :class:`.BoundedExplorer` uses for
query reachability, generalized to an arbitrary target relation).

- **Reachable** -- some concrete trace reaching the candidate's relation
  falsifies it; the removal is confirmed correct.
- **Not found within the bound** -- no such trace exists up to ``upto``
  steps. This does *not* prove the candidate is a true invariant (a longer
  trace might still falsify it), but it is a useful signal: the candidate
  may hold everywhere Houdini could not keep it inductive only because it is
  not provable on its own, and might become inductive once paired with an
  additional candidate.
- **Unknown** -- Z3 could not decide at least one of the checks performed
  (e.g. a timeout), and no reachable witness was found first.
- **Not applicable** -- the removal came from a fact rule, which has no
  source predicate. A fact rule's post-state is asserted directly at the
  first step of any trace, so it is trivially found ``REACHABLE`` at depth 1
  by the very same check; this status is purely a fast path that skips
  spending a solver call on that foregone conclusion.

This check is deliberately simple rather than maximally optimized: a fresh
``z3.Solver()`` per candidate trace, no incremental reuse or infeasible-
prefix pruning across depths (contrast :class:`.BoundedExplorer`, which
carries that complexity for exhaustive query-reachability search over many
traces at once). ``VerificationConditionBuilder``'s own per-(rule, step)
cache is still shared across depths and across candidates when the same
builder instance is reused, which is what keeps repeated calls quick.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from time import perf_counter
from typing import Iterator

import z3

from .horn import ENTRY, HornProgram, HornRule
from .houdini import RemovedCandidate
from .seedminer import VariableMap
from .vc import VerificationConditionBuilder

DEFAULT_CANDIDATE_BOUND = 10


class CandidateReachability(str, Enum):
    REACHABLE = "reachable"
    NOT_FOUND = "not-found"
    UNKNOWN = "unknown"
    NOT_APPLICABLE = "not-applicable"


@dataclass(frozen=True)
class CandidateValidation:
    """Outcome of bound-checking one removed candidate against real unrollings."""

    status: CandidateReachability
    checked_upto: int
    witness_depth: int | None  # set only when status is REACHABLE
    elapsed_seconds: float
    checks_performed: int
    reason_unknown: str | None = None


def _traces_reaching(
    program: HornProgram,
    target: z3.FuncDeclRef,
    length: int,
) -> Iterator[tuple[HornRule, ...]]:
    """Yield every ``ENTRY``-rooted rule trace of exactly ``length`` steps
    whose final step's destination is ``target``.

    Unlike :meth:`.BoundedExplorer.traces_of_length` (which stops extending a
    path the moment it reaches a query relation, since those are terminal by
    construction), this does *not* stop early when an intermediate step
    reaches ``target``: ``target`` is an ordinary predicate and may
    legitimately be revisited by a longer trace (the extremely common
    self-loop shape, e.g. ``inv -> inv``, depends on exactly this).
    """
    if length < 1:
        return
    stack: list[tuple[z3.FuncDeclRef | None, int, tuple[HornRule, ...]]] = [
        (ENTRY, length, ())
    ]
    while stack:
        relation, remaining, trace = stack.pop()
        for rule in program.outgoing.get(relation, ()):
            next_trace = trace + (rule,)
            if remaining == 1:
                if rule.dst_relation == target:
                    yield next_trace
            else:
                stack.append((rule.dst_relation, remaining - 1, next_trace))


def _build_open_trace(
    builder: VerificationConditionBuilder,
    trace: tuple[HornRule, ...],
) -> tuple[list[z3.BoolRef], tuple[z3.ExprRef, ...]]:
    """Build the SSA step constraints for a trace ending at an arbitrary
    (non-query) relation, returning them alongside that relation's final SSA
    variables.

    :meth:`VerificationConditionBuilder.build` refuses traces that do not end
    in a query relation; :func:`_traces_reaching` only ever yields traces
    ending at ``target``, which callers of this module guarantee is
    non-query (see :func:`validate_candidate_reachability`), so
    ``destination_state`` is never ``None`` on the final step here.
    """
    constraints: list[z3.BoolRef] = []
    final_variables: tuple[z3.ExprRef, ...] | None = None
    for step_index, rule in enumerate(trace):
        step = builder.build_step(rule, step_index)
        constraints.append(step.constraint)
        final_variables = (
            None if step.destination_state is None else step.destination_state.variables
        )
    if final_variables is None:
        raise RuntimeError(
            "internal error: trace from _traces_reaching did not end at a "
            "non-query relation"
        )
    return constraints, final_variables


def validate_candidate_reachability(
    program: HornProgram,
    relation: z3.FuncDeclRef,
    candidate: z3.BoolRef,
    canonical: tuple[z3.ExprRef, ...],
    *,
    upto: int = DEFAULT_CANDIDATE_BOUND,
    timeout_ms: int = 1000,
    builder: VerificationConditionBuilder | None = None,
) -> CandidateValidation:
    """Check whether some real, bounded execution of the program reaching
    ``relation`` can falsify ``candidate``.

    ``candidate`` must be expressed over ``canonical`` -- ``relation``'s own
    canonical variables (the same convention :data:`.CandidateMap` and
    :attr:`.RemovedCandidate.candidate_expr` already use).

    This is the bounded counterpart of exactly what
    :func:`render_candidate_verification_smt2` checks in full, unbounded
    generality via ``forall``: for each depth 1, 2, ..., ``upto``, every
    trace of that length from ``ENTRY`` to ``relation`` -- via *any*
    sequence of rules that can produce it, not only whichever one rule
    Houdini's own countermodel happened to come from -- is checked for
    satisfiability together with the negation of ``candidate`` substituted
    onto that trace's own final SSA state. Every variable other than
    ``relation``'s own canonical ones is left completely free (existentially
    quantified) rather than pinned to any witness a solver happened to
    report, which is what makes this sound against "don't-care" variables
    (see the module docstring): the same genuinely-false candidate must get
    the same verdict no matter which rule or which other candidates were
    active when Houdini removed it. Note that this checks reachability of
    *the candidate*, not of any particular counterexample-to-induction (CTI)
    Houdini's own solver happened to report -- see the module docstring for
    why that distinction matters.

    Returns as soon as any check is SAT (``REACHABLE``). If every check at
    every depth is decisively UNSAT, returns ``NOT_FOUND``. If at least one
    check could not be decided and no SAT witness was found first, returns
    ``UNKNOWN`` rather than the more confident ``NOT_FOUND`` -- an undecided
    check means the search was incomplete, not that it came back negative.

    Parameters
    ----------
    program:
        The (ideally unsliced -- see ``--cands``/``--seed-houdini``'s
        ``slice_program=False``) CHC program the candidate came from.
    relation:
        Target predicate; must not be a query relation (query relations
        never carry candidates to remove in the first place).
    upto:
        Maximum trace length to try.
    timeout_ms:
        Per-check Z3 timeout.
    builder:
        Reuse an existing :class:`.VerificationConditionBuilder` to share its
        per-(rule, step) SSA cache across multiple validations (e.g. when
        validating every removed candidate from one Houdini run). A fresh one
        is created if omitted.
    """
    started = perf_counter()
    vc_builder = builder if builder is not None else VerificationConditionBuilder(program)
    checks = 0
    first_unknown_reason: str | None = None

    for depth in range(1, upto + 1):
        for trace in _traces_reaching(program, relation, depth):
            constraints, final_variables = _build_open_trace(vc_builder, trace)

            solver = z3.Solver()
            solver.set(timeout=timeout_ms)
            for constraint in constraints:
                solver.add(constraint)
            violated = z3.substitute(
                candidate, *zip(canonical, final_variables, strict=True)
            )
            solver.add(z3.Not(violated))

            checks += 1
            outcome = solver.check()
            if outcome == z3.sat:
                return CandidateValidation(
                    status=CandidateReachability.REACHABLE,
                    checked_upto=depth,
                    witness_depth=depth,
                    elapsed_seconds=perf_counter() - started,
                    checks_performed=checks,
                )
            if outcome == z3.unknown and first_unknown_reason is None:
                first_unknown_reason = solver.reason_unknown()

    status = (
        CandidateReachability.UNKNOWN
        if first_unknown_reason is not None
        else CandidateReachability.NOT_FOUND
    )
    return CandidateValidation(
        status=status,
        checked_upto=upto,
        witness_depth=None,
        elapsed_seconds=perf_counter() - started,
        checks_performed=checks,
        reason_unknown=first_unknown_reason,
    )


def validate_removed_candidate(
    program: HornProgram,
    variables: VariableMap,
    removed: RemovedCandidate,
    *,
    upto: int = DEFAULT_CANDIDATE_BOUND,
    timeout_ms: int = 1000,
    builder: VerificationConditionBuilder | None = None,
) -> CandidateValidation:
    """Bound-check one :class:`.RemovedCandidate`'s reachability.

    Looks up *removed*'s relation (by :attr:`.RemovedCandidate.relation`, via
    *variables*) and delegates to :func:`validate_candidate_reachability`
    with :attr:`.RemovedCandidate.candidate_expr` -- never
    :attr:`.RemovedCandidate.pre_values` (the countermodel Houdini's own
    solver reported); see the module docstring for why.

    Reuse the same *builder* across multiple calls (e.g. one per removed
    candidate from a single Houdini run) to share SSA step construction for
    prefixes those candidates' traces have in common.

    Fact-rule removals (:attr:`.RemovedCandidate.pre_relation` is ``None``)
    take a fast path straight to :attr:`CandidateReachability.NOT_APPLICABLE`
    rather than spending a solver call: a fact's post-state is asserted
    directly at the first step of any trace, so
    :func:`validate_candidate_reachability` would find it ``REACHABLE`` at
    depth 1 regardless -- this is purely an optimization, not a different
    code path's answer.

    Raises
    ------
    KeyError
        If *removed*'s relation name is not present in *variables*.
    ValueError
        If *removed* has no ``candidate_expr`` (should not happen for a
        genuine :class:`RemovedCandidate` produced by :class:`.MultiHoudini`).
    """
    if removed.pre_relation is None:
        return CandidateValidation(
            status=CandidateReachability.NOT_APPLICABLE,
            checked_upto=0,
            witness_depth=None,
            elapsed_seconds=0.0,
            checks_performed=0,
        )
    if removed.candidate_expr is None:
        raise ValueError(
            f"RemovedCandidate for {removed.relation!r} (rule r{removed.rule_id}) "
            "has no candidate_expr to validate"
        )

    by_name = {str(rel.name()): rel for rel in variables}
    relation = by_name[removed.relation]
    canonical = variables[relation]

    return validate_candidate_reachability(
        program,
        relation,
        removed.candidate_expr,
        canonical,
        upto=upto,
        timeout_ms=timeout_ms,
        builder=builder,
    )


# ---------------------------------------------------------------------------
# Externally-checkable verification files for "potentially promising"
# candidates
# ---------------------------------------------------------------------------
#
# A NOT_FOUND verdict only means our own bounded, incremental search did not
# find a witness -- not that none exists. The functions below turn such a
# candidate into a standalone, independently checkable question: "is
# `candidate` actually an invariant of `relation` in the original program?".
# Every transition rule is carried over unchanged; only the safety property
# is replaced, using the same "interpreted safety head" shape this tool's
# own parser already accepts for the pure SMT-LIB HORN dialect (see the
# README's "Supported input formats" section):
#
#   (assert (forall (canonical vars) (=> (relation vars) candidate)))
#
# The result can be hand-fed to any HORN-capable solver, or re-run through
# this tool itself -- e.g. `chc-bounded-explorer --upto 200` for a much
# deeper bounded search than --candidate-bound would default to, or
# `--seed-houdini` for a fresh, independent inductive-invariant attempt.


def _relation_application(relation: z3.FuncDeclRef, args: tuple[z3.ExprRef, ...]) -> str:
    """SMT-LIB2 application text, matching this codebase's own convention of
    a bare identifier for nullary relations (see any example under
    examples/seed_houdini/, e.g. the nullary `fail` relation)."""
    name = str(relation.name())
    if not args:
        return name
    return "(" + name + " " + " ".join(arg.sexpr() for arg in args) + ")"


def _declare_fun(relation: z3.FuncDeclRef) -> str:
    domain = " ".join(relation.domain(i).sexpr() for i in range(relation.arity()))
    return f"(declare-fun {relation.name()} ({domain}) Bool)"


def _rule_to_assert(rule: HornRule) -> str:
    """Reconstruct one non-query HornRule as a standalone SMT-LIB2 assertion.

    Built directly from the rule's already-normalized fields (body,
    src/dst relation and args, rule_vars) rather than any original source
    text, so the result is independent of which of the two input dialects
    the source CHC file used, and is always in the single canonical shape
    this function produces.
    """
    antecedent_parts = []
    if rule.src_relation is not None:
        antecedent_parts.append(_relation_application(rule.src_relation, rule.src_args))
    body_sexpr = rule.body.sexpr()
    if body_sexpr != "true":
        antecedent_parts.append(body_sexpr)

    consequent = _relation_application(rule.dst_relation, rule.dst_args)
    if not antecedent_parts:
        clause = consequent
    else:
        antecedent = (
            antecedent_parts[0]
            if len(antecedent_parts) == 1
            else "(and " + " ".join(antecedent_parts) + ")"
        )
        clause = f"(=> {antecedent} {consequent})"

    if not rule.rule_vars:
        return f"(assert {clause})"
    binder = " ".join(f"({var} {var.sort().sexpr()})" for var in rule.rule_vars)
    return f"(assert (forall ({binder}) {clause}))"


def render_candidate_verification_smt2(
    program: HornProgram,
    variables: VariableMap,
    removed: RemovedCandidate,
    *,
    header: str | None = None,
) -> str:
    """Render a standalone CHC file checking whether *removed*'s candidate is
    actually an invariant of its relation, independent of this tool's own
    bounded candidate-reachability check.

    Every rule of *program* whose destination is not a query relation is
    carried over verbatim; every query relation and every rule that reaches
    one is dropped, since the new safety property replaces the original one
    entirely rather than supplementing it.

    Raises
    ------
    KeyError
        If *removed*'s relation name is not present in *variables* (should
        not happen for a genuine :class:`RemovedCandidate` produced by
        :class:`.MultiHoudini`, whose removed candidates are always keyed by
        one of its own tracked relations).
    """
    by_name = {str(rel.name()): rel for rel in variables}
    target = by_name[removed.relation]
    canonical = variables[target]

    kept_rules = [rule for rule in program.rules if not rule.is_query]
    used_relations: set[z3.FuncDeclRef] = {target}
    for rule in kept_rules:
        used_relations.add(rule.dst_relation)
        if rule.src_relation is not None:
            used_relations.add(rule.src_relation)

    # Z3's own SMT-LIB2 parser rejects String/RegLan sorts under an explicit
    # `(set-logic HORN)` tag (it is not one of the base sorts that logic
    # admits), which would make a dumped String candidate file fail to
    # reload in exactly the external solver this file is meant to hand off
    # to. Only emit the tag when it is safe to.
    def _mentions_string_theory(relation: z3.FuncDeclRef) -> bool:
        return any(
            "String" in relation.domain(i).sexpr()
            or "RegLan" in relation.domain(i).sexpr()
            for i in range(relation.arity())
        )

    needs_string_theory = any(_mentions_string_theory(rel) for rel in used_relations)

    lines: list[str] = []
    if header is not None:
        lines.extend(f"; {line}".rstrip() for line in header.splitlines())
        lines.append("")
    if not needs_string_theory:
        lines.append("(set-logic HORN)")
        lines.append("")
    for relation in sorted(used_relations, key=lambda rel: str(rel.name())):
        lines.append(_declare_fun(relation))
    lines.append("")
    for rule in kept_rules:
        lines.append(_rule_to_assert(rule))
    lines.append("")

    binder = " ".join(f"({var} {var.sort().sexpr()})" for var in canonical)
    target_application = _relation_application(target, canonical)
    property_clause = f"(=> {target_application} {removed.candidate})"
    property_assert = (
        f"(assert (forall ({binder}) {property_clause}))"
        if canonical
        else f"(assert {property_clause})"
    )
    lines.append(property_assert)
    lines.append("")
    lines.append("(check-sat)")
    return "\n".join(lines) + "\n"


def _candidate_verification_filename(removed: RemovedCandidate) -> str:
    """A stable, filesystem-safe, collision-resistant filename for *removed*.

    Deterministic (hashes rule_id + the candidate's own s-expression), so
    repeated `--dump-promising-candidates` runs on an unchanged program
    overwrite the same files rather than accumulating stale duplicates, and
    so the same candidate always maps to the same name across runs for easy
    caching or diffing.
    """
    safe_relation = re.sub(r"[^A-Za-z0-9_-]", "_", removed.relation) or "relation"
    digest_input = f"{removed.rule_id}:{removed.candidate}".encode()
    digest = hashlib.sha256(digest_input).hexdigest()[:10]
    return f"{safe_relation}__r{removed.rule_id}__{digest}.smt2"


def dump_promising_candidate_files(
    program: HornProgram,
    variables: VariableMap,
    removed_candidates: tuple[RemovedCandidate, ...],
    candidate_validations: tuple[CandidateValidation, ...],
    output_dir: Path,
) -> dict[int, Path]:
    """Write one external-verification file per NOT_FOUND-verdict removed
    candidate into *output_dir* (created, including parents, if missing).

    *removed_candidates* and *candidate_validations* must be the same length
    and in the same order (as produced by validating every entry of one
    :attr:`.HoudiniResult.removed_candidates` tuple). Candidates with any
    other verdict (REACHABLE, UNKNOWN, NOT_APPLICABLE) are skipped: only a
    NOT_FOUND verdict is the "potentially promising" case this is for.

    Returns ``{index: path}`` mapping each written file back to its position
    in *removed_candidates*, so callers can correlate a candidate with its
    generated file (e.g. to annotate JSON output) without depending on
    filename order. Use ``sorted(result.values())`` for a plain, deterministic
    list of the paths written.
    """
    output_dir.mkdir(parents=True, exist_ok=True)
    written: dict[int, Path] = {}
    for index, (removed, validation) in enumerate(
        zip(removed_candidates, candidate_validations, strict=True)
    ):
        if validation.status is not CandidateReachability.NOT_FOUND:
            continue
        header = (
            f"Externally-checkable verification task generated by "
            f"chc-bounded-explorer --dump-promising-candidates.\n"
            f"Original program: {program.source_path}\n"
            f"Candidate: {removed.candidate}\n"
            f"Originally proposed for relation: {removed.relation}\n"
            f"Removed by rule r{removed.rule_id} [{removed.rule}]\n"
            f"Not found reachable within {validation.checked_upto} step(s) "
            f"({validation.checks_performed} check(s) tried).\n"
            "This file reuses every transition rule from the original program "
            "verbatim, replacing the original safety property with a direct "
            "check of whether the candidate above holds for every reachable "
            "state of its relation."
        )
        text = render_candidate_verification_smt2(program, variables, removed, header=header)
        path = output_dir / _candidate_verification_filename(removed)
        path.write_text(text, encoding="utf-8")
        written[index] = path
    return written
