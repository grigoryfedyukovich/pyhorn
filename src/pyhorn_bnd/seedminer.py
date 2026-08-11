"""Syntactic invariant-candidate mining from normalized CHC parse trees.

The implementation uses native Z3 expressions throughout. It walks Boolean
subtrees of every normalized clause, projects expressions onto canonical
variables for each predicate occurrence, and records predicate-local formulas.
"""

from __future__ import annotations

import re
from collections.abc import Iterable
from dataclasses import dataclass

import z3
from z3.z3util import get_vars

from .horn import HornProgram, HornRule

CandidateMap = dict[z3.FuncDeclRef, tuple[z3.BoolRef, ...]]
VariableMap = dict[z3.FuncDeclRef, tuple[z3.ExprRef, ...]]


@dataclass(frozen=True)
class SeedObservation:
    """One accepted predicate-local candidate and its syntactic origin."""

    rule_id: int
    relation: z3.FuncDeclRef
    role: str
    candidate: z3.BoolRef
    source: z3.BoolRef


@dataclass(frozen=True)
class SeedMiningStatistics:
    rules_examined: int
    boolean_nodes_seen: int
    projections_attempted: int
    projections_rejected: int
    duplicate_candidates: int
    candidates_mined: int


@dataclass(frozen=True)
class SeedMiningResult:
    """Canonical predicate variables and mined candidates."""

    variables: VariableMap
    candidates: CandidateMap
    observations: tuple[SeedObservation, ...]
    statistics: SeedMiningStatistics

    @property
    def predicate_count(self) -> int:
        return len(self.variables)

    @property
    def candidate_count(self) -> int:
        return sum(len(items) for items in self.candidates.values())


class SeedMiner:
    """Collect syntactic invariant candidates from every normalized CHC."""

    def __init__(self, program: HornProgram):
        self.program = program
        used_names = set(program.symbol_names)
        variables: dict[z3.FuncDeclRef, tuple[z3.ExprRef, ...]] = {}
        for relation in sorted(
            program.relations - program.query_relations,
            key=lambda item: str(item.name()),
        ):
            canonical, used_names = _canonical_variables(relation, used_names)
            variables[relation] = canonical
        self.variables = variables
        self._canonical_ids = {
            relation: frozenset(variable.get_id() for variable in canonical)
            for relation, canonical in variables.items()
        }
        self._reset_mining_state()

    def _reset_mining_state(self) -> None:
        self._candidates: dict[z3.FuncDeclRef, dict[str, z3.BoolRef]] = {
            relation: {} for relation in self.variables
        }
        self._observations: list[SeedObservation] = []
        self._free_variable_ids_cache: dict[
            int, tuple[z3.ExprRef, frozenset[int]]
        ] = {}
        self._boolean_nodes_seen = 0
        self._projections_attempted = 0
        self._projections_rejected = 0
        self._duplicate_candidates = 0

    def mine(self) -> SeedMiningResult:
        # ``mine`` is intentionally idempotent: repeated calls on the same
        # miner recompute the same observations and statistics from scratch.
        self._reset_mining_state()
        for rule in self.program.rules:
            self._mine_rule(rule)
        self._share_transparent_candidates()

        candidates: CandidateMap = {
            relation: tuple(
                expr for _, expr in sorted(items.items(), key=lambda entry: entry[0])
            )
            for relation, items in self._candidates.items()
        }
        statistics = SeedMiningStatistics(
            rules_examined=len(self.program.rules),
            boolean_nodes_seen=self._boolean_nodes_seen,
            projections_attempted=self._projections_attempted,
            projections_rejected=self._projections_rejected,
            duplicate_candidates=self._duplicate_candidates,
            candidates_mined=sum(len(items) for items in candidates.values()),
        )
        return SeedMiningResult(
            variables=self.variables,
            candidates=candidates,
            observations=tuple(self._observations),
            statistics=statistics,
        )

    generator_id = "seedminer"

    def generate(self):
        """Return candidates through the neutral generator extension API.

        Lets :class:`SeedMiner` be used anywhere a
        :class:`.candidate_generation.CandidateGenerator` is expected (e.g.
        merged with other proposal engines via
        :func:`.candidate_generation.merge_candidate_batches`) without a
        direct import cycle between this module and
        :mod:`.candidate_generation`.
        """

        from .candidate_generation import CandidateBatch

        result = self.mine()
        return CandidateBatch(
            generator_id=self.generator_id,
            variables=result.variables,
            candidates=result.candidates,
            metadata={
                "rules_examined": result.statistics.rules_examined,
                "boolean_nodes_seen": result.statistics.boolean_nodes_seen,
            },
        )

    def _share_transparent_candidates(self) -> None:
        """Propagate candidate syntax across pure predicate-renaming rules.

        Multi-predicate benchmarks often contain phase changes such as
        ``P(x, y) -> Q(x, y)`` with no additional constraint.  A candidate
        observed for one phase is a useful candidate for the other phase, but
        the ordinary per-occurrence miner cannot invent it there.  Candidate
        sharing is sound because MultiHoudini still proves or removes every
        copied formula.
        """

        changed = True
        while changed:
            changed = False
            for rule in self.program.rules:
                if (
                    rule.is_query
                    or rule.src_relation is None
                    or rule.src_relation not in self.variables
                    or rule.dst_relation not in self.variables
                    or not z3.is_true(z3.simplify(rule.body))
                ):
                    continue
                mapping = _transparent_position_mapping(rule)
                if mapping is None:
                    continue

                src_relation = rule.src_relation
                dst_relation = rule.dst_relation
                src_variables = self.variables[src_relation]
                dst_variables = self.variables[dst_relation]
                src_to_dst = tuple(
                    (src_variables[src_index], dst_variables[dst_index])
                    for src_index, dst_index in enumerate(mapping)
                )
                dst_to_src = tuple(
                    (dst_variables[dst_index], src_variables[src_index])
                    for src_index, dst_index in enumerate(mapping)
                )

                before_dst = len(self._candidates[dst_relation])
                for candidate in tuple(self._candidates[src_relation].values()):
                    self._add_candidate(
                        rule,
                        dst_relation,
                        _substitute(candidate, src_to_dst),
                        source=candidate,
                        role="transfer:source-to-destination",
                    )
                changed |= len(self._candidates[dst_relation]) != before_dst

                before_src = len(self._candidates[src_relation])
                for candidate in tuple(self._candidates[dst_relation].values()):
                    self._add_candidate(
                        rule,
                        src_relation,
                        _substitute(candidate, dst_to_src),
                        source=candidate,
                        role="transfer:destination-to-source",
                    )
                changed |= len(self._candidates[src_relation]) != before_src

    def _mine_rule(self, rule: HornRule) -> None:
        occurrences: list[tuple[str, z3.FuncDeclRef, tuple[z3.ExprRef, ...]]] = []
        if rule.src_relation is not None and rule.src_relation in self.variables:
            occurrences.append(("source", rule.src_relation, rule.src_args))
        if not rule.is_query and rule.dst_relation in self.variables:
            occurrences.append(("destination", rule.dst_relation, rule.dst_args))

        for role, relation, args in occurrences:
            self._mine_argument_shape(rule, role, relation, args)

        body_roots: list[tuple[str, z3.BoolRef]] = [("body", rule.body)]
        avoidance: z3.BoolRef | None = None
        if rule.is_query:
            # The negated non-recursive query part is often useful, but it is
            # insufficient when the source relation is applied to repeated or
            # non-trivial arguments.  Mine both the simple projection and the
            # negation of the complete bad-state pattern.
            body_roots.append(("query-negation", z3.simplify(z3.Not(rule.body))))
            if rule.src_relation is not None and rule.src_relation in self.variables:
                avoidance = self._query_avoidance_candidate(rule)

        for origin, root in body_roots:
            for node in _boolean_seed_nodes(root):
                self._boolean_nodes_seen += 1
                for role, relation, args in occurrences:
                    self._project_and_add(
                        rule,
                        relation,
                        args,
                        node,
                        role=f"{role}:{origin}",
                    )

        # Add the complete query pattern after ordinary query-negation seeds so
        # existing observation provenance remains stable when both formulas
        # simplify to the same candidate.
        if avoidance is not None and rule.src_relation is not None:
            self._add_candidate(
                rule,
                rule.src_relation,
                avoidance,
                source=rule.body,
                role="source:query-avoidance",
            )

    def _query_avoidance_candidate(
        self, rule: HornRule
    ) -> z3.BoolRef | None:
        """Project the complete query bad-state pattern to canonical variables.

        For a query such as ``inv(y, y) and y >= k -> fail``, separately mining
        ``v0 == v1`` and ``v0 < k`` loses the useful disjunction
        ``v0 != v1 or v0 < k``.  This helper preserves the relation-argument
        shape and negates the complete projected bad state.
        """

        relation = rule.src_relation
        if relation is None or relation not in self.variables:
            return None
        canonical = self.variables[relation]
        substitutions = _direct_argument_substitutions(rule.src_args, canonical)
        projected_body = z3.simplify(_substitute(rule.body, substitutions))
        shape = _relation_argument_shape(
            rule.src_args,
            canonical,
            substitutions,
        )
        bad_state = z3.simplify(z3.And(projected_body, *shape))

        # Rule-local variables in a query describe existential witnesses for a
        # bad state.  Negating the query therefore universally closes those
        # witnesses.  This recovers the quantified array properties used by
        # the original benchmarks, e.g.
        # ``forall j. 0 < j < i -> a[j] == b[j]``.
        canonical_ids = self._canonical_ids[relation]
        locals_to_close = sorted(
            (
                variable
                for variable in get_vars(bad_state)
                if variable.get_id() not in canonical_ids
            ),
            key=lambda variable: (
                str(variable.decl().name()),
                variable.sort().sexpr(),
                variable.get_id(),
            ),
        )
        avoidance = z3.Not(bad_state)
        if locals_to_close:
            avoidance = z3.ForAll(locals_to_close, avoidance)
        return z3.simplify(avoidance)

    def _mine_argument_shape(
        self,
        rule: HornRule,
        role: str,
        relation: z3.FuncDeclRef,
        args: tuple[z3.ExprRef, ...],
    ) -> None:
        canonical = self.variables[relation]
        substitutions = _direct_argument_substitutions(args, canonical)
        for index, (variable, argument) in enumerate(zip(canonical, args, strict=True)):
            projected_argument = _substitute(argument, substitutions)
            equality = z3.simplify(variable == projected_argument)
            self._add_candidate(
                rule,
                relation,
                equality,
                source=equality,
                role=f"{role}:argument-{index}",
            )

    def _project_and_add(
        self,
        rule: HornRule,
        relation: z3.FuncDeclRef,
        args: tuple[z3.ExprRef, ...],
        expression: z3.BoolRef,
        *,
        role: str,
    ) -> None:
        self._projections_attempted += 1
        canonical = self.variables[relation]
        substitutions = _direct_argument_substitutions(args, canonical)
        projected = z3.simplify(_substitute(expression, substitutions))
        if not self._is_predicate_local(projected, relation):
            self._projections_rejected += 1
            return
        self._add_candidate(
            rule,
            relation,
            projected,
            source=expression,
            role=role,
        )

    def _add_candidate(
        self,
        rule: HornRule,
        relation: z3.FuncDeclRef,
        candidate: z3.ExprRef,
        *,
        source: z3.BoolRef,
        role: str,
    ) -> None:
        for variant_role, variant in _candidate_variants(candidate):
            normalized = z3.simplify(variant)
            if (
                not z3.is_bool(normalized)
                or z3.is_true(normalized)
                or z3.is_false(normalized)
            ):
                continue
            if not self._is_predicate_local(normalized, relation):
                continue
            key = normalized.sexpr()
            bucket = self._candidates[relation]
            if key in bucket:
                self._duplicate_candidates += 1
                continue
            bucket[key] = normalized
            self._observations.append(
                SeedObservation(
                    rule_id=rule.rule_id,
                    relation=relation,
                    role=role + variant_role,
                    candidate=normalized,
                    source=source,
                )
            )

    def _is_predicate_local(
        self,
        expression: z3.ExprRef,
        relation: z3.FuncDeclRef,
    ) -> bool:
        expression_id = expression.get_id()
        cached = self._free_variable_ids_cache.get(expression_id)
        if cached is None or not cached[0].eq(expression):
            free_ids = frozenset(variable.get_id() for variable in get_vars(expression))
            self._free_variable_ids_cache[expression_id] = (expression, free_ids)
        else:
            free_ids = cached[1]
        return free_ids <= self._canonical_ids[relation]


def _canonical_variables(
    relation: z3.FuncDeclRef, used_names: set[str]
) -> tuple[tuple[z3.ExprRef, ...], set[str]]:
    """Allocate collision-free variables without mutating ``used_names``."""

    allocated_names = set(used_names)
    relation_name = re.sub(r"[^A-Za-z0-9_]", "_", str(relation.name()))
    result: list[z3.ExprRef] = []
    for index in range(relation.arity()):
        base = f"__{relation_name}_{index}"
        name = base
        suffix = 0
        while name in allocated_names:
            suffix += 1
            name = f"{base}_{suffix}"
        allocated_names.add(name)
        result.append(z3.Const(name, relation.domain(index)))
    return tuple(result), allocated_names


def _is_free_uninterpreted_constant(expression: z3.ExprRef) -> bool:
    return (
        z3.is_const(expression)
        and expression.decl().kind() == z3.Z3_OP_UNINTERPRETED
    )


def _direct_argument_substitutions(
    arguments: tuple[z3.ExprRef, ...],
    canonical: tuple[z3.ExprRef, ...],
) -> tuple[tuple[z3.ExprRef, z3.ExprRef], ...]:
    """Map direct relation arguments to canonical predicate variables.

    Repeated arguments map to the first canonical position.  The argument-shape
    miner then records equalities between subsequent positions.
    """

    result: list[tuple[z3.ExprRef, z3.ExprRef]] = []
    seen_ids: set[int] = set()
    for argument, variable in zip(arguments, canonical, strict=True):
        if not _is_free_uninterpreted_constant(argument):
            continue
        argument_id = argument.get_id()
        if argument_id in seen_ids:
            continue
        seen_ids.add(argument_id)
        result.append((argument, variable))
    return tuple(result)


def _transparent_position_mapping(
    rule: HornRule,
) -> tuple[int, ...] | None:
    """Map each source position to a destination position for a pure renaming."""

    if len(rule.src_args) != len(rule.dst_args):
        return None
    if not all(_is_free_uninterpreted_constant(arg) for arg in rule.src_args):
        return None
    if not all(_is_free_uninterpreted_constant(arg) for arg in rule.dst_args):
        return None

    destination_by_id: dict[int, int] = {}
    for index, argument in enumerate(rule.dst_args):
        argument_id = argument.get_id()
        if argument_id in destination_by_id:
            return None
        destination_by_id[argument_id] = index

    mapping: list[int] = []
    seen_destinations: set[int] = set()
    for argument in rule.src_args:
        destination = destination_by_id.get(argument.get_id())
        if destination is None or destination in seen_destinations:
            return None
        seen_destinations.add(destination)
        mapping.append(destination)
    return tuple(mapping)


def _relation_argument_shape(
    arguments: tuple[z3.ExprRef, ...],
    canonical: tuple[z3.ExprRef, ...],
    substitutions: tuple[tuple[z3.ExprRef, z3.ExprRef], ...],
) -> tuple[z3.BoolRef, ...]:
    """Return canonical equalities imposed by one relation application."""

    first_position = {source.get_id(): target for source, target in substitutions}
    shape: list[z3.BoolRef] = []
    seen_direct: set[int] = set()
    for argument, variable in zip(arguments, canonical, strict=True):
        if _is_free_uninterpreted_constant(argument):
            argument_id = argument.get_id()
            target = first_position[argument_id]
            if argument_id in seen_direct:
                shape.append(z3.simplify(variable == target))
            else:
                seen_direct.add(argument_id)
            continue
        projected = z3.simplify(_substitute(argument, substitutions))
        shape.append(z3.simplify(variable == projected))
    return tuple(shape)


def _candidate_variants(
    candidate: z3.ExprRef,
) -> tuple[tuple[str, z3.ExprRef], ...]:
    """Keep a seed and derive ordered bounds from numeric equalities, plus a
    regex-complement push for String.

    The original SeedMiner normalized arithmetic equality ``a = b`` into the
    conjunction ``a >= b`` and ``b >= a``.  Retaining those weaker conjuncts is
    essential for loops where equality is not inductive but one directional
    bound is.  The original equality is kept as well, since the two forms can
    genuinely differ in inductive strength.

    ``Not(x in Complement(R))``, by contrast, is *replaced* by its
    logically-equivalent but syntactically simpler push, ``x in R``, rather
    than kept alongside it: the two forms carry identical logical content, so
    there is nothing to gain from the original, and (see the inline comment
    below) real harm in keeping it -- Z3's own regex-complement reasoning can
    be too expensive to certify even when the same fact in its pushed form
    is cheap.
    """

    normalized = z3.simplify(candidate)
    variants: list[tuple[str, z3.ExprRef]] = [("", normalized)]
    if z3.is_eq(normalized) and normalized.num_args() == 2:
        lhs, rhs = normalized.children()
        if z3.is_arith(lhs) and z3.is_arith(rhs):
            variants.extend(
                (
                    (":numeric-ge", lhs >= rhs),
                    (":numeric-le", rhs >= lhs),
                )
            )
    elif z3.is_not(normalized) and z3.is_eq(normalized.arg(0)):
        equality = normalized.arg(0)
        lhs, rhs = equality.children()
        if z3.is_arith(lhs) and z3.is_arith(rhs):
            variants.append((":numeric-disequality", z3.Or(lhs > rhs, rhs > lhs)))
    elif (
        z3.is_not(normalized)
        and z3.is_app(normalized.arg(0))
        and normalized.arg(0).decl().kind() == z3.Z3_OP_SEQ_IN_RE
    ):
        # `Not(x in Complement(R))` is logically `x in R`, but that push is a
        # regex-algebra rewrite, not a propositional one, and z3.simplify()
        # does not apply it by default. Unlike the numeric-equality variants
        # above, this is not a different logical strength worth keeping
        # alongside the original -- it is the exact same semantic content in
        # a syntactically simpler form, and the un-pushed form is strictly
        # worse: even when both survive MultiHoudini's per-candidate
        # induction check on their own, the mere presence of the
        # complement-laden term in the retained set is enough to make final
        # certification's solver call time out (observed directly: it
        # degrades to `canceled` rather than `unsat`/`sat`), producing
        # `unknown` overall despite a clean, cheap equivalent being right
        # there. So this replaces the un-pushed form rather than
        # supplementing it.
        membership = normalized.arg(0)
        subject, pattern = membership.arg(0), membership.arg(1)
        if z3.is_app(pattern) and pattern.decl().kind() == z3.Z3_OP_RE_COMPLEMENT:
            pushed = membership.decl()(subject, pattern.arg(0))
            variants = [(":regex-complement-pushed", pushed)]
    elif z3.is_distinct(normalized) and normalized.num_args() == 2:
        lhs, rhs = normalized.children()
        if z3.is_arith(lhs) and z3.is_arith(rhs):
            variants.append((":numeric-disequality", z3.Or(lhs > rhs, rhs > lhs)))

    deduplicated: dict[str, tuple[str, z3.ExprRef]] = {}
    for suffix, expression in variants:
        simplified = z3.simplify(expression)
        deduplicated.setdefault(simplified.sexpr(), (suffix, simplified))
    return tuple(deduplicated.values())


def _substitute(
    expression: z3.ExprRef,
    substitutions: tuple[tuple[z3.ExprRef, z3.ExprRef], ...],
) -> z3.ExprRef:
    if not substitutions:
        return expression
    return z3.substitute(expression, *substitutions)


def _boolean_seed_nodes(expression: z3.BoolRef) -> Iterable[z3.BoolRef]:
    """Yield useful Boolean subtrees in deterministic preorder.

    Conjunctions are split into independent seeds.  Disjunctions and negations
    are retained as complete candidates and are not recursively exploded,
    matching the original SeedMiner behavior and avoiding exponential
    candidate growth on large clauses.  Boolean ITE conditions are observed in
    addition to the complete ITE expression.
    """

    stack: list[z3.ExprRef] = [expression]
    seen: set[str] = set()
    while stack:
        current = stack.pop()
        if not z3.is_bool(current):
            continue
        if z3.is_true(current) or z3.is_false(current):
            continue

        if z3.is_and(current):
            stack.extend(reversed(current.children()))
            continue

        normalized = z3.simplify(current)
        if not z3.is_true(normalized) and not z3.is_false(normalized):
            key = normalized.sexpr()
            if key not in seen:
                seen.add(key)
                yield normalized

        if z3.is_quantifier(current) or z3.is_or(current) or z3.is_not(current):
            continue
        if z3.is_implies(current):
            continue
        if z3.is_app(current) and current.decl().kind() == z3.Z3_OP_ITE:
            condition = current.arg(0)
            if z3.is_bool(condition):
                stack.append(condition)


# ---------------------------------------------------------------------------
# --mut: candidate mutation
#
# Ported from and extends FreqHorn's RndLearnerV3.hpp::mutateHeuristicEq,
# which combines pairs of already-known numeric equalities via +/- (e.g.
# x=a and y=b together also give x+y=a+b and x-y=a-b) to enrich the
# candidate pool beyond what direct syntactic mining alone produces. This
# adds the inequality analog the original didn't have: chaining pairs of
# <=/</>=/> facts by transitivity (x<=y and y<=z give x<=z).
#
# Deliberately not ported: the original's constant-multiple substitution
# pass (turning x=5 and y=10 into y=2*x because 10 is a multiple of 5) is a
# narrower, more speculative heuristic that wasn't part of what was asked
# for here; left for a future extension if it turns out to be needed.
# ---------------------------------------------------------------------------

# Pairing cost in mutate_candidates() is quadratic in the number of terms
# per relation. Syntactically-mined and --cands pools are small enough that
# this was never an issue in practice, so mutate_candidates() itself stays
# unbounded by default. run_trace_houdini()'s combined seed-plus-trace pools
# can be an order of magnitude larger, so it applies this cap by default;
# see mutate_candidates()'s max_terms_per_relation parameter.
DEFAULT_MAX_MUTATION_TERMS_PER_RELATION = 32

# Sort-agnostic equality substitution is linear in |candidates| × |equalities|
# (each equality is applied as a rewrite to every other candidate, both
# orientations). Still needs a bound for large trace-sampled pools.
DEFAULT_MAX_EQUALITY_SUBSTITUTIONS_PER_RELATION = 256


@dataclass(frozen=True)
class MutationStatistics:
    """Counts from one :func:`mutate_candidates` call."""

    equalities_considered: int
    inequalities_considered: int
    equality_pairs_combined: int
    inequality_chains_combined: int
    candidates_added: int
    # Terms dropped by max_terms_per_relation before pairing, if that cap
    # was set and a relation's pool exceeded it. Zero whenever the cap was
    # not set or never triggered. Reported separately from
    # equalities_considered/inequalities_considered (which already reflect
    # the post-cap counts) purely so callers can tell a small candidate
    # pool apart from a large one that got truncated.
    terms_dropped_by_cap: int = 0
    # Sort-agnostic equality substitution (any sort, not just arithmetic).
    general_equalities_considered: int = 0
    substitution_rewrites_attempted: int = 0
    substitution_candidates_added: int = 0
    substitutions_dropped_by_cap: int = 0
    # Explicit string-theory bridge rules (linear, not quadratic).
    string_bridges_emitted: int = 0


@dataclass(frozen=True)
class MutationResult:
    """New candidates derived by :func:`mutate_candidates`.

    ``candidates`` holds only what was newly derived, keyed the same way as
    :data:`.CandidateMap` -- callers merge it into an existing pool with
    :func:`.merge_candidate_maps`, the same as any other candidate source
    (seed-mined or ``--cands``-supplied).
    """

    candidates: CandidateMap
    statistics: MutationStatistics


def mutate_candidates(
    candidates: CandidateMap,
    *,
    max_terms_per_relation: int | None = None,
    max_equality_substitutions_per_relation: int | None = DEFAULT_MAX_EQUALITY_SUBSTITUTIONS_PER_RELATION,
) -> MutationResult:
    """Derive additional candidates from *candidates* by combining pairs of
    existing numeric equalities and inequalities, and by sort-agnostic
    equality substitution, one relation at a time.

    Works the same regardless of where *candidates* came from -- a
    :class:`.SeedMiner` result, a ``--cands`` file parsed by
    :func:`.parse_candidate_file`, or a map already merged from both via
    :func:`.merge_candidate_maps` -- since it only looks at the candidate
    expressions themselves, never at how they were produced.

    Equalities (ported): given ``L1 = R1`` and ``L2 = R2`` already in the
    pool, both ``(L1+L2) = (R1+R2)`` and ``(L1-L2) = (R1-R2)`` hold, and so
    do the same after swapping the second equality's sides (since
    ``L2 = R2`` iff ``R2 = L2``): ``(L1+R2) = (R1+L2)`` and
    ``(L1-R2) = (R1-L2)``. Four derived candidates per unordered pair,
    exactly as in the original. Restricted to arithmetic terms.

    Inequalities (new): given ``L1 <=/< R1`` and ``L2 <=/< R2`` (``>=``/``>``
    are normalized to this form first: ``A >= B`` becomes ``B <= A``), if
    ``R1`` is syntactically the same term as ``L2``, the chain
    ``L1 <=/< R2`` holds -- strict if either input was strict. This is the
    "``x <= y`` and ``y <= z`` implies ``x <= z``" case, and its strict
    variants (``x < y`` and ``y <= z`` implies ``x < z``, etc.). Both
    directions of every unordered pair are tried, since chaining is not
    symmetric the way the equality combination is: only within-relation
    combinations are formed, and nothing here reasons across two different
    predicates' candidate sets.

    Sort-agnostic equality substitution (new): given any equality ``a = b``
    (any sort: Int, Real, String, Array, Bool, BitVec, …) already in the
    pool, every other candidate ``c`` is rewritten by substituting ``b`` for
    ``a`` and ``a`` for ``b``. The resulting formulas are valid under the
    invariant ``a = b``, so the rewrite is sound for free. This subsumes
    many per-theory “bridge” rules (e.g. length facts under string equality,
    select facts under array equality) as special cases. Cost is linear in
    |candidates| × |equalities|; *max_equality_substitutions_per_relation*
    bounds the number of rewrite attempts per relation (default
    :data:`DEFAULT_MAX_EQUALITY_SUBSTITUTIONS_PER_RELATION`). Pass ``None``
    to disable the bound.

    Explicit string bridges (new, linear): cheap, sound consequences that
    connect the String world to Int length templates without pairing:

    - ``s1 = s2`` → ``str.len(s1) = str.len(s2)``
    - ``str.prefixof(lit, s)`` / ``str.suffixof(lit, s)`` with a concrete
      string literal → ``str.len(s) >= len(lit)``
    - ``s_t = str.++(s_l, s_r)`` → ``str.len(s_t) = str.len(s_l) + str.len(s_r)``

    The concatenation bridge is especially useful together with equality
    substitution: when a concat equality and a numeric length fact on one
    operand both survive, substitution + this bridge connect the numeric
    side to concrete integer templates.

    Results that :func:`z3.simplify` collapses to ``True`` or ``False`` are
    dropped (matching the original's ``!u.isFalse(a) && !u.isTrue(a)``
    filter), as are results that duplicate a candidate already present.

    *max_terms_per_relation*, if set, caps how many equalities and how many
    inequalities (independently) are drawn from each relation's pool before
    pairing. Pairing cost is quadratic in the number of terms, so this
    exists for candidate pools too large for unbounded pairing to finish in
    reasonable time -- e.g. the trace-sampled pools ``--trace-houdini --mut``
    combines, which routinely carry an order of magnitude more equalities
    than the syntactically-mined pools this function was originally sized
    for. ``None`` (the default) preserves the original unbounded behavior,
    since plain ``--seed-houdini``/``--cands`` pools are not normally large
    enough to need it. When the cap truncates a relation's terms, the first
    *max_terms_per_relation* as encountered are kept and the rest are
    dropped, not resampled or prioritized by any heuristic.
    """

    derived_by_relation: dict[z3.FuncDeclRef, tuple[z3.BoolRef, ...]] = {}
    equalities_considered = 0
    inequalities_considered = 0
    equality_pairs_combined = 0
    inequality_chains_combined = 0
    terms_dropped_by_cap = 0
    general_equalities_considered = 0
    substitution_rewrites_attempted = 0
    substitution_candidates_added = 0
    substitutions_dropped_by_cap = 0
    string_bridges_emitted = 0

    for relation, relation_candidates in candidates.items():
        equalities: list[tuple[z3.ExprRef, z3.ExprRef]] = []
        inequalities: list[tuple[z3.ExprRef, z3.ExprRef, bool]] = []
        general_equalities: list[tuple[z3.ExprRef, z3.ExprRef]] = []

        for candidate in relation_candidates:
            numeric_eq = _as_numeric_equality(candidate)
            if numeric_eq is not None:
                equalities.append(numeric_eq)
                # Numeric equalities are also general equalities.
                general_equalities.append(numeric_eq)
                continue
            general_eq = _as_any_equality(candidate)
            if general_eq is not None:
                general_equalities.append(general_eq)
                continue
            inequality = _as_numeric_inequality(candidate)
            if inequality is not None:
                inequalities.append(inequality)

        if max_terms_per_relation is not None:
            if len(equalities) > max_terms_per_relation:
                terms_dropped_by_cap += len(equalities) - max_terms_per_relation
                equalities = equalities[:max_terms_per_relation]
            if len(inequalities) > max_terms_per_relation:
                terms_dropped_by_cap += len(inequalities) - max_terms_per_relation
                inequalities = inequalities[:max_terms_per_relation]

        equalities_considered += len(equalities)
        inequalities_considered += len(inequalities)
        general_equalities_considered += len(general_equalities)

        eq_derived, eq_pairs = _mutate_equalities(equalities)
        ineq_derived, ineq_chains = _mutate_inequalities(inequalities)
        equality_pairs_combined += eq_pairs
        inequality_chains_combined += ineq_chains

        # String bridges first so equality substitution can rewrite them
        # under existing equalities (e.g. len(st)=len(sl)+len(sr) under
        # len(sl)=3 → len(st)=3+len(sr)).
        string_derived = _mutate_string_bridges(relation_candidates)
        string_bridges_emitted += len(string_derived)

        sub_pool: list[z3.BoolRef] = list(relation_candidates) + list(string_derived)
        sub_derived, sub_attempted, sub_dropped = _mutate_equality_substitutions(
            sub_pool,
            general_equalities,
            max_rewrites=max_equality_substitutions_per_relation,
        )
        substitution_rewrites_attempted += sub_attempted
        substitutions_dropped_by_cap += sub_dropped

        existing = {c.sexpr() for c in relation_candidates}
        kept: dict[str, z3.BoolRef] = {}
        for candidate in (*eq_derived, *ineq_derived, *sub_derived, *string_derived):
            simplified = z3.simplify(candidate)
            if z3.is_true(simplified) or z3.is_false(simplified):
                continue
            key = simplified.sexpr()
            if key in existing or key in kept:
                continue
            kept[key] = simplified

        sub_added = sum(
            1
            for c in sub_derived
            if not z3.is_true(z3.simplify(c))
            and not z3.is_false(z3.simplify(c))
            and z3.simplify(c).sexpr() in kept
        )
        substitution_candidates_added += sub_added

        if kept:
            derived_by_relation[relation] = tuple(kept.values())

    statistics = MutationStatistics(
        equalities_considered=equalities_considered,
        inequalities_considered=inequalities_considered,
        equality_pairs_combined=equality_pairs_combined,
        inequality_chains_combined=inequality_chains_combined,
        candidates_added=sum(len(v) for v in derived_by_relation.values()),
        terms_dropped_by_cap=terms_dropped_by_cap,
        general_equalities_considered=general_equalities_considered,
        substitution_rewrites_attempted=substitution_rewrites_attempted,
        substitution_candidates_added=substitution_candidates_added,
        substitutions_dropped_by_cap=substitutions_dropped_by_cap,
        string_bridges_emitted=string_bridges_emitted,
    )
    return MutationResult(candidates=derived_by_relation, statistics=statistics)


def _as_numeric_equality(
    candidate: z3.BoolRef,
) -> tuple[z3.ExprRef, z3.ExprRef] | None:
    """Return ``(lhs, rhs)`` if *candidate* is ``lhs == rhs`` over
    arithmetic terms, else ``None``."""

    if not (z3.is_eq(candidate) and candidate.num_args() == 2):
        return None
    lhs, rhs = candidate.arg(0), candidate.arg(1)
    if z3.is_arith(lhs) and z3.is_arith(rhs):
        return (lhs, rhs)
    return None


def _as_any_equality(
    candidate: z3.BoolRef,
) -> tuple[z3.ExprRef, z3.ExprRef] | None:
    """Return ``(lhs, rhs)`` if *candidate* is ``lhs == rhs`` of any sort,
    else ``None``. Used by sort-agnostic equality substitution."""

    if not (z3.is_eq(candidate) and candidate.num_args() == 2):
        return None
    return (candidate.arg(0), candidate.arg(1))


def _mutate_equality_substitutions(
    relation_candidates: tuple[z3.BoolRef, ...] | list[z3.BoolRef],
    equalities: list[tuple[z3.ExprRef, z3.ExprRef]],
    *,
    max_rewrites: int | None,
) -> tuple[list[z3.BoolRef], int, int]:
    """Rewrite other candidates by substituting under any equality ``a = b``.

    For every equality ``(a, b)`` and every candidate ``c`` that is not that
    equality itself, emit ``c[b/a]`` and ``c[a/b]``. Sound because any model
    of the invariant set that satisfies ``a = b`` also satisfies the
    rewritten formula. Linear in |candidates| × |equalities|; *max_rewrites*
    caps the number of rewrite attempts (both orientations count) and any
    excess is reported as dropped.

    Returns ``(derived, attempted, dropped_by_cap)``.
    """

    derived: list[z3.BoolRef] = []
    attempted = 0
    dropped = 0
    if not equalities or not relation_candidates:
        return derived, attempted, dropped

    for lhs, rhs in equalities:
        # Skip trivial a = a.
        if lhs.eq(rhs):
            continue
        # Sexr of this particular equality so we skip rewriting it by itself
        # (only produces tautologies / the same fact). Other equalities are
        # still rewritten under this one.
        this_eq_sexpr = z3.simplify(lhs == rhs).sexpr()
        for candidate in relation_candidates:
            if candidate.sexpr() == this_eq_sexpr:
                continue
            for src, dst in ((lhs, rhs), (rhs, lhs)):
                if max_rewrites is not None and attempted >= max_rewrites:
                    dropped += 1
                    continue
                attempted += 1
                rewritten = z3.substitute(candidate, (src, dst))
                if rewritten.eq(candidate):
                    # No occurrence of src; skip.
                    continue
                derived.append(rewritten)

    return derived, attempted, dropped


def _mutate_string_bridges(
    relation_candidates: tuple[z3.BoolRef, ...] | list[z3.BoolRef],
) -> list[z3.BoolRef]:
    """Emit explicit String → Int length bridges (linear, sound, no pairing).

    Bridges:

    - ``s1 = s2`` (both String) → ``str.len(s1) = str.len(s2)``
    - ``str.prefixof(lit, s)`` / ``str.suffixof(lit, s)`` with a concrete
      string literal → ``str.len(s) >= len(lit)``
    - ``s_t = str.++(s_l, s_r)`` (or multi-arg concat) →
      ``str.len(s_t) = str.len(s_l) + str.len(s_r) + …``
    """

    derived: list[z3.BoolRef] = []

    for candidate in relation_candidates:
        # --- String equality → equal lengths ---
        if z3.is_eq(candidate) and candidate.num_args() == 2:
            lhs, rhs = candidate.arg(0), candidate.arg(1)
            if _is_string_sort(lhs) and _is_string_sort(rhs):
                derived.append(z3.Length(lhs) == z3.Length(rhs))

            # --- Concat equality → length additivity ---
            # s_t = str.++(s_l, s_r, ...)  or  str.++(...) = s_t
            for total, parts_expr in ((lhs, rhs), (rhs, lhs)):
                parts = _as_string_concat_parts(parts_expr)
                if parts is not None and _is_string_sort(total) and len(parts) >= 2:
                    length_sum = z3.Length(parts[0])
                    for part in parts[1:]:
                        length_sum = length_sum + z3.Length(part)
                    derived.append(z3.Length(total) == length_sum)

        if not z3.is_app(candidate):
            continue
        kind = candidate.decl().kind()

        # --- prefixof / suffixof with concrete literal → length lower bound ---
        if kind in (z3.Z3_OP_SEQ_PREFIX, z3.Z3_OP_SEQ_SUFFIX) and candidate.num_args() == 2:
            # SMT-LIB: (str.prefixof s t) means s is a prefix of t.
            # Z3 PrefixOf(prefix, string) same argument order.
            prefix_or_suffix, subject = candidate.arg(0), candidate.arg(1)
            lit_len = _concrete_string_length(prefix_or_suffix)
            if lit_len is not None and _is_string_sort(subject):
                derived.append(z3.Length(subject) >= lit_len)

    return derived


def _is_string_sort(expr: z3.ExprRef) -> bool:
    """True if *expr* has Z3's Unicode string/sequence sort."""
    try:
        if hasattr(z3, "is_string") and z3.is_string(expr):
            return True
        return bool(expr.sort().is_string())
    except Exception:
        return False


def _as_string_concat_parts(
    expr: z3.ExprRef,
) -> list[z3.ExprRef] | None:
    """If *expr* is ``str.++(a, b, ...)`` (possibly nested), return the flat
    list of string parts; else ``None``."""
    if not z3.is_app(expr):
        return None
    if expr.decl().kind() != z3.Z3_OP_SEQ_CONCAT:
        return None
    parts: list[z3.ExprRef] = []
    stack = list(reversed(expr.children()))
    while stack:
        current = stack.pop()
        if z3.is_app(current) and current.decl().kind() == z3.Z3_OP_SEQ_CONCAT:
            stack.extend(reversed(current.children()))
        else:
            parts.append(current)
    return parts if len(parts) >= 2 else None


def _concrete_string_length(expr: z3.ExprRef) -> int | None:
    """Return the character length if *expr* is a concrete string literal,
    else ``None``."""
    if not z3.is_string_value(expr):
        return None
    # z3.StringVal / is_string_value: .as_string() gives the Python str.
    try:
        return len(expr.as_string())
    except Exception:
        return None


# strict=False for <=/>=, strict=True for </>; >=/> are the "flipped" forms
# (A >= B normalizes to B <= A) so they carry the same two booleans.
_INEQUALITY_KINDS = {z3.Z3_OP_LE: False, z3.Z3_OP_LT: True}
_FLIPPED_INEQUALITY_KINDS = {z3.Z3_OP_GE: False, z3.Z3_OP_GT: True}


def _as_numeric_inequality(
    candidate: z3.BoolRef,
) -> tuple[z3.ExprRef, z3.ExprRef, bool] | None:
    """Return ``(lhs, rhs, strict)`` such that *candidate* is equivalent to
    ``lhs <= rhs`` (``strict=False``) or ``lhs < rhs`` (``strict=True``),
    normalizing ``>=``/``>`` to that form (``A >= B`` becomes ``B <= A``),
    else ``None``."""

    if not z3.is_app(candidate):
        return None
    kind = candidate.decl().kind()
    if kind not in _INEQUALITY_KINDS and kind not in _FLIPPED_INEQUALITY_KINDS:
        return None
    if candidate.num_args() != 2:
        return None
    lhs, rhs = candidate.arg(0), candidate.arg(1)
    if not (z3.is_arith(lhs) and z3.is_arith(rhs)):
        return None
    if kind in _INEQUALITY_KINDS:
        return (lhs, rhs, _INEQUALITY_KINDS[kind])
    return (rhs, lhs, _FLIPPED_INEQUALITY_KINDS[kind])


def _mutate_equalities(
    equalities: list[tuple[z3.ExprRef, z3.ExprRef]],
) -> tuple[list[z3.BoolRef], int]:
    """Port of ``mutateHeuristicEq``'s equality-combination step: for every
    unordered pair, four candidates via +/- across the two pairings (direct
    and swapped)."""

    derived: list[z3.BoolRef] = []
    pairs_combined = 0
    n = len(equalities)
    for i in range(n):
        l1, r1 = equalities[i]
        for j in range(i + 1, n):
            l2, r2 = equalities[j]
            pairs_combined += 1
            for l2p, r2p in ((l2, r2), (r2, l2)):
                derived.append((l1 + l2p) == (r1 + r2p))
                derived.append((l1 - l2p) == (r1 - r2p))
    return derived, pairs_combined


def _mutate_inequalities(
    inequalities: list[tuple[z3.ExprRef, z3.ExprRef, bool]],
) -> tuple[list[z3.BoolRef], int]:
    """New: chain pairs of normalized inequalities. If ``p``'s rhs is
    syntactically ``q``'s lhs, ``p.lhs <=/< q.rhs`` holds (strict if either
    input was) -- e.g. ``x<=y`` and ``y<=z`` give ``x<=z``; ``x<y`` and
    ``y<=z`` give ``x<z``. Every ordered pair is tried (not just ``i<j``,
    unlike the equality case above): chaining reads left-to-right, so which
    one supplies the "rhs to match" and which the "lhs to match" matters."""

    derived: list[z3.BoolRef] = []
    chains_combined = 0
    n = len(inequalities)
    for i in range(n):
        l1, r1, s1 = inequalities[i]
        for j in range(n):
            if i == j:
                continue
            l2, r2, s2 = inequalities[j]
            if not r1.eq(l2):
                continue
            chains_combined += 1
            strict = s1 or s2
            derived.append(l1 < r2 if strict else l1 <= r2)
    return derived, chains_combined
