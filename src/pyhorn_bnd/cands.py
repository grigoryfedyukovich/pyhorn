"""Parse user-supplied ``define-fun`` candidate files for Houdini filtering.

A candidate file is a plain SMT-LIB2 file containing one or more
``define-fun`` commands -- at most one group per uninterpreted, non-query
predicate of the target CHC system. Each function maps the predicate's
formal parameters to a Boolean formula (the proposed invariant)::

    (define-fun inv ((x Int) (n Int)) Bool
      (and (>= x 0) (<= x n)))

Multiple ``define-fun`` commands for the same predicate are supported; their
bodies are merged. Any other top-level SMT-LIB2 command (``declare-fun``,
``set-logic``, ``declare-datatypes``, comments, ...) is silently ignored, so
the same file may carry declarations purely for human readability.

Processing steps for each ``define-fun``:

1. **Structure check** -- validate the five-field shape (name, parameter
   list, return sort, body) and require a ``Bool`` return sort.
2. **Arity check** -- the number of declared parameters must equal the
   arity of the matching predicate's canonical variable tuple, as allocated
   by :class:`.SeedMiner`.
3. **Z3 interpretation with direct variable binding** -- the body text is
   parsed by :func:`z3.parse_smt2_string`, binding each declared parameter
   *name* directly to the predicate's canonical Z3 variable via the parser's
   ``decls`` symbol table rather than declaring fresh constants and
   substituting afterwards. Binding is *positional*: the *i*-th declared
   parameter is bound to ``variables[relation][i]`` regardless of what the
   file calls it. This sidesteps an entire class of bugs that would
   otherwise arise from reconstructing parameter sorts as text (arrays of
   user sorts, datatypes, and other non-builtin sorts all "just work" because
   the real :class:`z3.SortRef` object is reused, never re-parsed from a
   name).
4. **Conjunct splitting** -- the body is simplified and then flattened by
   :func:`.flatten_and`. Trivially-true / trivially-false conjuncts are
   discarded; duplicates (compared by s-expression string) are merged.

The result is a :data:`.CandidateMap` that can be passed directly to
:meth:`.MultiHoudini.run`, optionally after merging with mined candidates
via :func:`merge_candidate_maps`.

Known limitations (documented rather than silently mishandled):

- A ``define-fun`` body may not reference helper functions or constants
  declared elsewhere in the same candidate file; only the predicate's own
  parameters (and ordinary SMT-LIB2 operators/literals) are in scope.
- ``define-fun`` commands whose name does not match any predicate in
  ``variables`` (typically because the predicate is a query relation, or the
  name is misspelled) are silently skipped, matching SMT-LIB2's own
  tolerance of extraneous declarations.

Public API
----------
:func:`parse_candidate_file`
    Parse a candidate file and return a :data:`.CandidateMap`.
:func:`merge_candidate_maps`
    Merge two :data:`.CandidateMap` objects, deduplicating by s-expression.
    Useful when ``--cands`` is combined with ``--seed-houdini``.
:func:`format_candidates_smt2`
    The inverse of :func:`parse_candidate_file`: render a :data:`.CandidateMap`
    as SMT-LIB2 ``define-fun`` text that :func:`parse_candidate_file` can read
    back. Used by ``--dump-cands`` to make mined (``--seed-houdini``)
    invariants reusable as ``--cands`` input -- note this is *not* the same
    text that ``--print-invariants`` shows, which is Python's infix
    ``str()`` form and is not valid SMT-LIB2.
"""

from __future__ import annotations

import re
from pathlib import Path

import z3

from .horn import HornParseError
from .normalize import flatten_and
from .seedminer import CandidateMap, VariableMap
from .sexpr import SExprError, parse_commands, unquote_symbol

# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

# SMT-LIB2 "simple symbol" character class (Section 3.1 of the SMT-LIB2
# standard): letters, digits, and a fixed set of punctuation, not starting
# with a digit. Anything else must be written as a |quoted symbol| instead.
_SIMPLE_SYMBOL_RE = re.compile(
    r"^[A-Za-z~!@$%^&*_+=<>.?/][A-Za-z0-9~!@$%^&*_+=<>.?/-]*$"
)


def _format_symbol(name: str) -> str:
    """Render *name* as a valid SMT-LIB2 symbol, quoting it if necessary."""
    if _SIMPLE_SYMBOL_RE.match(name):
        return name
    # SMT-LIB2 quoted symbols have no in-quote escape for '|' or '\'; both
    # are rare in practice for CHC predicate names, so they are substituted
    # rather than left to produce invalid output.
    safe = name.replace("|", "_").replace("\\", "_")
    return f"|{safe}|"


def _node_to_str(node: object) -> str:
    """Reconstruct an SMT-LIB2 token or parenthesised sub-expression.

    :mod:`.sexpr` ``parse_commands`` represents atoms as :class:`str` and
    parenthesised groups as nested :class:`list` objects (e.g. the sort
    ``(Array Int Int)`` becomes ``['Array', 'Int', 'Int']``).
    """
    if isinstance(node, str):
        return node
    return "(" + " ".join(_node_to_str(child) for child in node) + ")"


def _unpack_param_names(raw_params: object, predicate_name: str) -> list[str]:
    """Validate the ``define-fun`` parameter list and return its names in order.

    Each element of *raw_params* must be a two-element list ``[name, sort]``;
    the sort field is checked only for well-formedness here -- it is never
    used to redeclare a constant, because callers bind parameters directly to
    the predicate's real canonical variables (see the module docstring).

    :raises HornParseError: if the list structure is malformed, a parameter
        name is not a plain symbol, or two parameters share a name.
    """
    if not isinstance(raw_params, list):
        raise HornParseError(
            f"define-fun '{predicate_name}': parameter list is not a list "
            f"(got {raw_params!r})"
        )
    names: list[str] = []
    seen: set[str] = set()
    for entry in raw_params:
        if not isinstance(entry, list) or len(entry) != 2:
            raise HornParseError(
                f"define-fun '{predicate_name}': malformed parameter entry "
                f"'{_node_to_str(entry)}'; expected (name sort)"
            )
        pname, psort = entry
        if not isinstance(pname, str):
            raise HornParseError(
                f"define-fun '{predicate_name}': parameter name is not a "
                f"symbol (got {pname!r})"
            )
        if not isinstance(psort, (str, list)):
            raise HornParseError(
                f"define-fun '{predicate_name}': malformed sort for "
                f"parameter '{pname}'"
            )
        if pname in seen:
            raise HornParseError(
                f"define-fun '{predicate_name}': duplicate parameter name "
                f"'{pname}'"
            )
        seen.add(pname)
        names.append(pname)
    return names


def _parse_body(
    predicate_name: str,
    body_str: str,
    decls: dict[str, z3.ExprRef],
) -> z3.BoolRef:
    """Parse *body_str* as a single Bool-sorted assertion.

    *decls* binds each in-scope parameter name directly to its canonical Z3
    constant, so the parsed expression is already expressed in terms of the
    predicate's canonical variables -- no post-hoc substitution is needed.
    Any identifier in *body_str* that is not a parameter name and not a
    built-in SMT-LIB2 symbol causes Z3 to reject the snippet with an "unknown
    constant/function" error, which is reported as a :class:`HornParseError`.

    :raises HornParseError: if Z3 rejects the snippet, or the result is not
        exactly one Bool-sorted assertion.
    """
    try:
        parsed = z3.parse_smt2_string(f"(assert {body_str})", decls=decls)
    except z3.Z3Exception as exc:
        raise HornParseError(
            f"define-fun '{predicate_name}': Z3 rejected body "
            f"'{body_str[:120]}': {exc}"
        ) from exc

    if len(parsed) != 1:
        raise HornParseError(
            f"define-fun '{predicate_name}': body produced {len(parsed)} "
            "Z3 assertions; expected exactly 1"
        )
    expr = parsed[0]
    if not z3.is_bool(expr):
        raise HornParseError(
            f"define-fun '{predicate_name}': body does not have Bool sort "
            f"(got {expr.sort()})"
        )
    return expr  # type: ignore[return-value]


def _accumulate_conjuncts(
    body: z3.BoolRef,
    bucket: dict[str, z3.BoolRef],
) -> None:
    """Split *body* into top-level conjuncts and insert unique ones into *bucket*.

    *body* is simplified first so that a conjunction revealed only after
    simplification (e.g. a tautological ``ite`` branch) is still split,
    matching the convention used when normalizing ordinary CHC rule bodies.
    Trivially-true and trivially-false conjuncts are dropped. Deduplication
    is by s-expression string, so multiple ``define-fun``s for the same
    predicate merge cleanly.
    """
    simplified_body: z3.BoolRef = z3.simplify(body)  # type: ignore[assignment]
    for conjunct in flatten_and(simplified_body):
        simplified: z3.BoolRef = z3.simplify(conjunct)  # type: ignore[assignment]
        if z3.is_true(simplified) or z3.is_false(simplified):
            continue
        if not z3.is_bool(simplified):
            continue
        bucket.setdefault(simplified.sexpr(), simplified)


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def parse_candidate_file(
    path: str | Path,
    variables: VariableMap,
) -> CandidateMap:
    """Parse *path* and return a :data:`.CandidateMap` keyed by
    :class:`z3.FuncDeclRef`.

    Only relations present in *variables* are processed; ``define-fun``
    commands for unknown predicates are silently skipped.

    Parameters
    ----------
    path:
        Path to an SMT-LIB2 file containing ``define-fun`` commands.
    variables:
        Canonical variable map produced by :class:`.SeedMiner` -- a
        ``dict[z3.FuncDeclRef, tuple[z3.ExprRef, ...]]``. Used both to filter
        relevant predicates and to supply the canonical Z3 variables that
        every parameter is bound to.

    Returns
    -------
    CandidateMap
        ``dict[z3.FuncDeclRef, tuple[z3.BoolRef, ...]]``. Each value tuple
        holds the deduplicated conjuncts harvested from all ``define-fun``
        commands for that relation, already expressed over the relation's
        canonical variables. Predicates whose every conjunct was trivial (or
        that had no matching ``define-fun``) are omitted from the result.

    Raises
    ------
    FileNotFoundError
        If *path* does not exist.
    HornParseError
        On any structural or Z3-level parse failure inside a ``define-fun``,
        or if the file is not well-formed SMT-LIB2 s-expression syntax.
    """
    path = Path(path)
    if not path.exists():
        raise FileNotFoundError(f"candidate file not found: {path}")

    source = path.read_text(encoding="utf-8")

    # Build a str -> FuncDeclRef reverse index once. VariableMap is keyed by
    # FuncDeclRef; SMT-LIB2 command names are plain strings. Without this
    # index every 'name in variables' check would compare a str against
    # FuncDeclRef keys and never match, silently dropping every define-fun
    # regardless of content.
    by_name: dict[str, z3.FuncDeclRef] = {str(rel.name()): rel for rel in variables}

    # buckets[predicate_name] = {sexpr_str: z3_expr} -- dedup within one predicate
    buckets: dict[str, dict[str, z3.BoolRef]] = {}

    try:
        commands = parse_commands(source)
    except SExprError as exc:
        # Match parse_chc_file's convention (see horn.py): callers of this
        # module only need to catch HornParseError/OSError to handle every
        # candidate-file failure uniformly.
        raise HornParseError(f"{path}: invalid SMT-LIB command structure: {exc}") from exc

    for cmd in commands:
        # A define-fun command is: ['define-fun', name, params, return_sort, body]
        if not isinstance(cmd, list) or len(cmd) != 5:
            continue
        head, name, raw_params, raw_ret, raw_body = cmd
        if head != "define-fun":
            continue
        if not isinstance(name, str):
            continue
        name = unquote_symbol(name)

        # Skip predicates not present in the variable map (typically query
        # relations, or a typo'd/stale predicate name).
        if name not in by_name:
            continue

        ret_sort = _node_to_str(raw_ret)
        if ret_sort != "Bool":
            raise HornParseError(
                f"define-fun '{name}': return sort must be Bool (got '{ret_sort}')"
            )

        relation = by_name[name]
        canonical = variables[relation]

        param_names = _unpack_param_names(raw_params, name)
        if len(param_names) != len(canonical):
            raise HornParseError(
                f"define-fun '{name}': declares {len(param_names)} "
                f"parameter(s) but the relation has {len(canonical)} "
                "canonical variable(s) -- check that the candidate file "
                "matches the CHC system."
            )

        decls: dict[str, z3.ExprRef] = dict(zip(param_names, canonical))
        body_str = _node_to_str(raw_body)
        body = _parse_body(name, body_str, decls)

        bucket = buckets.setdefault(name, {})
        _accumulate_conjuncts(body, bucket)

    return {
        by_name[name]: tuple(bucket.values())
        for name, bucket in buckets.items()
        if bucket  # omit predicates whose every conjunct was trivial
    }


def merge_candidate_maps(
    base: CandidateMap,
    extra: CandidateMap,
) -> CandidateMap:
    """Return a new :data:`.CandidateMap` that is the union of *base* and *extra*.

    For each relation, conjuncts from *extra* that are not already present in
    *base* (compared by s-expression string) are appended after the base
    conjuncts. Neither *base* nor *extra* is mutated.

    This is the intended entry point when ``--cands`` is combined with
    ``--seed-houdini``: mined candidates form the *base* and user-supplied
    candidates are the *extra* (or vice versa -- the result is the same set
    either way, modulo ordering).

    Parameters
    ----------
    base:
        Primary candidate map (e.g. from :class:`.SeedMiner`).
    extra:
        Secondary candidate map (e.g. from :func:`parse_candidate_file`).

    Returns
    -------
    CandidateMap
        Merged ``dict[z3.FuncDeclRef, tuple[z3.BoolRef, ...]]`` containing
        all relations from both inputs, with duplicate conjuncts removed.
    """
    accumulator: dict[z3.FuncDeclRef, list[z3.BoolRef]] = {
        rel: list(cands) for rel, cands in base.items()
    }

    for rel, extra_cands in extra.items():
        if rel not in accumulator:
            accumulator[rel] = list(extra_cands)
            continue
        existing_sexprs: set[str] = {c.sexpr() for c in accumulator[rel]}
        for cand in extra_cands:
            if cand.sexpr() not in existing_sexprs:
                accumulator[rel].append(cand)
                existing_sexprs.add(cand.sexpr())

    return {rel: tuple(cands) for rel, cands in accumulator.items()}


def format_candidates_smt2(
    candidates: CandidateMap,
    variables: VariableMap,
    *,
    header: str | None = None,
) -> str:
    """Render *candidates* as SMT-LIB2 text that :func:`parse_candidate_file`
    can read back -- the serialization counterpart of that function.

    One ``define-fun`` is emitted per relation that has at least one
    retained conjunct; a relation with zero conjuncts is omitted rather than
    written as an explicit ``true`` body, since :func:`parse_candidate_file`
    (via :meth:`.MultiHoudini.run`) already treats an absent predicate
    identically to one whose invariant is ``true``. Multiple conjuncts for a
    relation are joined with ``and``. Parameters are named after the
    relation's own canonical variables purely for readability -- binding on
    the read side is positional, so the exact names never matter.

    This is deliberately *not* what ``--print-invariants`` prints: that is
    Python's infix ``str()`` form (e.g. ``__inv_0 <= 10``), which is not
    valid SMT-LIB2 syntax and cannot be parsed back by
    :func:`parse_candidate_file`. This function instead uses each
    expression's ``.sexpr()`` form.

    Parameters
    ----------
    candidates:
        Typically :attr:`.HoudiniResult.candidates` after a
        ``--seed-houdini`` (or ``--cands``) run, but any :data:`.CandidateMap`
        works, including a hand-built one.
    variables:
        The canonical variable map the relations in *candidates* were
        expressed over (e.g. :attr:`.SeedMiner.variables`). Every relation
        key in *candidates* must also be a key here.
    header:
        Optional free-form text prefixed as ``;``-commented lines, e.g. to
        record provenance (source file, Houdini status, timestamp).

    Returns
    -------
    str
        SMT-LIB2 source text, terminated with a trailing newline. Empty
        (or comment-only, if *header* is given) when every relation in
        *candidates* has zero conjuncts.

    Raises
    ------
    KeyError
        If a relation in *candidates* is not present in *variables*.
    """
    header_block: list[str] = []
    if header is not None:
        header_lines = header.splitlines() or [""]
        header_block = [f"; {line}".rstrip() for line in header_lines]

    define_lines: list[str] = []
    for relation in sorted(candidates.keys(), key=lambda rel: str(rel.name())):
        conjuncts = candidates[relation]
        if not conjuncts:
            continue
        canonical = variables[relation]
        params = " ".join(f"({var} {var.sort().sexpr()})" for var in canonical)
        if len(conjuncts) == 1:
            body = conjuncts[0].sexpr()
        else:
            body = "(and " + " ".join(c.sexpr() for c in conjuncts) + ")"
        name = _format_symbol(str(relation.name()))
        define_lines.append(f"(define-fun {name} ({params}) Bool {body})")

    if not header_block and not define_lines:
        return ""
    separator = [""] if header_block and define_lines else []
    return "\n".join(header_block + separator + define_lines) + "\n"
