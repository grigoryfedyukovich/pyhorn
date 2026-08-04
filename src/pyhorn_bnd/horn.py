"""Intermediate representation and parser for linear constrained Horn clauses."""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Final

import z3
from z3.z3util import get_vars

from .normalize import (
    HornNormalizationError,
    collect_decls,
    contains_relation_app,
    expand_head,
    flatten_and,
    is_uninterpreted_bool_app,
    mk_and,
    open_outer_forall,
    split_horn_formula,
)
from .sexpr import SExprError, declared_relation_names

ENTRY: Final[None] = None


class HornParseError(ValueError):
    """Raised when an SMT-LIB file cannot be represented as linear CHCs."""


@dataclass(frozen=True)
class HornRule:
    """A normalized linear CHC, used by the bounded explorer."""

    rule_id: int
    original_rule_id: int
    body: z3.BoolRef
    rule_vars: tuple[z3.ExprRef, ...]
    src_relation: z3.FuncDeclRef | None
    src_args: tuple[z3.ExprRef, ...]
    dst_relation: z3.FuncDeclRef
    dst_args: tuple[z3.ExprRef, ...]
    is_fact: bool
    is_query: bool
    is_inductive: bool

    def short(self) -> str:
        src = "ENTRY" if self.src_relation is None else str(self.src_relation.name())
        return f"r{self.rule_id}: {src} -> {self.dst_relation.name()}"


@dataclass(frozen=True)
class ArithmeticSortProfile:
    """Numeric sorts occurring in relation signatures or CHC expressions.

    SMT-LIB ``Real`` is exact mathematical real arithmetic. Decimal literals
    are represented by Z3 as exact rationals, not IEEE floating-point values.
    """

    uses_integer: bool
    uses_real: bool

    @property
    def is_mixed(self) -> bool:
        return self.uses_integer and self.uses_real


@dataclass(frozen=True)
class HornProgram:
    """Normalized CHC database plus graph indices used by bounded exploration."""

    source_path: Path
    rules: tuple[HornRule, ...]
    relations: frozenset[z3.FuncDeclRef]
    query_relations: frozenset[z3.FuncDeclRef]
    outgoing: dict[z3.FuncDeclRef | None, tuple[HornRule, ...]]
    symbol_names: frozenset[str]
    arithmetic_sorts: ArithmeticSortProfile
    sliced: bool = False

    @property
    def has_cycles(self) -> bool:
        return self.maximum_acyclic_trace_length() is None

    def maximum_acyclic_trace_length(self) -> int | None:
        """Return the longest relevant ENTRY-to-query trace.

        ``None`` denotes a cycle on an ENTRY-to-query path. The implementation
        is iterative so CHC systems with thousands of relations do not hit
        Python's recursion limit.
        """

        reverse: dict[z3.FuncDeclRef, set[z3.FuncDeclRef | None]] = {}
        for rule in self.rules:
            reverse.setdefault(rule.dst_relation, set()).add(rule.src_relation)

        coreachable: set[z3.FuncDeclRef | None] = set(self.query_relations)
        work: list[z3.FuncDeclRef] = list(self.query_relations)
        while work:
            dst = work.pop()
            for src in reverse.get(dst, set()):
                if src in coreachable:
                    continue
                coreachable.add(src)
                if src is not None:
                    work.append(src)
        if ENTRY not in coreachable:
            return 0

        relevant_outgoing: dict[z3.FuncDeclRef | None, list[HornRule]] = {}
        for rule in self.rules:
            if (
                rule.src_relation in coreachable
                and rule.dst_relation in coreachable
                and rule.src_relation not in self.query_relations
            ):
                relevant_outgoing.setdefault(rule.src_relation, []).append(rule)

        reachable: set[z3.FuncDeclRef | None] = {ENTRY}
        work_nodes: list[z3.FuncDeclRef | None] = [ENTRY]
        while work_nodes:
            src = work_nodes.pop()
            for rule in relevant_outgoing.get(src, []):
                if rule.dst_relation not in reachable:
                    reachable.add(rule.dst_relation)
                    work_nodes.append(rule.dst_relation)

        nodes = reachable & coreachable
        indegree: dict[z3.FuncDeclRef | None, int] = {node: 0 for node in nodes}
        for src, rules in relevant_outgoing.items():
            if src not in nodes:
                continue
            for rule in rules:
                if rule.dst_relation in nodes:
                    indegree[rule.dst_relation] += 1

        queue = deque(node for node, degree in indegree.items() if degree == 0)
        distance: dict[z3.FuncDeclRef | None, int] = {ENTRY: 0}
        processed = 0
        while queue:
            src = queue.popleft()
            processed += 1
            for rule in relevant_outgoing.get(src, []):
                dst = rule.dst_relation
                if dst not in nodes:
                    continue
                if src in distance:
                    distance[dst] = max(distance.get(dst, -1), distance[src] + 1)
                indegree[dst] -= 1
                if indegree[dst] == 0:
                    queue.append(dst)

        if processed != len(nodes):
            return None
        return (
            max(
                (distance.get(query, -1) for query in self.query_relations),
                default=-1,
            )
            if any(distance.get(query, -1) >= 0 for query in self.query_relations)
            else 0
        )

    def slice_to_queries(self) -> "HornProgram":
        """Drop rules outside all ENTRY-to-query paths."""

        reachable: set[z3.FuncDeclRef | None] = {ENTRY}
        work: list[z3.FuncDeclRef | None] = [ENTRY]
        while work:
            src = work.pop()
            for rule in self.outgoing.get(src, ()):
                if rule.dst_relation not in reachable:
                    reachable.add(rule.dst_relation)
                    work.append(rule.dst_relation)

        reverse: dict[z3.FuncDeclRef, set[z3.FuncDeclRef | None]] = {}
        for rule in self.rules:
            reverse.setdefault(rule.dst_relation, set()).add(rule.src_relation)
        coreachable: set[z3.FuncDeclRef | None] = set(self.query_relations)
        work = list(self.query_relations)
        while work:
            dst = work.pop()
            for src in reverse.get(dst, set()):
                if src not in coreachable:
                    coreachable.add(src)
                    if src is not None:
                        work.append(src)

        kept = [
            rule
            for rule in self.rules
            if rule.src_relation in reachable and rule.dst_relation in coreachable
        ]
        return _build_program(
            self.source_path,
            [replace(rule, rule_id=i) for i, rule in enumerate(kept)],
            self.query_relations,
            sliced=True,
        )


def _relation_application(expr: z3.ExprRef, relations: set[z3.FuncDeclRef]) -> bool:
    return is_uninterpreted_bool_app(expr) and expr.decl() in relations


def _numeric_sort_kinds(sort: z3.SortRef) -> set[int]:
    kind = sort.kind()
    if kind in (z3.Z3_INT_SORT, z3.Z3_REAL_SORT):
        return {kind}
    if kind == z3.Z3_ARRAY_SORT:
        return _numeric_sort_kinds(sort.domain()) | _numeric_sort_kinds(sort.range())
    if kind == z3.Z3_SEQ_SORT:
        return _numeric_sort_kinds(sort.basis())
    return set()


def _expression_numeric_sort_kinds(expr: z3.ExprRef) -> set[int]:
    found: set[int] = set()
    stack: list[z3.ExprRef] = [expr]
    while stack and len(found) < 2:
        current = stack.pop()
        found.update(_numeric_sort_kinds(current.sort()))
        if z3.is_quantifier(current):
            for index in range(current.num_vars()):
                found.update(_numeric_sort_kinds(current.var_sort(index)))
            stack.append(current.body())
        elif z3.is_app(current):
            stack.extend(current.children())
    return found


def _arithmetic_sort_profile(
    relations: set[z3.FuncDeclRef], rules: list[HornRule]
) -> ArithmeticSortProfile:
    found: set[int] = set()
    for relation in relations:
        for index in range(relation.arity()):
            found.update(_numeric_sort_kinds(relation.domain(index)))
    if len(found) < 2:
        for rule in rules:
            for expression in (
                rule.body,
                *rule.src_args,
                *rule.dst_args,
                *rule.rule_vars,
            ):
                found.update(_expression_numeric_sort_kinds(expression))
                if len(found) == 2:
                    break
            if len(found) == 2:
                break
    return ArithmeticSortProfile(
        uses_integer=z3.Z3_INT_SORT in found,
        uses_real=z3.Z3_REAL_SORT in found,
    )

def _build_program(
    source_path: Path,
    rules: list[HornRule],
    query_relations: set[z3.FuncDeclRef] | frozenset[z3.FuncDeclRef],
    *,
    sliced: bool,
) -> HornProgram:
    outgoing_lists: dict[z3.FuncDeclRef | None, list[HornRule]] = {}
    relations: set[z3.FuncDeclRef] = set(query_relations)
    for rule in rules:
        outgoing_lists.setdefault(rule.src_relation, []).append(rule)
        if rule.src_relation is not None:
            relations.add(rule.src_relation)
        relations.add(rule.dst_relation)
    outgoing = {key: tuple(value) for key, value in outgoing_lists.items()}
    symbol_names = {str(relation.name()) for relation in relations}
    for rule in rules:
        symbol_names.update(str(variable.decl().name()) for variable in rule.rule_vars)
        for expression in (rule.body, *rule.src_args, *rule.dst_args):
            symbol_names.update(
                str(variable.decl().name()) for variable in get_vars(expression)
            )
    return HornProgram(
        source_path=source_path,
        rules=tuple(rules),
        relations=frozenset(relations),
        query_relations=frozenset(query_relations),
        outgoing=outgoing,
        symbol_names=frozenset(symbol_names),
        arithmetic_sorts=_arithmetic_sort_profile(relations, rules),
        sliced=sliced,
    )


def parse_chc_file(path: str | Path, *, slice_program: bool = True) -> HornProgram:
    """Parse and normalize a linear CHC file using Z3Py.

    Supported command dialects are Z3 fixedpoint syntax
    (``declare-rel``/``rule``/``query``) and pure SMT-LIB HORN syntax
    (Bool-valued ``declare-fun`` plus quantified ``assert`` commands).
    Integer and exact real arithmetic, including mixed ``Int``/``Real`` terms,
    are preserved as native Z3 expressions.
    """

    source_path = Path(path)
    try:
        text = source_path.read_text(encoding="utf-8")
    except OSError as exc:
        raise HornParseError(f"cannot read {source_path}: {exc}") from exc

    # Fixedpoint syntax declares relations with ``declare-rel``; pure SMT-LIB
    # HORN syntax uses Bool-valued ``declare-fun`` declarations.  Accept both,
    # including files that mix the command styles.
    try:
        relation_names = declared_relation_names(text)
    except SExprError as exc:
        raise HornParseError(f"invalid SMT-LIB command structure: {exc}") from exc
    if not relation_names:
        raise HornParseError("no CHC relation declarations found")

    fp = z3.Fixedpoint()
    try:
        parsed_queries = tuple(fp.parse_string(text))
        # Z3 stores ``rule`` commands in get_rules() and ordinary ``assert``
        # commands in get_assertions().  They are disjoint for the supported
        # inputs, so combining them makes both dialects first-class.
        z3_rules = tuple(fp.get_rules()) + tuple(fp.get_assertions())
    except z3.Z3Exception as exc:
        raise HornParseError(f"Z3 failed to parse {source_path}: {exc}") from exc

    relation_decls: set[z3.FuncDeclRef] = set()
    for expr in (*z3_rules, *parsed_queries):
        relation_decls.update(collect_decls(expr, relation_names))

    query_relations: set[z3.FuncDeclRef] = set()
    for query in parsed_queries:
        if not is_uninterpreted_bool_app(query) or query.decl() not in relation_decls:
            raise HornParseError(
                "only relation-application queries are supported; got " + query.sexpr()
            )
        if query.decl().arity() != 0:
            raise HornParseError(
                "only nullary query relations are supported; use a dedicated "
                "nullary fail/error relation"
            )
        query_relations.add(query.decl())
    # Interpreted/false assertion heads are redirected to a synthetic query
    # relation.  Pick a collision-free name in case an input uses our prefix.
    assertion_error_name = "__chc_bnd_assertion_error"
    suffix = 0
    while assertion_error_name in relation_names:
        suffix += 1
        assertion_error_name = f"__chc_bnd_assertion_error_{suffix}"
    assertion_error = z3.Function(assertion_error_name, z3.BoolSort())
    normalized: list[HornRule] = []

    for original_id, raw_rule in enumerate(z3_rules):
        opened, rule_vars = open_outer_forall(raw_rule, prefix=f"r{original_id}")
        if z3.is_quantifier(opened):
            raise HornParseError(
                f"rule {original_id}: outer existential quantification is unsupported"
            )
        body, head = split_horn_formula(opened, relation_decls)

        for branch_body, branch_head in expand_head(body, head):
            if z3.is_true(branch_head):
                continue

            if _relation_application(branch_head, relation_decls):
                dst_relation = branch_head.decl()
                dst_args = tuple(branch_head.children())
                effective_body = branch_body
            else:
                # A Horn assertion B -> P is violated exactly when B and not P
                # hold.  Convert that violation to an explicit error relation.
                dst_relation = assertion_error
                dst_args = ()
                effective_body = (
                    branch_body
                    if z3.is_false(branch_head)
                    else mk_and((branch_body, z3.Not(branch_head)))
                )
                query_relations.add(assertion_error)
                relation_decls.add(assertion_error)

            effective_body = z3.simplify(effective_body)
            conjuncts = flatten_and(effective_body)
            relation_atoms = [
                item
                for item in conjuncts
                if _relation_application(item, relation_decls)
            ]
            if len(relation_atoms) > 1:
                atoms = ", ".join(atom.sexpr() for atom in relation_atoms)
                raise HornNormalizationError(
                    f"rule {original_id} is nonlinear (multiple body relations): {atoms}"
                )
            source_atom = relation_atoms[0] if relation_atoms else None
            constraints = [item for item in conjuncts if item is not source_atom]
            src_relation = None if source_atom is None else source_atom.decl()
            src_args = () if source_atom is None else tuple(source_atom.children())
            rule_body = z3.simplify(mk_and(constraints))
            if contains_relation_app(rule_body, relation_decls):
                raise HornNormalizationError(
                    f"rule {original_id} contains a relation outside a positive "
                    "top-level body conjunction"
                )
            is_query = dst_relation in query_relations

            normalized.append(
                HornRule(
                    rule_id=len(normalized),
                    original_rule_id=original_id,
                    body=rule_body,
                    rule_vars=rule_vars,
                    src_relation=src_relation,
                    src_args=src_args,
                    dst_relation=dst_relation,
                    dst_args=dst_args,
                    is_fact=src_relation is None,
                    is_query=is_query,
                    is_inductive=(
                        src_relation is not None and src_relation == dst_relation
                    ),
                )
            )

    if not query_relations:
        # A small number of legacy CHC files omit the explicit ``query``
        # command but still encode an error rule whose head is a terminal
        # nullary relation (usually ``fail``).  Infer that target only when it
        # is unambiguous.  Requiring nullary arity and no use as a source keeps
        # the inference conservative: ordinary state predicates are never
        # silently reclassified as queries.
        source_relations = {
            rule.src_relation
            for rule in normalized
            if rule.src_relation is not None
        }
        terminal_nullary = {
            rule.dst_relation
            for rule in normalized
            if rule.dst_relation.arity() == 0
            and rule.dst_relation not in source_relations
        }
        if len(terminal_nullary) == 1:
            query_relations.update(terminal_nullary)
        elif not terminal_nullary:
            raise HornParseError(
                "the CHC file contains no query, false assertion, or "
                "terminal nullary error relation"
            )
        else:
            names = ", ".join(
                sorted(str(relation.name()) for relation in terminal_nullary)
            )
            raise HornParseError(
                "the CHC file omits an explicit query and has multiple "
                f"terminal nullary relations: {names}"
            )

    # Query membership may have grown while processing interpreted heads or
    # legacy terminal-nullary inference.
    normalized = [
        replace(rule, is_query=rule.dst_relation in query_relations)
        for rule in normalized
    ]
    program = _build_program(source_path, normalized, query_relations, sliced=False)
    return program.slice_to_queries() if slice_program else program
