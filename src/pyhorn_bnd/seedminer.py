"""Syntactic invariant-candidate mining from normalized CHC parse trees.

The implementation uses native Z3 expressions throughout. It walks Boolean
subtrees of every normalized clause, projects expressions onto canonical
variables for each predicate occurrence, and records predicate-local formulas.
"""

from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Iterable

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
    """Keep a seed and derive ordered bounds from numeric equalities.

    The original SeedMiner normalized arithmetic equality ``a = b`` into the
    conjunction ``a >= b`` and ``b >= a``.  Retaining those weaker conjuncts is
    essential for loops where equality is not inductive but one directional
    bound is.  The original equality is kept as well.
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
