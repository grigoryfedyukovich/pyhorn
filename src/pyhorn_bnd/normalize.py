"""Z3-expression normalization helpers for linear constrained Horn clauses."""

from __future__ import annotations

from collections.abc import Iterable, Iterator

import z3


class HornNormalizationError(ValueError):
    """Raised when a rule is outside the supported linear-CHC fragment."""


def is_uninterpreted_bool_app(expr: z3.ExprRef) -> bool:
    return (
        z3.is_app(expr)
        and expr.sort().kind() == z3.Z3_BOOL_SORT
        and expr.decl().kind() == z3.Z3_OP_UNINTERPRETED
    )


def flatten_and(expr: z3.BoolRef) -> list[z3.BoolRef]:
    result: list[z3.BoolRef] = []
    stack: list[z3.BoolRef] = [expr]
    while stack:
        current = stack.pop()
        if z3.is_and(current):
            stack.extend(reversed(current.children()))
        elif z3.is_true(current):
            continue
        else:
            result.append(current)
    return result


def flatten_or(expr: z3.BoolRef) -> list[z3.BoolRef]:
    result: list[z3.BoolRef] = []
    stack: list[z3.BoolRef] = [expr]
    while stack:
        current = stack.pop()
        if z3.is_or(current):
            stack.extend(reversed(current.children()))
        elif z3.is_false(current):
            continue
        else:
            result.append(current)
    return result


def mk_and(parts: Iterable[z3.BoolRef]) -> z3.BoolRef:
    items = list(parts)
    if not items:
        return z3.BoolVal(True)
    if len(items) == 1:
        return items[0]
    return z3.And(*items)


def open_outer_forall(
    expr: z3.ExprRef, *, prefix: str
) -> tuple[z3.ExprRef, tuple[z3.ExprRef, ...]]:
    """Open CHC rule binders using named Z3 constants.

    Leading universal binders become rule-local symbols. A top-level
    ``not (exists ...)`` is opened as well, matching the normalization in
    the normalized Horn representation. Inner quantifiers are retained as theory
    constraints in the generated verification condition.
    """

    all_vars: list[z3.ExprRef] = []
    current = expr
    layer = 0

    def open_quantifier(quantifier: z3.QuantifierRef) -> z3.ExprRef:
        nonlocal layer
        names = [quantifier.var_name(i) for i in range(quantifier.num_vars())]
        sorts = [quantifier.var_sort(i) for i in range(quantifier.num_vars())]
        fresh = tuple(
            z3.Const(f"__pyhorn_{prefix}_{layer}_{i}_{names[i]}", sorts[i])
            for i in range(len(names))
        )
        layer += 1
        all_vars.extend(fresh)
        # De Bruijn variable 0 is the last syntactic binder.
        return z3.substitute_vars(quantifier.body(), *reversed(fresh))

    while z3.is_quantifier(current) and current.is_forall():
        current = open_quantifier(current)

    if (
        z3.is_not(current)
        and z3.is_quantifier(current.arg(0))
        and current.arg(0).is_exists()
    ):
        current = z3.Not(open_quantifier(current.arg(0)))

    return current, tuple(all_vars)


def split_implication(expr: z3.BoolRef) -> tuple[z3.BoolRef, z3.BoolRef]:
    if z3.is_implies(expr):
        return expr.arg(0), expr.arg(1)
    if z3.is_not(expr):
        return expr.arg(0), z3.BoolVal(False)
    return z3.BoolVal(True), expr


def split_horn_formula(
    expr: z3.BoolRef, relations: set[z3.FuncDeclRef]
) -> tuple[z3.BoolRef, z3.BoolRef]:
    """Convert implication, negation, or clausal OR syntax to body/head form."""

    if z3.is_implies(expr) or z3.is_not(expr):
        return split_implication(expr)
    if z3.is_or(expr):
        disjuncts = flatten_or(expr)
        positive_heads = [
            item
            for item in disjuncts
            if is_uninterpreted_bool_app(item) and item.decl() in relations
        ]
        if len(positive_heads) > 1:
            heads = ", ".join(item.sexpr() for item in positive_heads)
            raise HornNormalizationError(
                f"formula has multiple positive relation heads: {heads}"
            )
        head = positive_heads[0] if positive_heads else z3.BoolVal(False)
        body = mk_and(z3.Not(item) for item in disjuncts if item is not head)
        return z3.simplify(body), head
    return z3.BoolVal(True), expr


def expand_head(
    body: z3.BoolRef, head: z3.BoolRef
) -> Iterator[tuple[z3.BoolRef, z3.BoolRef]]:
    """Flatten nested implication/ITE heads into ordinary Horn-rule branches."""

    if z3.is_implies(head):
        yield from expand_head(mk_and((body, head.arg(0))), head.arg(1))
        return
    if z3.is_app_of(head, z3.Z3_OP_ITE):
        cond, then_head, else_head = head.children()
        yield from expand_head(mk_and((body, cond)), then_head)
        yield from expand_head(mk_and((body, z3.Not(cond))), else_head)
        return
    yield body, head


def collect_decls(expr: z3.ExprRef, relation_names: set[str]) -> set[z3.FuncDeclRef]:
    """Collect relation declarations by matching source-level declare-rel names."""

    found: set[z3.FuncDeclRef] = set()
    stack: list[z3.ExprRef] = [expr]
    while stack:
        current = stack.pop()
        if z3.is_quantifier(current):
            stack.append(current.body())
            continue
        if not z3.is_app(current):
            continue
        if (
            is_uninterpreted_bool_app(current)
            and str(current.decl().name()) in relation_names
        ):
            found.add(current.decl())
        stack.extend(current.children())
    return found


def contains_relation_app(expr: z3.ExprRef, relations: set[z3.FuncDeclRef]) -> bool:
    stack: list[z3.ExprRef] = [expr]
    while stack:
        current = stack.pop()
        if z3.is_quantifier(current):
            stack.append(current.body())
            continue
        if not z3.is_app(current):
            continue
        if is_uninterpreted_bool_app(current) and current.decl() in relations:
            return True
        stack.extend(current.children())
    return False


def substitute_many(
    expr: z3.ExprRef, pairs: Iterable[tuple[z3.ExprRef, z3.ExprRef]]
) -> z3.ExprRef:
    substitutions = list(pairs)
    if not substitutions:
        return expr
    return z3.substitute(expr, *substitutions)
