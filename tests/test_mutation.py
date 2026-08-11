"""Tests for :func:`pyhorn_bnd.seedminer.mutate_candidates` -- the ``--mut``
heuristic ported and extended from FreqHorn's
``RndLearnerV3.hpp::mutateHeuristicEq``.

Every expected output here is derived by hand from the function's own
documented algorithm (pairwise +/- combination for equalities, transitive
chaining for inequalities), not by running the tool and observing what
comes out -- this is pure symbolic AST construction, fully checkable
without a live solver. Z3 expression equality is checked via ``.sexpr()``
strings throughout, matching ``tests/test_cands.py``'s convention, because
Python's ``==`` on symbolic Z3 expressions builds a new ``z3.BoolRef``
rather than comparing structurally.
"""

from __future__ import annotations

import z3

from pyhorn_bnd.seedminer import CandidateMap, mutate_candidates


def _rel(name: str, *sorts: z3.SortRef) -> z3.FuncDeclRef:
    return z3.Function(name, *sorts, z3.BoolSort())


def _sexprs(candidates: tuple[z3.BoolRef, ...]) -> set[str]:
    return {c.sexpr() for c in candidates}


# ---------------------------------------------------------------------------
# Equalities (ported from mutateHeuristicEq)
# ---------------------------------------------------------------------------


def test_equality_pair_produces_four_combinations() -> None:
    """x=a and y=b together give (x+y)=(a+b), (x-y)=(a-b), and the same
    with the second equality's sides swapped: (x+b)=(a+y), (x-b)=(a-y)."""
    x, y, a, b = z3.Ints("x y a b")
    rel = _rel("inv", z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {rel: (x == a, y == b)}

    result = mutate_candidates(candidates)
    got = _sexprs(result.candidates[rel])

    expected = {
        z3.simplify((x + y) == (a + b)).sexpr(),
        z3.simplify((x - y) == (a - b)).sexpr(),
        z3.simplify((x + b) == (a + y)).sexpr(),
        z3.simplify((x - b) == (a - y)).sexpr(),
    }
    assert expected <= got
    assert result.statistics.equality_pairs_combined == 1
    assert result.statistics.equalities_considered == 2


def test_three_equalities_combine_pairwise_not_all_at_once() -> None:
    """Three equalities give C(3,2)=3 pairs, not one three-way combination
    -- matching the original, which only ever combines two at a time."""
    x, y, w, a, b, c = z3.Ints("x y w a b c")
    rel = _rel("inv", z3.IntSort(), z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {rel: (x == a, y == b, w == c)}

    result = mutate_candidates(candidates)

    assert result.statistics.equality_pairs_combined == 3
    # 4 derived per pair, 3 pairs = 12 (before any collapse to duplicates)
    assert result.statistics.candidates_added <= 12


# ---------------------------------------------------------------------------
# Inequalities (new: transitivity)
# ---------------------------------------------------------------------------


def test_le_transitivity_x_le_y_and_y_le_z_gives_x_le_z() -> None:
    """The example from the request this feature was built for."""
    x, y, z = z3.Ints("x y z")
    rel = _rel("inv", z3.IntSort(), z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {rel: (x <= y, y <= z)}

    result = mutate_candidates(candidates)
    got = _sexprs(result.candidates[rel])

    assert z3.simplify(x <= z).sexpr() in got
    assert result.statistics.inequality_chains_combined == 1
    assert result.statistics.candidates_added == 1


def test_strict_propagates_lt_then_le() -> None:
    """x<y and y<=z: the chain is strict because the first leg is."""
    x, y, z = z3.Ints("x y z")
    rel = _rel("inv", z3.IntSort(), z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {rel: (x < y, y <= z)}

    result = mutate_candidates(candidates)
    got = _sexprs(result.candidates[rel])

    assert z3.simplify(x < z).sexpr() in got
    assert z3.simplify(x <= z).sexpr() not in got


def test_strict_propagates_le_then_lt() -> None:
    """x<=y and y<z: the chain is strict because the second leg is."""
    x, y, z = z3.Ints("x y z")
    rel = _rel("inv", z3.IntSort(), z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {rel: (x <= y, y < z)}

    result = mutate_candidates(candidates)
    got = _sexprs(result.candidates[rel])

    assert z3.simplify(x < z).sexpr() in got


def test_ge_and_gt_are_normalized_before_chaining() -> None:
    """y>=x (i.e. x<=y) and z>=y (i.e. y<=z) should chain to x<=z just
    like the direct <= forms do -- normalization must happen first."""
    x, y, z = z3.Ints("x y z")
    rel = _rel("inv", z3.IntSort(), z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {rel: (y >= x, z >= y)}

    result = mutate_candidates(candidates)
    got = _sexprs(result.candidates[rel])

    assert z3.simplify(x <= z).sexpr() in got


def test_unrelated_inequalities_do_not_chain() -> None:
    """x<=y and a<=b share no term -- nothing should be derived."""
    x, y, a, b = z3.Ints("x y a b")
    rel = _rel("inv", z3.IntSort(), z3.IntSort(), z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {rel: (x <= y, a <= b)}

    result = mutate_candidates(candidates)

    assert rel not in result.candidates
    assert result.statistics.inequality_chains_combined == 0


def test_mut_never_combines_across_different_relations() -> None:
    """x<=y for one relation and y<=z for a completely different one must
    not chain -- mutation only reasons within a single relation's pool."""
    x, y, z = z3.Ints("x y z")
    rel_p = _rel("p", z3.IntSort(), z3.IntSort())
    rel_q = _rel("q", z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {rel_p: (x <= y,), rel_q: (y <= z,)}

    result = mutate_candidates(candidates)

    assert rel_p not in result.candidates
    assert rel_q not in result.candidates


# ---------------------------------------------------------------------------
# Filtering: trivial results and duplicates
# ---------------------------------------------------------------------------


def test_trivial_chain_is_filtered() -> None:
    """x<=y and y<=x together chain to x<=x both ways -- both trivially
    true, both must be dropped, even though two chain attempts were made."""
    x, y = z3.Ints("x y")
    rel = _rel("inv", z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {rel: (x <= y, y <= x)}

    result = mutate_candidates(candidates)

    assert rel not in result.candidates
    assert result.statistics.inequality_chains_combined == 2
    assert result.statistics.candidates_added == 0


def test_chain_already_present_is_not_reported_as_new() -> None:
    """If x<=z is already in the pool, deriving it again from x<=y and
    y<=z must not count as a new candidate."""
    x, y, z = z3.Ints("x y z")
    rel = _rel("inv", z3.IntSort(), z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {rel: (x <= y, y <= z, x <= z)}

    result = mutate_candidates(candidates)

    assert rel not in result.candidates


# ---------------------------------------------------------------------------
# Non-arithmetic candidates are left alone
# ---------------------------------------------------------------------------


def test_non_arithmetic_candidates_are_ignored() -> None:
    """A String equality/comparison-shaped candidate must not be treated as
    numeric -- str.<= doesn't exist, but guard against ever trying to."""
    s = z3.String("s")
    t = z3.String("t")
    rel = _rel("inv", z3.StringSort(), z3.StringSort())
    candidates: CandidateMap = {rel: (s == t,)}

    result = mutate_candidates(candidates)

    assert rel not in result.candidates
    assert result.statistics.equalities_considered == 0
    assert result.statistics.inequalities_considered == 0


def test_boolean_candidate_is_ignored() -> None:
    """A plain boolean candidate (no comparison at all) contributes to
    neither bucket and causes no error."""
    p = z3.Bool("p")
    rel = _rel("inv", z3.BoolSort())
    candidates: CandidateMap = {rel: (p,)}

    result = mutate_candidates(candidates)

    assert rel not in result.candidates
    assert result.statistics.equalities_considered == 0
    assert result.statistics.inequalities_considered == 0


# ---------------------------------------------------------------------------
# Sort-agnostic equality substitution
# ---------------------------------------------------------------------------


def test_string_equality_substitutes_into_length() -> None:
    """s = t together with str.len(s) == n yields str.len(t) == n (and the
    symmetric rewrite). Sound under the equality invariant."""
    s = z3.String("s")
    t = z3.String("t")
    n = z3.Int("n")
    rel = _rel("inv", z3.StringSort(), z3.StringSort(), z3.IntSort())
    candidates: CandidateMap = {
        rel: (s == t, z3.Length(s) == n),
    }

    result = mutate_candidates(candidates)
    got = _sexprs(result.candidates.get(rel, ()))

    expected = {
        z3.simplify(z3.Length(t) == n).sexpr(),
        # also the length equality rewritten the other way is the same form
    }
    assert expected <= got
    # Both the String equality and the arithmetic length equality are
    # general equalities.
    assert result.statistics.general_equalities_considered == 2
    assert result.statistics.substitution_candidates_added >= 1


def test_array_equality_substitutes_into_select() -> None:
    """a = b and Select(a, i) == v yield Select(b, i) == v."""
    a = z3.Array("a", z3.IntSort(), z3.IntSort())
    b = z3.Array("b", z3.IntSort(), z3.IntSort())
    i = z3.Int("i")
    v = z3.Int("v")
    rel = _rel("inv", a.sort(), b.sort(), z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {
        rel: (a == b, z3.Select(a, i) == v),
    }

    result = mutate_candidates(candidates)
    got = _sexprs(result.candidates.get(rel, ()))

    expected = {z3.simplify(z3.Select(b, i) == v).sexpr()}
    assert expected <= got
    # Array equality + arithmetic select equality.
    assert result.statistics.general_equalities_considered == 2


def test_arithmetic_equality_also_feeds_substitution() -> None:
    """Numeric equalities still participate in the general substitution pass
    in addition to the +/- combination pass."""
    x, y, a = z3.Ints("x y a")
    rel = _rel("inv", z3.IntSort(), z3.IntSort())
    # x == a and y >= x  →  substitution yields y >= a
    candidates: CandidateMap = {rel: (x == a, y >= x)}

    result = mutate_candidates(candidates)
    got = _sexprs(result.candidates.get(rel, ()))

    expected = {z3.simplify(y >= a).sexpr()}
    assert expected <= got
    assert result.statistics.general_equalities_considered == 1
    assert result.statistics.substitution_candidates_added >= 1


def test_substitution_cap_is_respected() -> None:
    """max_equality_substitutions_per_relation bounds rewrite attempts."""
    x, y, a, b = z3.Ints("x y a b")
    rel = _rel("inv", z3.IntSort(), z3.IntSort())
    candidates: CandidateMap = {
        rel: (x == a, y == b, x + y > 0, x - y < 10),
    }

    result = mutate_candidates(
        candidates, max_equality_substitutions_per_relation=2
    )
    assert result.statistics.substitution_rewrites_attempted <= 2
    assert result.statistics.substitutions_dropped_by_cap >= 0
