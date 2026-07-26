"""Tests for :mod:`pyhorn_bnd.cands` -- parse_candidate_file and merge_candidate_maps.

All variable-map fixtures use real ``z3.FuncDeclRef`` keys, matching the
actual ``VariableMap = dict[z3.FuncDeclRef, tuple[z3.ExprRef, ...]]`` type
that :class:`.SeedMiner` produces and :class:`.MultiHoudini` expects. Using
plain ``str`` keys would make these tests pass for the wrong reason: a
``str``-vs-``FuncDeclRef`` membership check silently fails to match anything.

Z3 expression equality is checked via ``.sexpr()`` strings throughout,
because Python's ``==`` on symbolic Z3 expressions builds a new ``z3.BoolRef``
rather than comparing structurally, and ``bool()`` of that expression raises
``Z3Exception``.
"""

from __future__ import annotations

import textwrap
from pathlib import Path

import pytest
import z3

from pyhorn_bnd.cands import (
    format_candidates_smt2,
    merge_candidate_maps,
    parse_candidate_file,
)
from pyhorn_bnd.horn import HornParseError

# ---------------------------------------------------------------------------
# Shared fixtures
# ---------------------------------------------------------------------------


def _rel(name: str, *sorts: z3.SortRef) -> z3.FuncDeclRef:
    """Create a Z3 uninterpreted-predicate declaration (Bool-returning)."""
    return z3.Function(name, *sorts, z3.BoolSort())


def _write(tmp_path: Path, content: str) -> Path:
    p = tmp_path / "cands.smt2"
    p.write_text(textwrap.dedent(content), encoding="utf-8")
    return p


def _sexprs(cands: tuple[z3.BoolRef, ...]) -> set[str]:
    return {c.sexpr() for c in cands}


def _inv_variables() -> tuple[z3.FuncDeclRef, dict]:
    x = z3.Int("x")
    n = z3.Int("n")
    rel = _rel("inv", z3.IntSort(), z3.IntSort())
    return rel, {rel: (x, n)}


# ---------------------------------------------------------------------------
# parse_candidate_file -- happy path
# ---------------------------------------------------------------------------


class TestParseCandidateFileHappyPath:
    def test_single_conjunct(self, tmp_path: Path) -> None:
        rel, variables = _inv_variables()
        p = _write(
            tmp_path,
            """\
            (define-fun inv ((x Int) (n Int)) Bool
              (>= x 0))
            """,
        )
        result = parse_candidate_file(p, variables)
        assert set(result.keys()) == {rel}
        assert len(result[rel]) == 1
        assert result[rel][0].sexpr() == z3.simplify(z3.Int("x") >= 0).sexpr()

    def test_conjunction_is_split(self, tmp_path: Path) -> None:
        rel, variables = _inv_variables()
        p = _write(
            tmp_path,
            """\
            (define-fun inv ((x Int) (n Int)) Bool
              (and (>= x 0) (<= x n)))
            """,
        )
        result = parse_candidate_file(p, variables)
        assert len(result[rel]) == 2
        x, n = z3.Int("x"), z3.Int("n")
        sexprs = _sexprs(result[rel])
        assert z3.simplify(x >= 0).sexpr() in sexprs
        assert z3.simplify(x <= n).sexpr() in sexprs

    def test_conjunction_revealed_only_after_simplification_is_split(
        self, tmp_path: Path
    ) -> None:
        """A body that only becomes a top-level And after simplification (e.g.
        a tautological `ite`) is still split into separate conjuncts, matching
        the convention used for ordinary CHC rule bodies in horn.py."""
        rel, variables = _inv_variables()
        p = _write(
            tmp_path,
            """\
            (define-fun inv ((x Int) (n Int)) Bool
              (ite true (and (>= x 0) (<= x n)) false))
            """,
        )
        result = parse_candidate_file(p, variables)
        x, n = z3.Int("x"), z3.Int("n")
        sexprs = _sexprs(result[rel])
        assert len(result[rel]) == 2
        assert z3.simplify(x >= 0).sexpr() in sexprs
        assert z3.simplify(x <= n).sexpr() in sexprs

    def test_two_defines_same_predicate_merged(self, tmp_path: Path) -> None:
        rel, variables = _inv_variables()
        p = _write(
            tmp_path,
            """\
            (define-fun inv ((x Int) (n Int)) Bool (>= x 0))
            (define-fun inv ((x Int) (n Int)) Bool (<= x n))
            """,
        )
        result = parse_candidate_file(p, variables)
        assert len(result[rel]) == 2

    def test_duplicate_conjuncts_deduped(self, tmp_path: Path) -> None:
        rel, variables = _inv_variables()
        p = _write(
            tmp_path,
            """\
            (define-fun inv ((x Int) (n Int)) Bool (>= x 0))
            (define-fun inv ((x Int) (n Int)) Bool (>= x 0))
            """,
        )
        result = parse_candidate_file(p, variables)
        assert len(result[rel]) == 1

    def test_unknown_predicate_skipped(self, tmp_path: Path) -> None:
        rel, variables = _inv_variables()
        p = _write(
            tmp_path,
            """\
            (define-fun other ((x Int)) Bool (>= x 0))
            (define-fun inv   ((x Int) (n Int)) Bool (>= x 0))
            """,
        )
        result = parse_candidate_file(p, variables)
        assert set(result.keys()) == {rel}

    def test_file_with_only_unknown_predicate_returns_empty_map(
        self, tmp_path: Path
    ) -> None:
        _, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun other_pred ((x Int)) Bool (>= x 0))\n")
        assert parse_candidate_file(p, variables) == {}

    def test_trivially_true_dropped(self, tmp_path: Path) -> None:
        rel, variables = _inv_variables()
        p = _write(
            tmp_path,
            """\
            (define-fun inv ((x Int) (n Int)) Bool
              (and true (>= x 0)))
            """,
        )
        result = parse_candidate_file(p, variables)
        assert len(result[rel]) == 1

    def test_wholly_trivial_body_omits_predicate(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv ((x Int) (n Int)) Bool true)\n")
        result = parse_candidate_file(p, variables)
        assert result == {}

    def test_wholly_false_body_omits_predicate(self, tmp_path: Path) -> None:
        """`And` with a literally-false conjunct collapses to False as a
        whole under simplification (P and False == False, unconditionally),
        so the predicate ends up with zero retained conjuncts and is omitted
        -- the same outcome as a wholly-true body, just for the opposite
        reason."""
        rel, variables = _inv_variables()
        p = _write(
            tmp_path,
            """\
            (define-fun inv ((x Int) (n Int)) Bool
              (and false (>= x 0)))
            """,
        )
        result = parse_candidate_file(p, variables)
        assert rel not in result

    def test_trivially_false_disjunct_branch_dropped(self, tmp_path: Path) -> None:
        """A locally-false sub-formula that does *not* propagate to make the
        whole body false (here, an unreachable `ite` branch) still leaves the
        real conjuncts intact."""
        rel, variables = _inv_variables()
        p = _write(
            tmp_path,
            """\
            (define-fun inv ((x Int) (n Int)) Bool
              (and (>= x 0) (ite false (= x 999) true)))
            """,
        )
        result = parse_candidate_file(p, variables)
        assert len(result[rel]) == 1
        x = z3.Int("x")
        assert result[rel][0].sexpr() == z3.simplify(x >= 0).sexpr()

    def test_result_keys_are_funcdeclref(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv ((x Int) (n Int)) Bool (>= x 0))\n")
        result = parse_candidate_file(p, variables)
        for key in result:
            assert isinstance(key, z3.FuncDeclRef)

    def test_result_key_is_the_same_object_from_variables(
        self, tmp_path: Path
    ) -> None:
        rel, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv ((x Int) (n Int)) Bool (>= x 0))\n")
        result = parse_candidate_file(p, variables)
        (key,) = result.keys()
        assert key is rel

    def test_result_values_are_tuples(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv ((x Int) (n Int)) Bool (>= x 0))\n")
        result = parse_candidate_file(p, variables)
        for val in result.values():
            assert isinstance(val, tuple)

    def test_two_predicates(self, tmp_path: Path) -> None:
        x, n = z3.Int("x"), z3.Int("n")
        rel_inv = _rel("inv", z3.IntSort(), z3.IntSort())
        rel_post = _rel("post", z3.IntSort())
        variables = {rel_inv: (x, n), rel_post: (n,)}
        p = _write(
            tmp_path,
            """\
            (define-fun inv  ((x Int) (n Int)) Bool (>= x 0))
            (define-fun post ((n Int))         Bool (>= n 0))
            """,
        )
        result = parse_candidate_file(p, variables)
        assert set(result.keys()) == {rel_inv, rel_post}
        assert len(result[rel_inv]) == 1
        assert len(result[rel_post]) == 1

    def test_non_define_fun_commands_ignored(self, tmp_path: Path) -> None:
        rel, variables = _inv_variables()
        p = _write(
            tmp_path,
            """\
            (set-logic HORN)
            (declare-fun inv (Int Int) Bool)
            ; a comment
            (define-fun inv ((x Int) (n Int)) Bool (>= x 0))
            """,
        )
        result = parse_candidate_file(p, variables)
        assert len(result[rel]) == 1

    def test_empty_file_returns_empty_map(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(tmp_path, "")
        assert parse_candidate_file(p, variables) == {}

    def test_variable_renaming_is_positional(self, tmp_path: Path) -> None:
        """Parameters named differently from canonical vars still bind correctly."""
        x, n = z3.Int("x"), z3.Int("n")
        rel = _rel("inv", z3.IntSort(), z3.IntSort())
        variables = {rel: (x, n)}
        p = _write(tmp_path, "(define-fun inv ((a Int) (b Int)) Bool (>= a 0))\n")
        result = parse_candidate_file(p, variables)
        assert len(result[rel]) == 1
        assert result[rel][0].sexpr() == z3.simplify(x >= 0).sexpr()

    def test_unused_parameter_is_tolerated(self, tmp_path: Path) -> None:
        rel, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv ((x Int) (n Int)) Bool (>= x 0))\n")
        result = parse_candidate_file(p, variables)
        assert len(result[rel]) == 1

    def test_array_sorted_parameter_binds_without_declare_sort(
        self, tmp_path: Path
    ) -> None:
        """Parameters are bound to their real canonical variable, so compound
        sorts (arrays, datatypes, ...) never need to be re-declared textually
        inside the candidate file."""
        arr = z3.Const("a", z3.ArraySort(z3.IntSort(), z3.IntSort()))
        rel = _rel("inv", z3.ArraySort(z3.IntSort(), z3.IntSort()))
        variables = {rel: (arr,)}
        p = _write(
            tmp_path,
            "(define-fun inv ((arr (Array Int Int))) Bool (>= (select arr 0) 0))\n",
        )
        result = parse_candidate_file(p, variables)
        assert len(result[rel]) == 1
        assert "select" in result[rel][0].sexpr()

    def test_body_referencing_symbol_declared_elsewhere_in_file_raises(
        self, tmp_path: Path
    ) -> None:
        """Known, documented limitation: each define-fun body is parsed in
        isolation, so it cannot see a `declare-const`/`declare-fun` written
        elsewhere in the same candidate file -- only its own parameters and
        ordinary SMT-LIB2 operators/literals are in scope."""
        sort = z3.DeclareSort("MyThing")
        c = z3.Const("c", sort)
        rel = _rel("inv", sort)
        variables = {rel: (c,)}
        p = _write(
            tmp_path,
            "(declare-const other MyThing)\n"
            "(define-fun inv ((t MyThing)) Bool (distinct t other))\n",
        )
        with pytest.raises(HornParseError):
            parse_candidate_file(p, variables)

    def test_body_referencing_only_its_own_parameter_succeeds(
        self, tmp_path: Path
    ) -> None:
        sort = z3.DeclareSort("MyThing")
        c = z3.Const("c", sort)
        rel = _rel("inv", sort)
        variables = {rel: (c,)}
        p = _write(tmp_path, "(define-fun inv ((t MyThing)) Bool (= t t))\n")
        result = parse_candidate_file(p, variables)
        # (= t t) simplifies to true and is dropped entirely -> predicate absent.
        assert rel not in result

    def test_quantified_body_is_supported(self, tmp_path: Path) -> None:
        x, n = z3.Int("x"), z3.Int("n")
        rel = _rel("inv", z3.IntSort(), z3.IntSort())
        variables = {rel: (x, n)}
        p = _write(
            tmp_path,
            "(define-fun inv ((x Int) (n Int)) Bool "
            "(forall ((k Int)) (=> (= k x) (>= k 0))))\n",
        )
        result = parse_candidate_file(p, variables)
        assert len(result[rel]) == 1


# ---------------------------------------------------------------------------
# parse_candidate_file -- error path
# ---------------------------------------------------------------------------


class TestParseCandidateFileErrors:
    def test_file_not_found(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        with pytest.raises(FileNotFoundError):
            parse_candidate_file(tmp_path / "missing.smt2", variables)

    def test_wrong_return_sort_raises(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv ((x Int) (n Int)) Int x)\n")
        with pytest.raises(HornParseError, match="return sort must be Bool"):
            parse_candidate_file(p, variables)

    def test_arity_mismatch_too_few_raises(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv ((x Int)) Bool (>= x 0))\n")
        with pytest.raises(HornParseError, match="parameter"):
            parse_candidate_file(p, variables)

    def test_arity_mismatch_too_many_raises(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(
            tmp_path,
            "(define-fun inv ((x Int) (n Int) (extra Int)) Bool (>= x 0))\n",
        )
        with pytest.raises(HornParseError, match="parameter"):
            parse_candidate_file(p, variables)

    def test_z3_parse_error_raises(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(
            tmp_path,
            "(define-fun inv ((x Int) (n Int)) Bool (not_a_valid_operator x))\n",
        )
        with pytest.raises(HornParseError):
            parse_candidate_file(p, variables)

    def test_undeclared_identifier_in_body_raises(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv ((x Int) (n Int)) Bool (>= ghost 0))\n")
        with pytest.raises(HornParseError):
            parse_candidate_file(p, variables)

    def test_sort_mismatch_in_body_raises(self, tmp_path: Path) -> None:
        """Even though the sort annotation isn't reparsed, an incompatible
        usage of a canonical (Int) variable as if it were Bool must still be
        rejected by Z3's own type checking."""
        _, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv ((x Int) (n Int)) Bool (and x true))\n")
        with pytest.raises(HornParseError):
            parse_candidate_file(p, variables)

    def test_malformed_parameter_entry_raises(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv (x n) Bool (>= x 0))\n")
        with pytest.raises(HornParseError, match="malformed parameter"):
            parse_candidate_file(p, variables)

    def test_duplicate_parameter_name_raises(self, tmp_path: Path) -> None:
        _, variables = _inv_variables()
        p = _write(
            tmp_path, "(define-fun inv ((x Int) (x Int)) Bool (>= x 0))\n"
        )
        with pytest.raises(HornParseError, match="duplicate parameter"):
            parse_candidate_file(p, variables)

    def test_malformed_s_expression_raises_horn_parse_error(
        self, tmp_path: Path
    ) -> None:
        """Unbalanced parens must surface as HornParseError (not SExprError),
        matching parse_chc_file's convention so callers only need to catch
        one exception family (see cli.py's `except (HornParseError, ...)`)."""
        _, variables = _inv_variables()
        p = _write(tmp_path, "(define-fun inv ((x Int) (n Int)) Bool (>= x 0)\n")
        with pytest.raises(HornParseError):
            parse_candidate_file(p, variables)

# ---------------------------------------------------------------------------
# merge_candidate_maps
# ---------------------------------------------------------------------------


class TestMergeCandidateMaps:
    def test_disjoint_relations_unioned(self) -> None:
        x, n = z3.Int("x"), z3.Int("n")
        rel_a = _rel("inv", z3.IntSort(), z3.IntSort())
        rel_b = _rel("post", z3.IntSort())
        base = {rel_a: (z3.simplify(x >= 0),)}
        extra = {rel_b: (z3.simplify(n >= 0),)}
        merged = merge_candidate_maps(base, extra)
        assert set(merged.keys()) == {rel_a, rel_b}

    def test_extra_conjuncts_appended(self) -> None:
        x, n = z3.Int("x"), z3.Int("n")
        rel = _rel("inv", z3.IntSort(), z3.IntSort())
        c1 = z3.simplify(x >= 0)
        c2 = z3.simplify(x <= n)
        base = {rel: (c1,)}
        extra = {rel: (c2,)}
        merged = merge_candidate_maps(base, extra)
        assert len(merged[rel]) == 2
        sxs = _sexprs(merged[rel])
        assert c1.sexpr() in sxs
        assert c2.sexpr() in sxs

    def test_duplicate_conjuncts_not_added(self) -> None:
        x = z3.Int("x")
        rel = _rel("inv", z3.IntSort())
        c = z3.simplify(x >= 0)
        base = {rel: (c,)}
        extra = {rel: (c,)}
        merged = merge_candidate_maps(base, extra)
        assert len(merged[rel]) == 1

    def test_base_not_mutated(self) -> None:
        x, n = z3.Int("x"), z3.Int("n")
        rel = _rel("inv", z3.IntSort(), z3.IntSort())
        original = (z3.simplify(x >= 0),)
        base = {rel: original}
        extra = {rel: (z3.simplify(x <= n),)}
        merge_candidate_maps(base, extra)
        assert len(base[rel]) == 1
        assert base[rel][0].sexpr() == original[0].sexpr()

    def test_extra_not_mutated(self) -> None:
        x, n = z3.Int("x"), z3.Int("n")
        rel = _rel("inv", z3.IntSort(), z3.IntSort())
        base = {rel: (z3.simplify(x >= 0),)}
        original = (z3.simplify(x <= n),)
        extra = {rel: original}
        merge_candidate_maps(base, extra)
        assert len(extra[rel]) == 1
        assert extra[rel][0].sexpr() == original[0].sexpr()

    def test_empty_base(self) -> None:
        x = z3.Int("x")
        rel = _rel("inv", z3.IntSort())
        c = z3.simplify(x >= 0)
        merged = merge_candidate_maps({}, {rel: (c,)})
        assert set(merged.keys()) == {rel}
        assert len(merged[rel]) == 1

    def test_empty_extra(self) -> None:
        x = z3.Int("x")
        rel = _rel("inv", z3.IntSort())
        c = z3.simplify(x >= 0)
        merged = merge_candidate_maps({rel: (c,)}, {})
        assert set(merged.keys()) == {rel}
        assert len(merged[rel]) == 1

    def test_both_empty(self) -> None:
        assert merge_candidate_maps({}, {}) == {}

    def test_result_values_are_tuples(self) -> None:
        x = z3.Int("x")
        rel = _rel("inv", z3.IntSort())
        merged = merge_candidate_maps(
            {rel: (z3.simplify(x >= 0),)},
            {rel: (z3.simplify(x <= 10),)},
        )
        for val in merged.values():
            assert isinstance(val, tuple)


# ---------------------------------------------------------------------------
# format_candidates_smt2 -- the serialization counterpart of
# parse_candidate_file, used by --dump-cands
# ---------------------------------------------------------------------------


class TestFormatCandidatesSmt2:
    def test_single_predicate_single_conjunct(self) -> None:
        x = z3.Int("x")
        rel = _rel("inv", z3.IntSort())
        cand = z3.simplify(x >= 0)
        text = format_candidates_smt2({rel: (cand,)}, {rel: (x,)})
        assert text.strip() == f"(define-fun inv ((x Int)) Bool {cand.sexpr()})"

    def test_multiple_conjuncts_wrapped_in_and(self) -> None:
        x, n = z3.Int("x"), z3.Int("n")
        rel = _rel("inv", z3.IntSort(), z3.IntSort())
        c1, c2 = z3.simplify(x >= 0), z3.simplify(x <= n)
        text = format_candidates_smt2({rel: (c1, c2)}, {rel: (x, n)})
        assert text.count("(and") == 1
        assert c1.sexpr() in text
        assert c2.sexpr() in text

    def test_relation_with_zero_conjuncts_omitted(self) -> None:
        rel = _rel("inv", z3.IntSort())
        x = z3.Int("x")
        text = format_candidates_smt2({rel: ()}, {rel: (x,)})
        assert text == ""

    def test_empty_candidate_map_without_header_is_empty_string(self) -> None:
        assert format_candidates_smt2({}, {}) == ""

    def test_header_preserved_even_with_no_candidates(self) -> None:
        text = format_candidates_smt2({}, {}, header="nothing survived")
        assert "; nothing survived" in text
        assert "define-fun" not in text

    def test_header_lines_are_comments(self) -> None:
        rel = _rel("inv", z3.IntSort())
        x = z3.Int("x")
        text = format_candidates_smt2(
            {rel: (z3.simplify(x >= 0),)},
            {rel: (x,)},
            header="line one\nline two",
        )
        lines = text.splitlines()
        assert lines[0] == "; line one"
        assert lines[1] == "; line two"
        assert any(line.startswith("(define-fun") for line in lines)

    def test_multiple_predicates_sorted_by_name(self) -> None:
        x, n = z3.Int("x"), z3.Int("n")
        rel_q = _rel("q", z3.IntSort())
        rel_p = _rel("p", z3.IntSort(), z3.IntSort())
        text = format_candidates_smt2(
            {
                rel_q: (z3.simplify(x >= 0),),
                rel_p: (z3.simplify(x <= n),),
            },
            {rel_q: (x,), rel_p: (x, n)},
        )
        # 'p' must come before 'q' regardless of dict insertion order.
        assert text.index("define-fun p") < text.index("define-fun q")

    def test_output_ends_with_single_trailing_newline(self) -> None:
        rel = _rel("inv", z3.IntSort())
        x = z3.Int("x")
        text = format_candidates_smt2({rel: (z3.simplify(x >= 0),)}, {rel: (x,)})
        assert text.endswith("\n")
        assert not text.endswith("\n\n")

    def test_output_is_not_the_print_invariants_infix_form(self) -> None:
        """The infix form ('0 <= x') that --print-invariants shows is not
        valid SMT-LIB2; the serializer must use s-expression (prefix) form."""
        x = z3.Int("x")
        rel = _rel("inv", z3.IntSort())
        cand = z3.simplify(x >= 0)
        infix = str(cand)
        text = format_candidates_smt2({rel: (cand,)}, {rel: (x,)})
        assert infix not in text
        assert cand.sexpr() in text

    def test_round_trip_via_parse_candidate_file(self, tmp_path: Path) -> None:
        x, n = z3.Int("x"), z3.Int("n")
        rel = _rel("inv", z3.IntSort(), z3.IntSort())
        variables = {rel: (x, n)}
        original = {rel: (z3.simplify(x >= 0), z3.simplify(x <= n))}

        text = format_candidates_smt2(original, variables)
        p = tmp_path / "dump.smt2"
        p.write_text(text, encoding="utf-8")
        reparsed = parse_candidate_file(p, variables)

        assert set(reparsed.keys()) == set(original.keys())
        assert _sexprs(reparsed[rel]) == _sexprs(original[rel])

    def test_round_trip_preserves_array_sorted_parameters(
        self, tmp_path: Path
    ) -> None:
        """The serializer must reproduce a compound sort (here, Array) as
        valid SMT-LIB2 sort syntax via z3.SortRef.sexpr(), not by guessing
        from the variable's name."""
        arr_sort = z3.ArraySort(z3.IntSort(), z3.IntSort())
        arr = z3.Const("a", arr_sort)
        rel = _rel("inv", arr_sort)
        variables = {rel: (arr,)}
        original = {rel: (z3.simplify(z3.Select(arr, 0) >= 0),)}

        text = format_candidates_smt2(original, variables)
        assert "(Array Int Int)" in text
        p = tmp_path / "dump.smt2"
        p.write_text(text, encoding="utf-8")
        reparsed = parse_candidate_file(p, variables)

        assert _sexprs(reparsed[rel]) == _sexprs(original[rel])

    def test_round_trip_preserves_uninterpreted_sort(self, tmp_path: Path) -> None:
        sort = z3.DeclareSort("MyThing")
        c1, c2 = z3.Const("c1", sort), z3.Const("c2", sort)
        rel = _rel("inv", sort, sort)
        variables = {rel: (c1, c2)}
        original = {rel: (z3.simplify(z3.Distinct(c1, c2)),)}

        text = format_candidates_smt2(original, variables)
        p = tmp_path / "dump.smt2"
        p.write_text(text, encoding="utf-8")
        reparsed = parse_candidate_file(p, variables)

        assert _sexprs(reparsed[rel]) == _sexprs(original[rel])

    def test_predicate_name_needing_quoting_round_trips(self, tmp_path: Path) -> None:
        """A predicate name containing a character outside SMT-LIB2's simple
        symbol class is written as a |quoted symbol| and read back as the
        same relation (parse_candidate_file unquotes before matching)."""
        x = z3.Int("x")
        rel = _rel("weird name!", z3.IntSort())
        variables = {rel: (x,)}
        original = {rel: (z3.simplify(x >= 0),)}

        text = format_candidates_smt2(original, variables)
        assert "|weird name!|" in text
        p = tmp_path / "dump.smt2"
        p.write_text(text, encoding="utf-8")
        reparsed = parse_candidate_file(p, variables)

        assert set(reparsed.keys()) == {rel}
        assert _sexprs(reparsed[rel]) == _sexprs(original[rel])

    def test_missing_relation_in_variables_raises_key_error(self) -> None:
        rel = _rel("inv", z3.IntSort())
        x = z3.Int("x")
        with pytest.raises(KeyError):
            format_candidates_smt2({rel: (z3.simplify(x >= 0),)}, {})
