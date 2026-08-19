"""Invariant-candidate mining from bounded reachable-state models.

The miner enumerates connected ENTRY prefixes, solves their positional SSA
encodings, extracts concrete destination states, and generalizes observations
into a finite candidate language.  Candidates are hypotheses only:
``MultiHoudini`` must prove or remove every generated formula before PyHorn can
report ``Success``.
"""

from __future__ import annotations

from collections import deque
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
from enum import Enum
from fractions import Fraction
from itertools import permutations
from math import gcd, lcm

import z3

from .horn import ENTRY, HornProgram, HornRule
from .seedminer import CandidateMap, VariableMap
from .vc import VerificationConditionBuilder

DEFAULT_TRACE_DEPTH = 8
DEFAULT_TRACE_LIMIT = 1_000
DEFAULT_MODELS_PER_PREFIX = 2
DEFAULT_SAMPLES_PER_RELATION = 64
DEFAULT_TRACE_CANDIDATES_PER_RELATION = 256
DEFAULT_MAX_CONGRUENCE_MODULUS = 8
DEFAULT_MAX_AFFINE_COEFFICIENT = 64


class TraceTemplateId(str, Enum):
    """Stable identifiers for every trace-generalization template."""

    BOOLEAN_TRUE = "boolean.always-true"
    BOOLEAN_FALSE = "boolean.always-false"
    NUMERIC_CONSTANT = "numeric.constant"
    NUMERIC_LOWER_BOUND = "numeric.lower-bound"
    NUMERIC_UPPER_BOUND = "numeric.upper-bound"
    INTEGER_CONGRUENCE = "integer.congruence"
    AFFINE_EQUALITY = "numeric.affine-equality"
    STRING_CONSTANT = "string.constant"
    STRING_COMMON_PREFIX = "string.common-prefix"
    STRING_COMMON_SUFFIX = "string.common-suffix"
    STRING_ALPHABET_CLOSURE = "string.observed-alphabet-closure"
    STRING_CHAR_COUNT_MODULO = "string.char-count-modulo"
    STRING_CHAR_COUNT_MODULO_SET = "string.char-count-modulo-set"
    STRING_EQUALITY = "string.equality"
    STRING_PREFIX_RELATION = "string.prefix-relation"
    STRING_SUFFIX_RELATION = "string.suffix-relation"
    STRING_CONCATENATION = "string.concatenation"


@dataclass(frozen=True)
class TraceTemplateSpecification:
    """Machine-readable contract for one supported template family."""

    template_id: TraceTemplateId
    domain: str
    formula_schema: str
    applicable_features: tuple[str, ...]
    emission_condition: str


TRACE_TEMPLATE_SPECIFICATIONS: tuple[TraceTemplateSpecification, ...] = (
    TraceTemplateSpecification(
        TraceTemplateId.BOOLEAN_TRUE,
        "Bool",
        "b",
        ("Boolean predicate argument b",),
        "Every retained sample evaluates b to true.",
    ),
    TraceTemplateSpecification(
        TraceTemplateId.BOOLEAN_FALSE,
        "Bool",
        "(not b)",
        ("Boolean predicate argument b",),
        "Every retained sample evaluates b to false.",
    ),
    TraceTemplateSpecification(
        TraceTemplateId.NUMERIC_CONSTANT,
        "Int/Real/String length",
        "(= f c)",
        (
            "numeric predicate argument",
            "length of a string predicate argument",
            "difference f_i - f_j of two base numeric features",
        ),
        "All exact sampled values of feature f are the same rational c.",
    ),
    TraceTemplateSpecification(
        TraceTemplateId.NUMERIC_LOWER_BOUND,
        "Int/Real/String length",
        "(>= f min(S_f))",
        (
            "numeric predicate argument",
            "length of a string predicate argument",
            "difference f_i - f_j of two base numeric features",
        ),
        "Feature f has at least two distinct sampled values.",
    ),
    TraceTemplateSpecification(
        TraceTemplateId.NUMERIC_UPPER_BOUND,
        "Int/Real/String length",
        "(<= f max(S_f))",
        (
            "numeric predicate argument",
            "length of a string predicate argument",
            "difference f_i - f_j of two base numeric features",
        ),
        "Feature f has at least two distinct sampled values.",
    ),
    TraceTemplateSpecification(
        TraceTemplateId.INTEGER_CONGRUENCE,
        "Int/String length",
        "(= (mod f m) r)",
        (
            "integer predicate argument",
            "length of a string predicate argument",
            "difference of two integral base features",
        ),
        (
            "For each modulus 2 <= m <= max_congruence_modulus, all sampled "
            "integer values of f have the same residue r modulo m."
        ),
    ),
    TraceTemplateSpecification(
        TraceTemplateId.AFFINE_EQUALITY,
        "Int/Real/String length",
        "(= (+ (* a_1 f_1) ... (* a_n f_n) a_0) 0)",
        (
            "all numeric predicate arguments",
            "lengths of all string predicate arguments",
        ),
        (
            "There are 2..8 base features and at least two samples; an exact "
            "rational nullspace basis vector of [f_1 ... f_n 1] normalizes to "
            "primitive integer coefficients whose maximum absolute value is "
            "at most max_affine_coefficient."
        ),
    ),
    TraceTemplateSpecification(
        TraceTemplateId.STRING_CONSTANT,
        "String",
        '(= s "w")',
        ("string predicate argument s",),
        'Every sampled value of s is the same concrete string "w".',
    ),
    TraceTemplateSpecification(
        TraceTemplateId.STRING_COMMON_PREFIX,
        "String",
        '(str.prefixof "p" s)',
        ("string predicate argument s",),
        "The longest common prefix p of all sampled strings is nonempty.",
    ),
    TraceTemplateSpecification(
        TraceTemplateId.STRING_COMMON_SUFFIX,
        "String",
        '(str.suffixof "q" s)',
        ("string predicate argument s",),
        "The longest common suffix q of all sampled strings is nonempty.",
    ),
    TraceTemplateSpecification(
        TraceTemplateId.STRING_ALPHABET_CLOSURE,
        "String/RegLan",
        "(str.in_re s (re.* (re.union (str.to_re c_1) ... (str.to_re c_k))))",
        ("string predicate argument s",),
        (
            "The union of Unicode characters observed in all samples has "
            "size 1..16. Empty strings contribute no character."
        ),
    ),
    TraceTemplateSpecification(
        TraceTemplateId.STRING_CHAR_COUNT_MODULO,
        "String/RegLan",
        "(str.in_re s <regex for count(c) ≡ r (mod m)>)",
        (
            "string predicate argument s",
            "observed character c",
            "modulus m in 2..max_congruence_modulus",
        ),
        (
            "For each observed character c and each modulus "
            "2 <= m <= max_congruence_modulus, all sampled strings have the "
            "same residue r = count(s, c) mod m. Empty strings contribute "
            "count 0 for every character."
        ),
    ),
    TraceTemplateSpecification(
        TraceTemplateId.STRING_CHAR_COUNT_MODULO_SET,
        "String/RegLan",
        "(str.in_re s (re.union <regexes for count(c) ≡ r (mod m), r in R>))",
        (
            "string predicate argument s",
            "observed character c",
            "modulus m in 2..max_congruence_modulus",
        ),
        (
            "For each observed character c and each modulus "
            "2 <= m <= max_congruence_modulus, the set R of residues "
            "count(s, c) mod m across samples is a proper nonempty subset "
            "of {0,...,m-1} with |R| >= 2 (some residues are never "
            "observed). Emits the union of the single-residue languages "
            "for r in R. Captures invariants such as count(c) ≢ 0 (mod 3)."
        ),
    ),
    TraceTemplateSpecification(
        TraceTemplateId.STRING_EQUALITY,
        "String",
        "(= s_i s_j)",
        ("two distinct string predicate arguments",),
        "Every sampled pair has identical concrete values.",
    ),
    TraceTemplateSpecification(
        TraceTemplateId.STRING_PREFIX_RELATION,
        "String",
        "(str.prefixof s_i s_j)",
        ("ordered pair of distinct string predicate arguments",),
        "For every sample, the value of s_j starts with the value of s_i.",
    ),
    TraceTemplateSpecification(
        TraceTemplateId.STRING_SUFFIX_RELATION,
        "String",
        "(str.suffixof s_i s_j)",
        ("ordered pair of distinct string predicate arguments",),
        "For every sample, the value of s_j ends with the value of s_i.",
    ),
    TraceTemplateSpecification(
        TraceTemplateId.STRING_CONCATENATION,
        "String",
        "(= s_t (str.++ s_l s_r))",
        ("ordered triple of three distinct string predicate arguments",),
        (
            "There are at most five string arguments and every sampled triple "
            "satisfies value(s_t) = value(s_l) ++ value(s_r)."
        ),
    ),
)


def trace_template_specifications() -> tuple[TraceTemplateSpecification, ...]:
    """Return the complete, stable trace-template registry."""

    return TRACE_TEMPLATE_SPECIFICATIONS


@dataclass(frozen=True)
class TraceStateSample:
    """One concrete state reached by a satisfiable bounded prefix."""

    relation: z3.FuncDeclRef
    depth: int
    rule_ids: tuple[int, ...]
    values: tuple[z3.ExprRef, ...]


@dataclass(frozen=True)
class TraceCandidateObservation:
    """One candidate generalized from reachable-state samples."""

    relation: z3.FuncDeclRef
    template_id: TraceTemplateId
    kind: str
    candidate: z3.BoolRef
    sample_count: int


@dataclass(frozen=True)
class TraceMiningStatistics:
    max_depth: int
    prefixes_checked: int
    sat_prefixes: int
    unsat_prefixes: int
    unknown_prefixes: int
    models_extracted: int
    duplicate_samples: int
    sample_limit_hits: int
    candidate_limit_hits: int
    candidates_mined: int


@dataclass(frozen=True)
class TraceMiningResult:
    variables: VariableMap
    candidates: CandidateMap
    samples: tuple[TraceStateSample, ...]
    observations: tuple[TraceCandidateObservation, ...]
    statistics: TraceMiningStatistics

    @property
    def candidate_count(self) -> int:
        return sum(len(items) for items in self.candidates.values())

    @property
    def sample_count(self) -> int:
        return len(self.samples)


@dataclass(frozen=True, slots=True)
class _Prefix:
    relation: z3.FuncDeclRef | None
    trace: tuple[HornRule, ...]


@dataclass(frozen=True)
class _Feature:
    expression: z3.ArithRef
    values: tuple[Fraction, ...]
    integral: bool
    label: str


class TraceCandidateMiner:
    """Sample bounded reachable states and generalize them into candidates.

    The exploration is breadth-first and exhaustive up to ``max_depth`` unless
    ``max_prefixes`` is reached.  Each satisfiable prefix may contribute several
    models, obtained by blocking the previously observed destination state.
    Only positive reachable-state samples are learned here; Houdini supplies the
    inductiveness and safety checks.
    """

    generator_id = "trace-templates"

    def __init__(
        self,
        program: HornProgram,
        variables: VariableMap,
        *,
        max_depth: int = DEFAULT_TRACE_DEPTH,
        max_prefixes: int = DEFAULT_TRACE_LIMIT,
        models_per_prefix: int = DEFAULT_MODELS_PER_PREFIX,
        max_samples_per_relation: int = DEFAULT_SAMPLES_PER_RELATION,
        max_candidates_per_relation: int = DEFAULT_TRACE_CANDIDATES_PER_RELATION,
        max_congruence_modulus: int = DEFAULT_MAX_CONGRUENCE_MODULUS,
        max_affine_coefficient: int = DEFAULT_MAX_AFFINE_COEFFICIENT,
        timeout_ms: int = 1_000,
        random_seed: int | None = None,
    ) -> None:
        if max_depth < 1:
            raise ValueError("max_depth must be at least 1")
        if max_prefixes < 1:
            raise ValueError("max_prefixes must be at least 1")
        if models_per_prefix < 1:
            raise ValueError("models_per_prefix must be at least 1")
        if max_samples_per_relation < 1:
            raise ValueError("max_samples_per_relation must be at least 1")
        if max_candidates_per_relation < 1:
            raise ValueError("max_candidates_per_relation must be at least 1")
        if max_congruence_modulus < 2:
            raise ValueError("max_congruence_modulus must be at least 2")
        if max_affine_coefficient < 1:
            raise ValueError("max_affine_coefficient must be at least 1")
        if timeout_ms < 0:
            raise ValueError("timeout_ms must be non-negative")
        self.program = program
        self.variables = variables
        self.max_depth = max_depth
        self.max_prefixes = max_prefixes
        self.models_per_prefix = models_per_prefix
        self.max_samples_per_relation = max_samples_per_relation
        self.max_candidates_per_relation = max_candidates_per_relation
        self.max_congruence_modulus = max_congruence_modulus
        self.max_affine_coefficient = max_affine_coefficient
        self.timeout_ms = timeout_ms
        self.random_seed = random_seed
        self.vc_builder = VerificationConditionBuilder(program)

    def generate(self):
        """Return candidates through the neutral generator extension API."""

        from .candidate_generation import CandidateBatch

        result = self.mine()
        return CandidateBatch(
            generator_id=self.generator_id,
            variables=result.variables,
            candidates=result.candidates,
            metadata={
                "models_extracted": result.statistics.models_extracted,
                "template_ids": tuple(
                    sorted({item.template_id.value for item in result.observations})
                ),
            },
        )

    def mine(self) -> TraceMiningResult:
        samples, counters = self._sample_reachable_states()
        by_relation: dict[z3.FuncDeclRef, list[TraceStateSample]] = {
            relation: [] for relation in self.variables
        }
        for sample in samples:
            if sample.relation in by_relation:
                by_relation[sample.relation].append(sample)

        candidate_maps: dict[z3.FuncDeclRef, dict[str, z3.BoolRef]] = {
            relation: {} for relation in self.variables
        }
        observations: list[TraceCandidateObservation] = []
        candidate_limit_hits = 0
        for relation in sorted(self.variables, key=lambda item: str(item.name())):
            relation_samples = by_relation[relation]
            if not relation_samples:
                continue
            for template_id, kind, candidate in self._generalize_relation(
                relation, relation_samples
            ):
                normalized = z3.simplify(candidate)
                if (
                    not z3.is_bool(normalized)
                    or z3.is_true(normalized)
                    or z3.is_false(normalized)
                ):
                    continue
                bucket = candidate_maps[relation]
                key = normalized.sexpr()
                if key in bucket:
                    continue
                if len(bucket) >= self.max_candidates_per_relation:
                    candidate_limit_hits += 1
                    break
                bucket[key] = normalized
                observations.append(
                    TraceCandidateObservation(
                        relation=relation,
                        template_id=template_id,
                        kind=kind,
                        candidate=normalized,
                        sample_count=len(relation_samples),
                    )
                )

        candidates: CandidateMap = {
            relation: tuple(
                expression
                for _, expression in sorted(items.items(), key=lambda item: item[0])
            )
            for relation, items in candidate_maps.items()
        }
        statistics = TraceMiningStatistics(
            max_depth=self.max_depth,
            prefixes_checked=counters["prefixes_checked"],
            sat_prefixes=counters["sat_prefixes"],
            unsat_prefixes=counters["unsat_prefixes"],
            unknown_prefixes=counters["unknown_prefixes"],
            models_extracted=len(samples),
            duplicate_samples=counters["duplicate_samples"],
            sample_limit_hits=counters["sample_limit_hits"],
            candidate_limit_hits=candidate_limit_hits,
            candidates_mined=sum(len(items) for items in candidates.values()),
        )
        return TraceMiningResult(
            variables=self.variables,
            candidates=candidates,
            samples=tuple(samples),
            observations=tuple(observations),
            statistics=statistics,
        )

    def _make_solver(self) -> z3.Solver:
        solver = z3.Solver()
        if self.timeout_ms:
            solver.set(timeout=self.timeout_ms)
        if self.random_seed is not None:
            solver.set(random_seed=self.random_seed)
        return solver

    def _sample_reachable_states(
        self,
    ) -> tuple[list[TraceStateSample], dict[str, int]]:
        queue: deque[_Prefix] = deque([_Prefix(ENTRY, ())])
        samples: list[TraceStateSample] = []
        seen_samples: dict[int, set[tuple[str, ...]]] = {
            relation.get_id(): set() for relation in self.variables
        }
        sample_counts: dict[int, int] = {
            relation.get_id(): 0 for relation in self.variables
        }
        counters = {
            "prefixes_checked": 0,
            "sat_prefixes": 0,
            "unsat_prefixes": 0,
            "unknown_prefixes": 0,
            "duplicate_samples": 0,
            "sample_limit_hits": 0,
        }

        while queue and counters["prefixes_checked"] < self.max_prefixes:
            prefix = queue.popleft()
            if len(prefix.trace) >= self.max_depth:
                continue
            for rule in self.program.outgoing.get(prefix.relation, ()):
                if counters["prefixes_checked"] >= self.max_prefixes:
                    break
                trace = prefix.trace + (rule,)
                counters["prefixes_checked"] += 1
                vc = self.vc_builder.build_prefix(trace)
                solver = self._make_solver()
                solver.add(*(step.constraint for step in vc.steps))
                current = solver.check()
                if current == z3.unsat:
                    counters["unsat_prefixes"] += 1
                    continue
                if current == z3.unknown:
                    counters["unknown_prefixes"] += 1
                    continue
                counters["sat_prefixes"] += 1

                destination = vc.steps[-1].destination_state
                if destination is None:
                    # Query rules have no reachable destination state to sample.
                    continue
                relation = destination.relation
                relation_id = relation.get_id()
                if relation not in self.variables:
                    continue

                for model_index in range(self.models_per_prefix):
                    if sample_counts[relation_id] >= self.max_samples_per_relation:
                        counters["sample_limit_hits"] += 1
                        break
                    if model_index > 0:
                        current = solver.check()
                    if current != z3.sat:
                        if current == z3.unknown:
                            counters["unknown_prefixes"] += 1
                        break
                    model = solver.model()
                    values = tuple(
                        model.eval(variable, model_completion=True)
                        for variable in destination.variables
                    )
                    key = tuple(value.sexpr() for value in values)
                    if key in seen_samples[relation_id]:
                        counters["duplicate_samples"] += 1
                    else:
                        seen_samples[relation_id].add(key)
                        sample_counts[relation_id] += 1
                        samples.append(
                            TraceStateSample(
                                relation=relation,
                                depth=len(trace),
                                rule_ids=vc.rule_ids,
                                values=values,
                            )
                        )
                    if not destination.variables:
                        break
                    solver.add(
                        z3.Or(
                            *(
                                variable != value
                                for variable, value in zip(
                                    destination.variables, values, strict=True
                                )
                            )
                        )
                    )

                if len(trace) < self.max_depth:
                    queue.append(_Prefix(relation, trace))

        return samples, counters

    def _generalize_relation(
        self,
        relation: z3.FuncDeclRef,
        samples: list[TraceStateSample],
    ) -> Iterable[tuple[TraceTemplateId, str, z3.BoolRef]]:
        canonical = self.variables[relation]
        columns = tuple(zip(*(sample.values for sample in samples), strict=True))

        for index, (variable, values) in enumerate(
            zip(canonical, columns, strict=True)
        ):
            yield from self._single_variable_candidates(index, variable, values)

        features = self._numeric_features(canonical, columns)
        yield from self._numeric_relations(features)
        yield from self._string_relations(canonical, columns)

    def _single_variable_candidates(
        self,
        index: int,
        variable: z3.ExprRef,
        values: tuple[z3.ExprRef, ...],
    ) -> Iterable[tuple[TraceTemplateId, str, z3.BoolRef]]:
        if z3.is_bool(variable):
            if all(z3.is_true(value) for value in values):
                yield (TraceTemplateId.BOOLEAN_TRUE, f"bool-{index}-true", variable)
            elif all(z3.is_false(value) for value in values):
                yield (TraceTemplateId.BOOLEAN_FALSE, f"bool-{index}-false", z3.Not(variable))
            return

        fractions = tuple(_as_fraction(value) for value in values)
        if all(value is not None for value in fractions):
            numeric = tuple(value for value in fractions if value is not None)
            yield from self._numeric_column_candidates(
                f"arg-{index}", variable, numeric, variable.sort().is_int()
            )

        strings = tuple(_as_string(value) for value in values)
        if all(value is not None for value in strings):
            concrete = tuple(value for value in strings if value is not None)
            if len(set(concrete)) == 1:
                yield (
                    TraceTemplateId.STRING_CONSTANT,
                    f"string-{index}-constant",
                    variable == z3.StringVal(concrete[0]),
                )
            prefix = _common_prefix(concrete)
            if prefix:
                yield (
                    TraceTemplateId.STRING_COMMON_PREFIX,
                    f"string-{index}-prefix",
                    z3.PrefixOf(z3.StringVal(prefix), variable),
                )
            suffix = _common_suffix(concrete)
            if suffix:
                yield (
                    TraceTemplateId.STRING_COMMON_SUFFIX,
                    f"string-{index}-suffix",
                    z3.SuffixOf(z3.StringVal(suffix), variable),
                )
            alphabet = sorted({character for value in concrete for character in value})
            if 0 < len(alphabet) <= 16:
                regexes = [z3.Re(z3.StringVal(character)) for character in alphabet]
                alphabet_re = regexes[0]
                for regex in regexes[1:]:
                    alphabet_re = z3.Union(alphabet_re, regex)
                yield (
                    TraceTemplateId.STRING_ALPHABET_CLOSURE,
                    f"string-{index}-alphabet",
                    z3.InRe(variable, z3.Star(alphabet_re)),
                )
            # Leading-symbol alphabet: every sample is c · (Σ \ {c})*.
            # Stronger and much cheaper for the solver than a count-modulo
            # regex for a character that appears exactly once as a prefix
            # (e.g. MU-puzzle strings are M(I|U)*).
            if prefix and len(prefix) == 1 and 0 < len(alphabet) <= 16:
                lead = prefix[0]
                if all(value.count(lead) == 1 for value in concrete):
                    rest = [c for c in alphabet if c != lead]
                    if rest:
                        rest_re = z3.Re(z3.StringVal(rest[0]))
                        for c in rest[1:]:
                            rest_re = z3.Union(rest_re, z3.Re(z3.StringVal(c)))
                        lead_re = z3.Concat(
                            z3.Re(z3.StringVal(lead)), z3.Star(rest_re)
                        )
                        yield (
                            TraceTemplateId.STRING_ALPHABET_CLOSURE,
                            f"string-{index}-leading-{lead}-alphabet",
                            z3.InRe(variable, lead_re),
                        )

            # Character-count modulo templates (parity, mod-3, residue sets).
            # Only emit when the observed alphabet is small enough that the
            # resulting regex stays manageable. Prefer small moduli; higher
            # moduli are emitted only for binary alphabets where the regex
            # remains compact.
            #
            # Characters with a *constant* raw count across all samples are
            # skipped: a stack of M-count-mod-2/3/... regexes (always 1 M in
            # MU samples) makes induction checks unknown without adding
            # strength beyond prefix / leading-symbol patterns.
            if 0 < len(alphabet) <= 8:
                # m=2 (parity) and m=3 cover coffee-can / MU; higher moduli
                # only bloat the pool and make induction checks unknown.
                max_m = min(3, self.max_congruence_modulus)
                for char in alphabet:
                    counts = [value.count(char) for value in concrete]
                    if len(set(counts)) == 1:
                        continue
                    for modulus in range(2, max_m + 1):
                        residues = {count % modulus for count in counts}
                        if not residues:
                            continue
                        if len(residues) == 1:
                            residue = next(iter(residues))
                            regex = _char_count_mod_regex(
                                char, modulus, residue, alphabet
                            )
                            if regex is None:
                                continue
                            yield (
                                TraceTemplateId.STRING_CHAR_COUNT_MODULO,
                                f"string-{index}-count-{char}-mod-{modulus}-{residue}",
                                z3.InRe(variable, regex),
                            )
                            continue
                        # Proper subset with multiple residues (e.g. #I ≢ 0 mod 3).
                        if len(residues) >= modulus:
                            continue
                        # Prefer classic "avoid residue 0" / almost-full sets.
                        if 0 in residues and len(residues) < modulus - 1:
                            continue
                        set_re = _char_count_mod_set_regex(
                            char, modulus, residues, alphabet
                        )
                        if set_re is None:
                            continue
                        residue_label = "-".join(
                            str(r) for r in sorted(residues)
                        )
                        yield (
                            TraceTemplateId.STRING_CHAR_COUNT_MODULO_SET,
                            f"string-{index}-count-{char}-mod-{modulus}-in-{residue_label}",
                            z3.InRe(variable, set_re),
                        )

    def _numeric_features(
        self,
        canonical: tuple[z3.ExprRef, ...],
        columns: tuple[tuple[z3.ExprRef, ...], ...],
    ) -> tuple[_Feature, ...]:
        features: list[_Feature] = []
        for index, (variable, values) in enumerate(
            zip(canonical, columns, strict=True)
        ):
            fractions = tuple(_as_fraction(value) for value in values)
            if all(value is not None for value in fractions):
                features.append(
                    _Feature(
                        expression=variable,
                        values=tuple(value for value in fractions if value is not None),
                        integral=variable.sort().is_int(),
                        label=f"arg-{index}",
                    )
                )
                continue
            strings = tuple(_as_string(value) for value in values)
            if all(value is not None for value in strings):
                features.append(
                    _Feature(
                        expression=z3.Length(variable),
                        values=tuple(
                            Fraction(len(value))
                            for value in strings
                            if value is not None
                        ),
                        integral=True,
                        label=f"len-{index}",
                    )
                )
        return tuple(features)

    def _numeric_relations(
        self, features: tuple[_Feature, ...]
    ) -> Iterable[tuple[TraceTemplateId, str, z3.BoolRef]]:
        for feature in features:
            yield from self._numeric_column_candidates(
                feature.label,
                feature.expression,
                feature.values,
                feature.integral,
            )

        for left_index in range(len(features)):
            for right_index in range(left_index + 1, len(features)):
                left = features[left_index]
                right = features[right_index]
                differences = tuple(
                    left_value - right_value
                    for left_value, right_value in zip(
                        left.values, right.values, strict=True
                    )
                )
                expression = left.expression - right.expression
                yield from self._numeric_column_candidates(
                    f"difference-{left.label}-{right.label}",
                    expression,
                    differences,
                    left.integral and right.integral,
                )

        if len(features) >= 2 and len(features[0].values) >= 2 and len(features) <= 8:
            matrix = [
                [feature.values[row] for feature in features] + [Fraction(1)]
                for row in range(len(features[0].values))
            ]
            for vector in _nullspace(matrix):
                integer_vector = _normalize_coefficients(vector)
                if integer_vector is None:
                    continue
                if max(abs(item) for item in integer_vector) > self.max_affine_coefficient:
                    continue
                terms: list[z3.ArithRef] = []
                for coefficient, feature in zip(
                    integer_vector[:-1], features, strict=True
                ):
                    if coefficient:
                        terms.append(coefficient * feature.expression)
                constant = integer_vector[-1]
                if constant:
                    terms.append(z3.IntVal(constant))
                if not terms:
                    continue
                affine = terms[0]
                for term in terms[1:]:
                    affine = affine + term
                yield (TraceTemplateId.AFFINE_EQUALITY, "affine-equality", affine == 0)

    def _numeric_column_candidates(
        self,
        label: str,
        expression: z3.ArithRef,
        values: tuple[Fraction, ...],
        integral: bool,
    ) -> Iterable[tuple[TraceTemplateId, str, z3.BoolRef]]:
        minimum = min(values)
        maximum = max(values)
        if minimum == maximum:
            yield (
                TraceTemplateId.NUMERIC_CONSTANT,
                f"{label}-constant",
                expression == _numeric_value(minimum, integral),
            )
        else:
            yield (
                TraceTemplateId.NUMERIC_LOWER_BOUND,
                f"{label}-lower",
                expression >= _numeric_value(minimum, integral),
            )
            yield (
                TraceTemplateId.NUMERIC_UPPER_BOUND,
                f"{label}-upper",
                expression <= _numeric_value(maximum, integral),
            )
        if integral and all(value.denominator == 1 for value in values):
            integers = tuple(value.numerator for value in values)
            for modulus in range(2, self.max_congruence_modulus + 1):
                residues = {value % modulus for value in integers}
                if len(residues) == 1:
                    residue = next(iter(residues))
                    yield (
                        TraceTemplateId.INTEGER_CONGRUENCE,
                        f"{label}-mod-{modulus}",
                        expression % modulus == residue,
                    )

    def _string_relations(
        self,
        canonical: tuple[z3.ExprRef, ...],
        columns: tuple[tuple[z3.ExprRef, ...], ...],
    ) -> Iterable[tuple[TraceTemplateId, str, z3.BoolRef]]:
        string_columns: list[tuple[int, z3.SeqRef, tuple[str, ...]]] = []
        for index, (variable, values) in enumerate(
            zip(canonical, columns, strict=True)
        ):
            strings = tuple(_as_string(value) for value in values)
            if all(value is not None for value in strings):
                string_columns.append(
                    (
                        index,
                        variable,
                        tuple(value for value in strings if value is not None),
                    )
                )
        for left_index in range(len(string_columns)):
            li, left_expr, left_values = string_columns[left_index]
            for right_index in range(left_index + 1, len(string_columns)):
                ri, right_expr, right_values = string_columns[right_index]
                if all(
                    left == right
                    for left, right in zip(left_values, right_values, strict=True)
                ):
                    yield (
                        TraceTemplateId.STRING_EQUALITY,
                        f"string-equality-{li}-{ri}",
                        left_expr == right_expr,
                    )
                if all(
                    left.startswith(right)
                    for left, right in zip(left_values, right_values, strict=True)
                ):
                    yield (
                        TraceTemplateId.STRING_PREFIX_RELATION,
                        f"string-prefix-{ri}-{li}",
                        z3.PrefixOf(right_expr, left_expr),
                    )
                if all(
                    left.endswith(right)
                    for left, right in zip(left_values, right_values, strict=True)
                ):
                    yield (
                        TraceTemplateId.STRING_SUFFIX_RELATION,
                        f"string-suffix-{ri}-{li}",
                        z3.SuffixOf(right_expr, left_expr),
                    )
                if all(
                    right.startswith(left)
                    for left, right in zip(left_values, right_values, strict=True)
                ):
                    yield (
                        TraceTemplateId.STRING_PREFIX_RELATION,
                        f"string-prefix-{li}-{ri}",
                        z3.PrefixOf(left_expr, right_expr),
                    )
                if all(
                    right.endswith(left)
                    for left, right in zip(left_values, right_values, strict=True)
                ):
                    yield (
                        TraceTemplateId.STRING_SUFFIX_RELATION,
                        f"string-suffix-{li}-{ri}",
                        z3.SuffixOf(left_expr, right_expr),
                    )

        if len(string_columns) <= 5:
            for target, left, right in permutations(string_columns, 3):
                ti, target_expr, target_values = target
                li, left_expr, left_values = left
                ri, right_expr, right_values = right
                if all(
                    target_value == left_value + right_value
                    for target_value, left_value, right_value in zip(
                        target_values, left_values, right_values, strict=True
                    )
                ):
                    yield (
                        TraceTemplateId.STRING_CONCATENATION,
                        f"string-concat-{ti}-{li}-{ri}",
                        target_expr == z3.Concat(left_expr, right_expr),
                    )


def merge_candidate_maps(
    variables: VariableMap,
    *candidate_maps: Mapping[z3.FuncDeclRef, Iterable[z3.BoolRef]],
) -> CandidateMap:
    """Deduplicate candidate sources using their canonical SMT representation."""

    merged: CandidateMap = {}
    for relation in variables:
        bucket: dict[str, z3.BoolRef] = {}
        for candidate_map in candidate_maps:
            for candidate in candidate_map.get(relation, ()):
                normalized = z3.simplify(candidate)
                bucket.setdefault(normalized.sexpr(), normalized)
        merged[relation] = tuple(
            expression
            for _, expression in sorted(bucket.items(), key=lambda item: item[0])
        )
    return merged


def _as_fraction(value: z3.ExprRef) -> Fraction | None:
    if z3.is_int_value(value):
        return Fraction(value.as_long())
    if z3.is_rational_value(value):
        return Fraction(value.numerator_as_long(), value.denominator_as_long())
    return None


def _as_string(value: z3.ExprRef) -> str | None:
    if z3.is_string_value(value):
        return value.as_string()
    return None


def _numeric_value(value: Fraction, integral: bool) -> z3.ArithRef:
    if integral:
        if value.denominator != 1:
            raise ValueError("integral feature received a non-integral value")
        return z3.IntVal(value.numerator)
    return z3.RealVal(f"{value.numerator}/{value.denominator}")


def _common_prefix(values: tuple[str, ...]) -> str:
    if not values:
        return ""
    prefix = values[0]
    for value in values[1:]:
        while prefix and not value.startswith(prefix):
            prefix = prefix[:-1]
        if not prefix:
            break
    return prefix


def _common_suffix(values: tuple[str, ...]) -> str:
    reversed_values = tuple(value[::-1] for value in values)
    return _common_prefix(reversed_values)[::-1]


def _char_count_mod_regex(
    char: str,
    modulus: int,
    residue: int,
    alphabet: list[str],
) -> z3.ReRef | None:
    """Build a regex accepting strings over ``alphabet`` whose count of
    ``char`` is congruent to ``residue`` modulo ``modulus``.

    Uses the standard m-state counting DFA and converts it to a regular
    expression by state elimination. Returns ``None`` when the construction
    is refused (empty alphabet, invalid residue, or modulus out of range).
    """
    if modulus < 2 or not (0 <= residue < modulus) or not alphabet:
        return None
    if char not in alphabet:
        return None

    # Symbols that do not change the count.
    others = [c for c in alphabet if c != char]
    char_re = z3.Re(z3.StringVal(char))
    if others:
        other_res = [z3.Re(z3.StringVal(c)) for c in others]
        other_re = other_res[0]
        for re in other_res[1:]:
            other_re = z3.Union(other_re, re)
        # Stay-transition: zero or more non-counted symbols.
        stay = z3.Star(other_re)
    else:
        # Alphabet is {char} only; stay is empty string.
        stay = z3.Re(z3.StringVal(""))

    # Special-case the common and most useful instances with compact regexes.
    # Odd count of ``char`` over a binary alphabet (coffee-can).
    if modulus == 2 and residue == 1 and others:
        # (others)* char ( (others)* char (others)* char )* (others)*
        # i.e. odd number of char.
        return z3.Concat(
            stay,
            char_re,
            z3.Star(z3.Concat(stay, char_re, stay, char_re)),
            stay,
        )
    # Even count (including zero).
    if modulus == 2 and residue == 0 and others:
        # ( (others)* char (others)* char )* (others)*
        return z3.Concat(
            z3.Star(z3.Concat(stay, char_re, stay, char_re)),
            stay,
        )
    def _repeat(unit: z3.ReRef, times: int) -> z3.ReRef:
        """Concatenate ``unit`` with itself ``times`` times (times >= 1)."""
        result = unit
        for _ in range(times - 1):
            result = z3.Concat(result, unit)
        return result

    # Pure powers of a single character.
    if not others:
        # char^k where k ≡ residue (mod modulus)
        # (char^modulus)* char^residue
        if residue == 0:
            return z3.Star(_repeat(char_re, modulus))
        prefix = char_re if residue == 1 else _repeat(char_re, residue)
        cycle = _repeat(char_re, modulus)
        return z3.Concat(z3.Star(cycle), prefix)

    # General small-modulus construction via a loop of "blocks".
    # Language: strings whose number of ``char`` ≡ residue (mod m).
    # Regex shape:
    #   stay (char stay)^{residue} ( (char stay)^{modulus} )*
    # which is correct when the alphabet is partitioned into {char} ∪ others.
    step = z3.Concat(char_re, stay)
    if residue == 0:
        block = _repeat(step, modulus)
        return z3.Concat(stay, z3.Star(block))
    head = step if residue == 1 else _repeat(step, residue)
    block = _repeat(step, modulus)
    return z3.Concat(stay, head, z3.Star(block))


def _char_count_mod_set_regex(
    char: str,
    modulus: int,
    residues: set[int],
    alphabet: list[str],
) -> z3.ReRef | None:
    """Regex for count(char) mod modulus ∈ residues over ``alphabet``.

    Builds a single compact expression from the counting DFA rather than a
    naive union of full single-residue regexes, which helps the string solver
    on induction checks (e.g. MU-puzzle doubling).
    """
    if modulus < 2 or not alphabet or not residues:
        return None
    if char not in alphabet:
        return None
    if any(r < 0 or r >= modulus for r in residues):
        return None
    # Full set = alphabet closure; not useful as a modulo invariant.
    if len(residues) >= modulus:
        return None

    others = [c for c in alphabet if c != char]
    char_re = z3.Re(z3.StringVal(char))
    if others:
        other_re = z3.Re(z3.StringVal(others[0]))
        for c in others[1:]:
            other_re = z3.Union(other_re, z3.Re(z3.StringVal(c)))
        stay = z3.Star(other_re)
    else:
        stay = z3.Re(z3.StringVal(""))

    def _repeat(unit: z3.ReRef, times: int) -> z3.ReRef:
        result = unit
        for _ in range(times - 1):
            result = z3.Concat(result, unit)
        return result

    step = z3.Concat(char_re, stay)
    cycle = _repeat(step, modulus) if modulus > 1 else step

    # Special case: all nonzero residues (count ≢ 0 mod m) — one compact form.
    nonzero = set(range(1, modulus))
    if residues == nonzero:
        # stay · step · (step^{m})* · (ε ∪ step ∪ ... ∪ step^{m-2})
        # i.e. at least one counted char, residue in 1..m-1.
        if modulus == 2:
            # Odd: stay char (stay char stay char)* stay
            return z3.Concat(
                stay, char_re, z3.Star(z3.Concat(stay, char_re, stay, char_re)), stay
            )
        # After first step (res 1), any number of full cycles, then optional
        # extra 0..m-2 steps (still avoiding 0).
        tails: list[z3.ReRef] = [z3.Re(z3.StringVal(""))]  # +0 steps
        for k in range(1, modulus - 1):
            tails.append(_repeat(step, k))
        tail_union = tails[0]
        for t in tails[1:]:
            tail_union = z3.Union(tail_union, t)
        return z3.Concat(stay, step, z3.Star(cycle), tail_union)

    # General: union over r in residues of stay · step^r · cycle* (r>0),
    # and stay · cycle* for r=0.
    parts: list[z3.ReRef] = []
    for r in sorted(residues):
        if r == 0:
            parts.append(z3.Concat(stay, z3.Star(cycle)))
        else:
            head = step if r == 1 else _repeat(step, r)
            parts.append(z3.Concat(stay, head, z3.Star(cycle)))
    if not parts:
        return None
    result = parts[0]
    for p in parts[1:]:
        result = z3.Union(result, p)
    return result


def _nullspace(matrix: list[list[Fraction]]) -> tuple[tuple[Fraction, ...], ...]:
    """Return a rational basis for the nullspace of ``matrix``."""

    if not matrix:
        return ()
    rows = [row[:] for row in matrix]
    row_count = len(rows)
    column_count = len(rows[0])
    pivot_columns: list[int] = []
    pivot_row = 0
    for column in range(column_count):
        selected = next(
            (row for row in range(pivot_row, row_count) if rows[row][column]),
            None,
        )
        if selected is None:
            continue
        rows[pivot_row], rows[selected] = rows[selected], rows[pivot_row]
        pivot = rows[pivot_row][column]
        rows[pivot_row] = [value / pivot for value in rows[pivot_row]]
        for row in range(row_count):
            if row == pivot_row or not rows[row][column]:
                continue
            factor = rows[row][column]
            rows[row] = [
                value - factor * pivot_value
                for value, pivot_value in zip(
                    rows[row], rows[pivot_row], strict=True
                )
            ]
        pivot_columns.append(column)
        pivot_row += 1
        if pivot_row == row_count:
            break

    free_columns = [
        column for column in range(column_count) if column not in pivot_columns
    ]
    basis: list[tuple[Fraction, ...]] = []
    for free in free_columns:
        vector = [Fraction(0) for _ in range(column_count)]
        vector[free] = Fraction(1)
        for row, pivot in reversed(list(enumerate(pivot_columns))):
            vector[pivot] = -sum(
                rows[row][column] * vector[column]
                for column in free_columns
            )
        basis.append(tuple(vector))
    return tuple(basis)


def _normalize_coefficients(
    vector: tuple[Fraction, ...],
) -> tuple[int, ...] | None:
    if not any(vector):
        return None
    denominator_lcm = 1
    for value in vector:
        denominator_lcm = lcm(denominator_lcm, value.denominator)
    integers = [value.numerator * (denominator_lcm // value.denominator) for value in vector]
    common = 0
    for value in integers:
        common = gcd(common, abs(value))
    if common:
        integers = [value // common for value in integers]
    first = next((value for value in integers if value), 0)
    if first < 0:
        integers = [-value for value in integers]
    return tuple(integers)
