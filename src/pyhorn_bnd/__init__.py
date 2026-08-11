"""Python/Z3 bounded exploration, seed-Houdini, and trace-guided Houdini
analysis for linear CHCs."""

from importlib.metadata import PackageNotFoundError, version

try:
    __version__ = version("pyhorn-bounded-explorer")
except PackageNotFoundError:
    __version__ = "0.0.18"

from .candidate_generation import (
    CandidateBatch,
    CandidateGenerator,
    merge_candidate_batches,
)
from .candidate_validation import (
    DEFAULT_CANDIDATE_BOUND,
    CandidateReachability,
    CandidateValidation,
    validate_candidate_reachability,
    validate_removed_candidate,
)
from .cands import format_candidates_smt2, merge_candidate_maps, parse_candidate_file
from .explorer import (
    BoundedExplorer,
    CheckStatus,
    DepthStatistics,
    ExplorationResult,
    ExplorationStatus,
    TraceCheck,
)
from .horn import (
    ArithmeticSortProfile,
    HornParseError,
    HornProgram,
    HornRule,
    StringSortProfile,
    parse_chc_file,
)
from .houdini import (
    HoudiniFailure,
    HoudiniResult,
    HoudiniStatistics,
    HoudiniStatus,
    MultiHoudini,
    RemovedCandidate,
    run_seed_houdini,
    run_trace_houdini,
)
from .normalize import HornNormalizationError
from .seedminer import (
    CandidateMap,
    MutationResult,
    MutationStatistics,
    SeedMiner,
    SeedMiningResult,
    SeedMiningStatistics,
    SeedObservation,
    VariableMap,
    mutate_candidates,
)
from .solver_pool import (
    DEFAULT_MAX_SOLVERS,
    FreshTraceSolver,
    IncrementalSolverPool,
    SolverPoolCheck,
    SolverPoolStatistics,
)

# Note: trace_miner also defines a `merge_candidate_maps`, but it is
# superseded by `merge_candidate_batches` above (which every caller in this
# codebase actually uses) and is deliberately NOT re-exported here, since
# that name is already the public, load-bearing merge used by --cands /
# --seed-houdini combination (see cands.merge_candidate_maps above). Import
# it directly from `pyhorn_bnd.trace_miner` if you need it.
from .trace_miner import (
    DEFAULT_MAX_AFFINE_COEFFICIENT,
    DEFAULT_MAX_CONGRUENCE_MODULUS,
    DEFAULT_MODELS_PER_PREFIX,
    DEFAULT_SAMPLES_PER_RELATION,
    DEFAULT_TRACE_CANDIDATES_PER_RELATION,
    DEFAULT_TRACE_DEPTH,
    DEFAULT_TRACE_LIMIT,
    TraceCandidateMiner,
    TraceCandidateObservation,
    TraceMiningResult,
    TraceMiningStatistics,
    TraceStateSample,
    TraceTemplateId,
    TraceTemplateSpecification,
    trace_template_specifications,
)
from .vc import (
    DEFAULT_MAX_SSA_CACHE_STEPS,
    BndExplSmtDumpBuilder,
    SSAConstructionStatistics,
    StateVersion,
    VCStep,
    VerificationCondition,
    VerificationConditionBuilder,
    build_verification_condition,
)

__all__ = [
    "DEFAULT_CANDIDATE_BOUND",
    "DEFAULT_MAX_AFFINE_COEFFICIENT",
    "DEFAULT_MAX_CONGRUENCE_MODULUS",
    "DEFAULT_MAX_SOLVERS",
    "DEFAULT_MAX_SSA_CACHE_STEPS",
    "DEFAULT_MODELS_PER_PREFIX",
    "DEFAULT_SAMPLES_PER_RELATION",
    "DEFAULT_TRACE_CANDIDATES_PER_RELATION",
    "DEFAULT_TRACE_DEPTH",
    "DEFAULT_TRACE_LIMIT",
    "ArithmeticSortProfile",
    "BndExplSmtDumpBuilder",
    "BoundedExplorer",
    "CandidateBatch",
    "CandidateGenerator",
    "CandidateMap",
    "CandidateReachability",
    "CandidateValidation",
    "CheckStatus",
    "DepthStatistics",
    "ExplorationResult",
    "ExplorationStatus",
    "FreshTraceSolver",
    "HornNormalizationError",
    "HornParseError",
    "HornProgram",
    "HornRule",
    "HoudiniFailure",
    "HoudiniResult",
    "HoudiniStatistics",
    "HoudiniStatus",
    "IncrementalSolverPool",
    "MultiHoudini",
    "MutationResult",
    "MutationStatistics",
    "RemovedCandidate",
    "SSAConstructionStatistics",
    "SeedMiner",
    "SeedMiningResult",
    "SeedMiningStatistics",
    "SeedObservation",
    "SolverPoolCheck",
    "SolverPoolStatistics",
    "StateVersion",
    "StringSortProfile",
    "TraceCandidateMiner",
    "TraceCandidateObservation",
    "TraceCheck",
    "TraceMiningResult",
    "TraceMiningStatistics",
    "TraceStateSample",
    "TraceTemplateId",
    "TraceTemplateSpecification",
    "VCStep",
    "VariableMap",
    "VerificationCondition",
    "VerificationConditionBuilder",
    "__version__",
    "build_verification_condition",
    "format_candidates_smt2",
    "merge_candidate_batches",
    "merge_candidate_maps",
    "mutate_candidates",
    "parse_candidate_file",
    "parse_chc_file",
    "run_seed_houdini",
    "run_trace_houdini",
    "trace_template_specifications",
    "validate_candidate_reachability",
    "validate_removed_candidate",
]
