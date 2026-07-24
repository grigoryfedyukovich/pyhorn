"""Python/Z3 bounded exploration and seed-Houdini analysis for linear CHCs."""

from importlib.metadata import PackageNotFoundError, version

try:
    __version__ = version("pyhorn-bounded-explorer")
except PackageNotFoundError:
    __version__ = "0.0.11"

from .explorer import (
    BoundedExplorer,
    CheckStatus,
    DepthStatistics,
    ExplorationResult,
    ExplorationStatus,
    TraceCheck,
)
from .horn import HornParseError, HornProgram, HornRule, parse_chc_file
from .houdini import (
    HoudiniFailure,
    HoudiniResult,
    HoudiniStatistics,
    HoudiniStatus,
    MultiHoudini,
    run_seed_houdini,
)
from .normalize import HornNormalizationError
from .seedminer import (
    CandidateMap,
    SeedMiner,
    SeedMiningResult,
    SeedMiningStatistics,
    SeedObservation,
    VariableMap,
)
from .solver_pool import (
    DEFAULT_MAX_SOLVERS,
    FreshTraceSolver,
    IncrementalSolverPool,
    SolverPoolCheck,
    SolverPoolStatistics,
)
from .vc import (
    BndExplSmtDumpBuilder,
    DEFAULT_MAX_SSA_CACHE_STEPS,
    SSAConstructionStatistics,
    StateVersion,
    VCStep,
    VerificationCondition,
    VerificationConditionBuilder,
    build_verification_condition,
)

__all__ = [
    "BndExplSmtDumpBuilder",
    "BoundedExplorer",
    "run_seed_houdini",
    "VariableMap",
    "SeedObservation",
    "SeedMiningStatistics",
    "SeedMiningResult",
    "SeedMiner",
    "MultiHoudini",
    "HoudiniStatus",
    "HoudiniStatistics",
    "HoudiniResult",
    "HoudiniFailure",
    "CandidateMap",
    "CheckStatus",
    "DEFAULT_MAX_SOLVERS",
    "DEFAULT_MAX_SSA_CACHE_STEPS",
    "DepthStatistics",
    "ExplorationResult",
    "ExplorationStatus",
    "HornNormalizationError",
    "HornParseError",
    "HornProgram",
    "HornRule",
    "FreshTraceSolver",
    "IncrementalSolverPool",
    "SSAConstructionStatistics",
    "SolverPoolCheck",
    "SolverPoolStatistics",
    "StateVersion",
    "TraceCheck",
    "VCStep",
    "VerificationCondition",
    "VerificationConditionBuilder",
    "build_verification_condition",
    "parse_chc_file",
    "__version__",
]
