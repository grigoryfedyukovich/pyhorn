#!/usr/bin/env python3
"""Run SeedMiner and MultiHoudini over every SMT-LIB file in a directory."""

from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
from time import perf_counter

from pyhorn_bnd import HoudiniStatus, parse_chc_file, run_seed_houdini


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path, help="directory containing *.smt2")
    parser.add_argument(
        "--timeout",
        type=int,
        default=1_000,
        metavar="MS",
        help="timeout for each Z3 Houdini check in milliseconds (default: 1000)",
    )
    parser.add_argument(
        "--random-seed",
        type=int,
        default=1,
        help="Z3 random seed (default: 1)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit the complete per-file result as JSON",
    )
    return parser


def main() -> int:
    args = _parser().parse_args()
    if not args.directory.is_dir():
        print(f"not a directory: {args.directory}")
        return 2
    if args.timeout < 0:
        print("--timeout must be non-negative")
        return 2

    files = sorted(args.directory.glob("*.smt2"))
    if not files:
        print(f"no .smt2 files found in {args.directory}")
        return 2

    counts: Counter[str] = Counter()
    rows: list[dict[str, object]] = []
    totals = {
        "candidates_initial": 0,
        "candidates_removed": 0,
        "candidates_remaining": 0,
        "solver_checks": 0,
        "certification_checks": 0,
    }
    started = perf_counter()

    for path in files:
        row: dict[str, object] = {"file": path.name}
        try:
            program = parse_chc_file(path, slice_program=False)
            result = run_seed_houdini(
                program,
                timeout_ms=args.timeout,
                random_seed=args.random_seed,
            )
            status = result.status.value
            counts[status] += 1
            stats = result.statistics
            row.update(
                {
                    "status": status,
                    "candidates_initial": stats.candidates_initial,
                    "candidates_removed": stats.candidates_removed,
                    "candidates_remaining": stats.candidates_remaining,
                    "iterations": stats.iterations,
                    "solver_checks": stats.solver_checks,
                    "certification_checks": stats.certification_checks,
                    "failure": None
                    if not result.failures
                    else result.failures[0].reason,
                }
            )
            for key in totals:
                totals[key] += getattr(stats, key)
        except Exception as exc:  # report the entire corpus, not just first error
            counts["error"] += 1
            row.update(
                {
                    "status": "error",
                    "error": f"{type(exc).__name__}: {exc}",
                }
            )
        rows.append(row)

    elapsed = perf_counter() - started
    summary = {
        "files": len(files),
        "success": counts[HoudiniStatus.SUCCESS.value],
        "unknown": counts[HoudiniStatus.UNKNOWN.value],
        "errors": counts["error"],
        "elapsed_seconds": elapsed,
        **totals,
    }

    if args.json:
        print(json.dumps({"summary": summary, "results": rows}, indent=2))
    else:
        print(
            f"processed {summary['files']} files: "
            f"success={summary['success']}, unknown={summary['unknown']}, "
            f"errors={summary['errors']}"
        )
        print(
            "candidates: "
            f"initial={summary['candidates_initial']}, "
            f"removed={summary['candidates_removed']}, "
            f"remaining={summary['candidates_remaining']}"
        )
        print(
            f"solver checks={summary['solver_checks']}, "
            f"certification checks={summary['certification_checks']}, "
            f"elapsed={summary['elapsed_seconds']:.3f}s"
        )
        if counts["error"]:
            for row in rows:
                if row["status"] == "error":
                    print(f"{row['file']}: {row['error']}")

    return 1 if counts["error"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
