#!/usr/bin/env python3
"""Compare syntactic Seed-Houdini with bounded trace generalization."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from pyhorn_bnd import (
    HoudiniStatus,
    parse_chc_file,
    run_seed_houdini,
    run_trace_houdini,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("directory", type=Path)
    parser.add_argument("--depth", type=int, default=4)
    parser.add_argument("--limit", type=int, default=50)
    parser.add_argument("--models-per-prefix", type=int, default=1)
    parser.add_argument("--timeout-ms", type=int, default=300)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()

    report = {
        "files": 0,
        "seed_success": 0,
        "trace_success": 0,
        "improved": [],
        "regressed": [],
        "errors": [],
    }
    for path in sorted(args.directory.glob("*.smt2")):
        report["files"] += 1
        try:
            program = parse_chc_file(path, slice_program=False)
            seed = run_seed_houdini(
                program, timeout_ms=args.timeout_ms, random_seed=1
            )
            trace = run_trace_houdini(
                program,
                trace_depth=args.depth,
                trace_limit=args.limit,
                models_per_prefix=args.models_per_prefix,
                timeout_ms=args.timeout_ms,
                random_seed=1,
            )
            seed_ok = seed.status is HoudiniStatus.SUCCESS
            trace_ok = trace.status is HoudiniStatus.SUCCESS
            report["seed_success"] += int(seed_ok)
            report["trace_success"] += int(trace_ok)
            if not seed_ok and trace_ok:
                report["improved"].append(path.name)
            if seed_ok and not trace_ok:
                report["regressed"].append(path.name)
        # Must survive any single-file failure to keep scanning the
        # rest of the corpus.
        except Exception as exc:  # noqa: BLE001
            report["errors"].append(
                {"file": path.name, "error": f"{type(exc).__name__}: {exc}"}
            )

    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(
            f"files={report['files']} seed-success={report['seed_success']} "
            f"trace-success={report['trace_success']} "
            f"improved={len(report['improved'])} "
            f"regressed={len(report['regressed'])} "
            f"errors={len(report['errors'])}"
        )
        for name in report["improved"]:
            print(f"  + {name}")
        for name in report["regressed"]:
            print(f"  - {name}")
    return 0 if not report["errors"] and not report["regressed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
