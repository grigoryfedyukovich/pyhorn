#!/usr/bin/env python3
"""Parse and run Seed-Houdini over the three original FreqHorn suites."""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

SUITES = ("bench_horn", "bench_horn_cex", "bench_horn_multiple")


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "freqhorn_root",
        type=Path,
        help="FreqHorn repository root containing benchmark directories",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=1_000,
        metavar="MS",
        help="per-check Z3 timeout in milliseconds (default: 1000)",
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
        help="emit complete machine-readable results",
    )
    return parser


def _run_suite_process(
    repository_root: Path,
    directory: Path,
    *,
    timeout_ms: int,
    random_seed: int,
) -> dict[str, object]:
    """Run each suite in a fresh process to bound Z3-context growth."""

    script = repository_root / "tools" / "check_seed_houdini_corpus.py"
    env = os.environ.copy()
    src = str(repository_root / "src")
    existing = env.get("PYTHONPATH")
    env["PYTHONPATH"] = src if not existing else src + os.pathsep + existing
    completed = subprocess.run(
        [
            sys.executable,
            str(script),
            str(directory),
            "--timeout",
            str(timeout_ms),
            "--random-seed",
            str(random_seed),
            "--json",
        ],
        cwd=repository_root,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    try:
        payload = json.loads(completed.stdout)
    except json.JSONDecodeError as exc:
        raise RuntimeError(
            f"suite process for {directory.name} produced invalid JSON; "
            f"exit={completed.returncode}, stderr={completed.stderr.strip()}"
        ) from exc
    payload["process_exit_code"] = completed.returncode
    if completed.stderr.strip():
        payload["process_stderr"] = completed.stderr.strip()
    return payload


def main() -> int:
    args = _parser().parse_args()
    if args.timeout < 0:
        print("--timeout must be non-negative")
        return 2

    missing = [
        suite for suite in SUITES if not (args.freqhorn_root / suite).is_dir()
    ]
    if missing:
        print("missing benchmark directories: " + ", ".join(missing))
        return 2

    repository_root = Path(__file__).resolve().parents[1]
    suites = {
        suite: _run_suite_process(
            repository_root,
            args.freqhorn_root / suite,
            timeout_ms=args.timeout,
            random_seed=args.random_seed,
        )
        for suite in SUITES
    }

    unsafe_successes = [
        row["file"]
        for row in suites["bench_horn_cex"]["results"]
        if row["status"] == "success"
    ]
    payload = {
        "configuration": {
            "timeout_ms": args.timeout,
            "random_seed": args.random_seed,
            "suite_process_isolation": True,
        },
        "suites": suites,
        "soundness_guard": {
            "known_counterexample_successes": unsafe_successes,
            "passed": not unsafe_successes,
        },
    }

    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        for suite in SUITES:
            summary = suites[suite]["summary"]
            print(
                f"{suite}: files={summary['files']}, "
                f"success={summary['success']}, unknown={summary['unknown']}, "
                f"errors={summary['errors']}, elapsed={summary['elapsed_seconds']:.3f}s"
            )
        if unsafe_successes:
            print(
                "soundness guard FAILED; known counterexample files reported "
                "Success: " + ", ".join(unsafe_successes)
            )
        else:
            print("soundness guard passed: no bench_horn_cex file reported Success")

    any_errors = any(
        suites[suite]["summary"]["errors"] for suite in SUITES
    )
    process_failures = any(
        suites[suite]["process_exit_code"] not in (0, 1) for suite in SUITES
    )
    return 1 if any_errors or process_failures or unsafe_successes else 0


if __name__ == "__main__":
    raise SystemExit(main())
