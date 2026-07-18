#!/usr/bin/env python3
"""Parse every SMT-LIB file in a CHC corpus and report all failures."""

from __future__ import annotations

import argparse
from pathlib import Path

from pyhorn_bnd import parse_chc_file


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path, help="directory containing *.smt2")
    parser.add_argument(
        "--manifest",
        type=Path,
        help="optional newline-separated list of files that must be present",
    )
    return parser


def _well_typed(program) -> None:
    for rule in program.rules:
        if rule.src_relation is not None:
            if len(rule.src_args) != rule.src_relation.arity():
                raise ValueError(f"{rule.short()}: source arity mismatch")
            for index, argument in enumerate(rule.src_args):
                if not argument.sort().eq(rule.src_relation.domain(index)):
                    raise ValueError(f"{rule.short()}: source sort mismatch at {index}")
        elif rule.src_args:
            raise ValueError(f"{rule.short()}: ENTRY rule has source arguments")

        if len(rule.dst_args) != rule.dst_relation.arity():
            raise ValueError(f"{rule.short()}: destination arity mismatch")
        for index, argument in enumerate(rule.dst_args):
            if not argument.sort().eq(rule.dst_relation.domain(index)):
                raise ValueError(
                    f"{rule.short()}: destination sort mismatch at {index}"
                )


def main() -> int:
    args = _parser().parse_args()
    if not args.directory.is_dir():
        print(f"not a directory: {args.directory}")
        return 2

    files = sorted(args.directory.glob("*.smt2"))
    if not files:
        print(f"no .smt2 files found in {args.directory}")
        return 2

    if args.manifest is not None:
        expected = {
            line.strip()
            for line in args.manifest.read_text(encoding="utf-8").splitlines()
            if line.strip()
        }
        actual = {path.name for path in files}
        missing = sorted(expected - actual)
        if missing:
            print("missing manifest files:")
            for name in missing:
                print(f"  {name}")
            return 1

    failures: list[str] = []
    total_rules = 0
    for path in files:
        try:
            program = parse_chc_file(path, slice_program=False)
            _well_typed(program)
            total_rules += len(program.rules)
        except Exception as exc:
            failures.append(f"{path.name}: {type(exc).__name__}: {exc}")

    if failures:
        print(f"parsed {len(files) - len(failures)}/{len(files)} files")
        for failure in failures:
            print(failure)
        return 1

    print(f"parsed {len(files)}/{len(files)} files ({total_rules} normalized rules)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
