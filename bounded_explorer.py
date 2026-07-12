#!/usr/bin/env python3
"""Run the standalone bounded CHC explorer without installing the package."""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent / "src"))

from pyhorn_bnd.cli import main  # noqa: E402

raise SystemExit(main())
