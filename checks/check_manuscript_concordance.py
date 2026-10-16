#!/usr/bin/env python3
"""Compatibility entry point for the current theorem--Lean concordance.

The authoritative checker is ``check_full_manuscript_concordance.py``.  This
legacy command is retained because older CI jobs invoke this filename.
"""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
checker = ROOT / "checks/check_full_manuscript_concordance.py"
raise SystemExit(subprocess.call([sys.executable, str(checker)] + sys.argv[1:]))
