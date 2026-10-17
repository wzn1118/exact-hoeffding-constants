#!/usr/bin/env python3
"""Check frozen manuscript/declaration bindings; --check-live also inspects Lean."""
import sys
from export_theorem_manifest import main

if __name__ == "__main__":
    if "--check-live" not in sys.argv:
        sys.argv.append("--check")
    raise SystemExit(main())
