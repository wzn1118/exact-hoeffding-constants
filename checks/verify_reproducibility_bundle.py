#!/usr/bin/env python3
"""Verify an extracted complete reproducibility bundle without Git metadata."""
from __future__ import annotations

import hashlib
import os
from pathlib import Path, PurePosixPath
import re
from current_publication_fingerprints import validate_pdf_fingerprints

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "SHA256SUMS.txt"
CURRENT_SOURCE = ROOT / "submission/current/manuscript.tex"


def fail(message: str) -> None:
    raise SystemExit("FAIL: " + message)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    if not CURRENT_SOURCE.is_file() or not (ROOT / "README.txt").is_file():
        fail("run this checker from the extracted bundle root")
    if not MANIFEST.is_file():
        fail("SHA256SUMS.txt is missing")
    expected: dict[str, str] = {}
    for number, line in enumerate(MANIFEST.read_text(encoding="utf-8").splitlines(), 1):
        match = re.fullmatch(r"([0-9a-f]{64})  (.+)", line)
        if not match:
            fail(f"malformed checksum row {number}")
        digest, name = match.groups()
        relative = PurePosixPath(name)
        if relative.is_absolute() or ".." in relative.parts or name in expected:
            fail(f"unsafe or duplicate manifest path on row {number}")
        expected[name] = digest
    generated_suffixes = {".aux", ".fdb_latexmk", ".fls", ".log", ".out", ".toc", ".synctex.gz"}
    generated_roots = {"submission/integrated/combined_manuscript.tex",
                       "submission/integrated/combined_manuscript.pdf"}
    actual_files = set()
    # Prune only the archive-root Lake cache; do not traverse Mathlib's many
    # generated files on subsequent runs. All distributed files remain hashed.
    for directory, subdirs, filenames in os.walk(ROOT):
        parent = Path(directory)
        subdirs[:] = [name for name in subdirs
                      if name != "__pycache__" and not (parent == ROOT and name == ".lake")]
        for name in filenames:
            path = parent / name
            if path == MANIFEST or path.suffix == ".pyc":
                continue
            relative = path.relative_to(ROOT).as_posix()
            in_build_dir = relative.startswith("submission/integrated/")
            if relative in generated_roots or (in_build_dir and any(path.name.endswith(ext) for ext in generated_suffixes)):
                continue
            actual_files.add(relative)
    if actual_files != set(expected):
        fail("checksum manifest does not enumerate exactly the extracted file set; "
             f"missing={sorted(set(expected) - actual_files)}, "
             f"unlisted={sorted(actual_files - set(expected))}")
    for name, digest in expected.items():
        path = ROOT.joinpath(*PurePosixPath(name).parts)
        if not path.is_file() or sha(path) != digest:
            fail(f"checksum mismatch: {name}")
    source_hash = sha(CURRENT_SOURCE)
    inventory_path = ROOT / "submission/current/display_formula_inventory.json"
    binding_path = ROOT / "submission/current/display_formula_review_bindings.json"
    concordance = ROOT / "submission/current/theorem_lean_concordance.md"
    manifest = ROOT / "submission/current/theorem_lean_manifest.json"
    for path in (inventory_path, binding_path, concordance, manifest,
                 ROOT / "lean-toolchain", ROOT / "lakefile.toml", ROOT / "lake-manifest.json"):
        if not path.is_file():
            fail(f"required current-source or Lean input is missing: {path.relative_to(ROOT)}")
    for obsolete in ("run_all.sh", "build_manuscript.sh", "checks/validate_package.py",
                     "checks/package_submission.py", "checks/package_research.py",
                     "checks/sync_submission.py", "checks/refresh_checksums.py",
                     "checks/check_baseline_protection.py", "checks/build_current_release.py",
                     "goal_b/build.sh", "checks/write_test_report.py", "checks/plot_piecewise_kl.py",
                     "checks/test_reproducibility_bundle.py"):
        if (ROOT / obsolete).exists():
            fail(f"legacy release entrypoint was included in the current bundle: {obsolete}")
    for readme in (ROOT / "README.txt", ROOT / "submission/current/README.md"):
        if not readme.is_file():
            fail(f"missing bundle instructions: {readme.relative_to(ROOT)}")
    pdf_path = ROOT / "submission/current/manuscript.pdf"
    if not pdf_path.read_bytes().startswith(b"%PDF-"):
        fail("current manuscript PDF is missing or invalid")
    try:
        validate_pdf_fingerprints(ROOT, sha(pdf_path))
    except ValueError as error:
        fail(str(error))
    print("PASS: current PDF fingerprints agree in all four audit records")
    print(f"PASS: {len(expected)} extracted files match SHA256SUMS.txt (no Git metadata required)")
    print(f"PASS: current paper source SHA-256 {source_hash}")


if __name__ == "__main__":
    main()
