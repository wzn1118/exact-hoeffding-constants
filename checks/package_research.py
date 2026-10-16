#!/usr/bin/env python3
"""Package the full article, all project Lean source, pinned dependencies and literature."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import tempfile
from zipfile import ZipFile

from package_submission import DATE, PREFIX, ROOT, sha256, write_zip


def git(root: Path, *arguments: str) -> str:
    return subprocess.run(["git", "-C", str(root), *arguments], text=True, check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.strip()


def add(members: dict[str, bytes], formal: Path, path: Path) -> None:
    if path.is_file():
        members[path.relative_to(formal).as_posix()] = path.read_bytes()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--formal-root", type=Path, default=ROOT,
                        help="Integrated project root containing the final umbrella and audit")
    parser.add_argument("--publication-bundle", type=Path,
                        default=ROOT / "submission/release" / f"{PREFIX}_Publication_Bundle_{DATE}.zip")
    parser.add_argument("--output", type=Path, default=ROOT / "submission/release")
    args = parser.parse_args()
    formal = args.formal_root.resolve()
    publication = args.publication_bundle.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if not publication.is_file():
        raise SystemExit("First run python3 checks/package_submission.py")
    # Only the explicit publication payload is imported; no sibling or legacy archive is scanned.
    with ZipFile(publication) as archive:
        members = {name: archive.read(name) for name in archive.namelist() if name != "SHA256SUMS.txt"}
    for relative in ("source/manuscript.tex", "source/supplement.tex", "source/uniform_results.tex", "source/analytic_contraction.tex"):
        if (formal / relative).read_bytes() != members[relative]:
            raise SystemExit("Publication source differs from the integrated source: " + relative)
    files = [formal / "ExactHoeffding.lean", *sorted((formal / "ExactHoeffding").rglob("*.lean"))]
    for required in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "checks/generate_axiom_audit.py", "checks/check_axiom_output.py", "checks/full_closure_axioms.lean"):
        if not (formal / required).is_file():
            raise SystemExit("Required formal reproduction file missing: " + required)
    spec = importlib.util.spec_from_file_location("project_axiom_audit", formal / "checks/generate_axiom_audit.py")
    audit = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(audit)
    generated, theorems, modules = audit.generate()
    if (formal / "checks/full_closure_axioms.lean").read_text() != generated:
        raise SystemExit("Regenerate the integrated public-theorem audit before packaging")
    for path in files:
        source = audit.uncomment(path.read_text())
        if re.search(r"\b(?:sorry|admit|axiom)\b", source):
            raise SystemExit("Proof placeholder or axiom in " + str(path.relative_to(formal)))
        add(members, formal, path)
    for relative in ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "README_LEAN4.md", "LEAN_PROOF_STATUS.md", "proof_gap_register.md", "theorem_to_lean.csv", "requirements.txt", "run_all.sh", "build_manuscript.sh", "release_notes.md"):
        add(members, formal, formal / relative)
    for pattern in ("checks/*.py", "checks/*.sh", "checks/*.lean", "checks/logs/full_closure/*", "formal_status/*.md", "docs/*.md", "docs/*.tex", "docs/*.pdf", ".github/workflows/*.yml"):
        for path in sorted(formal.glob(pattern)):
            add(members, formal, path)
    # The archive remains reproducible even if its packager is run from a separate worktree.
    for name in ("package_research.py", "package_submission.py", "sync_submission.py"):
        members["checks/" + name] = (ROOT / "checks" / name).read_bytes()
    lock = json.loads((formal / "lake-manifest.json").read_text())
    mathlib = next(package for package in lock["packages"] if package["name"] == "mathlib")
    provenance = {"date": DATE, "project_commit": git(formal, "rev-parse", "HEAD"),
                  "project_branch": git(formal, "branch", "--show-current"),
                  "working_tree_status": git(formal, "status", "--porcelain").splitlines(),
                  "lean_toolchain": (formal / "lean-toolchain").read_text().strip(),
                  "mathlib_git": mathlib["url"], "mathlib_commit": mathlib["rev"],
                  "project_lean_source_files": len(files), "audited_public_theorems": theorems,
                  "umbrella_imported_project_modules": modules,
                  "publication_bundle_sha256": sha256(publication.read_bytes()),
                  "source_inventory_sha256": sha256("".join(f"{sha256(members[name])}  {name}\n" for name in sorted(members) if name.endswith(".lean")).encode()),
                  "verification": "Snapshot consistency, placeholder scan, audit-source regeneration, archive integrity and manifest checks. Kernel reproduction is performed by reproduce_formal.sh."}
    members["RESEARCH_PROVENANCE.json"] = (json.dumps(provenance, indent=2) + "\n").encode()
    members["reproduce_formal.sh"] = b'''#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build/formal
command -v lake >/dev/null || { printf 'Install elan and add it to PATH before running this script.\n' >&2; exit 1; }
lake exe cache get
lake build ExactHoeffding 2>&1 | tee build/formal/kernel_build.log
lake env lean ExactHoeffding.lean 2>&1 | tee build/formal/umbrella.log
python3 checks/generate_axiom_audit.py --check
python3 checks/check_manuscript_concordance.py
lake env lean checks/full_closure_axioms.lean 2>&1 | tee build/formal/axioms.log
python3 checks/check_axiom_output.py build/formal/axioms.log
'''
    members["README.md"] = (f"# Exact Hoeffding Constants for Finite Exchangeable Sequences\n\nZinan Wang and Xinhao Yang · {DATE}\n\nXinhao Yang: University of Southern California.\n\n"
        "This research bundle contains the complete article, its modular LaTeX source, all project Lean source, pinned toolchain and dependency metadata, reproduction scripts, theorem mapping, source and audit records, and the cited literature catalogue.\n\n"
        "## Article\n\nRead `article/combined_all.pdf`. The source `article/combined_all.tex` contains the principal paper and all technical refinements with one bibliography. The separate principal paper and supplement are `manuscript.pdf` and `supplementary_refinements.pdf`. Run `bash build_articles.sh` to rebuild the three PDFs.\n\n"
        f"For arXiv, use `{PREFIX}_arXiv_Source_{DATE}.zip`. The abstract and metadata are provided separately.\n\n"
        "## Lean reproduction\n\nInstall elan, Python 3 and Git, then run `bash reproduce_formal.sh`. The `lean-toolchain` file selects Lean 4.33.0. `lake-manifest.json` pins Mathlib and all its dependencies; `lake exe cache get` downloads their sources and compiled cache. No compiled project objects are included. The source is checked by `lake build ExactHoeffding`, the umbrella is checked independently, and the generated public-theorem audit is compared and checked against its complete transitive axiom dependencies.\n\n"
        f"Mathlib commit: `{mathlib['rev']}`. The included snapshot has {len(files)} project Lean source files and an umbrella audit listing {theorems} public theorems in {modules} project modules. `RESEARCH_PROVENANCE.json` records the exact source snapshot and its consistency checks.\n\n"
        "The theorem-to-manuscript mapping, mathematical hypotheses and verification scope are recorded in `theorem_to_lean.csv`, `README_LEAN4.md`, `LEAN_PROOF_STATUS.md`, `proof_gap_register.md` and `formal_status/`. The retained build records are in `checks/logs/full_closure/`; the reproduction script writes fresh results to `build/formal/`.\n\n"
        "## Literature and rights\n\n`refs/` identifies all 16 cited works and includes four unchanged CC BY 4.0 PDFs, each with a recorded source, license and SHA-256 checksum. `THIRD_PARTY_NOTICES.md` preserves their attribution.\n\n"
        "Copyright (c) 2026 Zinan Wang. All rights reserved in the original work. See `LICENSE` and `COPYRIGHT.md`.\n\n"
        "Verify the delivered inventory with `sha256sum -c SHA256SUMS.txt`.\n").encode()
    members["SHA256SUMS.txt"] = "".join(f"{sha256(data)}  {name}\n" for name, data in sorted(members.items())).encode()
    destination = output / f"{PREFIX}_Formalized_Research_Bundle_{DATE}.zip"
    write_zip(destination, members)
    with tempfile.TemporaryDirectory(prefix="wang-formal-research-check-") as temporary:
        check = Path(temporary)
        with ZipFile(destination) as archive:
            if archive.testzip() is not None:
                raise RuntimeError("Research ZIP integrity failure")
            archive.extractall(check)
        result = subprocess.run(["sha256sum", "-c", "SHA256SUMS.txt"], cwd=check, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
        subprocess.run(["bash", "-n", "reproduce_formal.sh"], cwd=check, check=True)
        subprocess.run(["python3", "checks/generate_axiom_audit.py", "--check"], cwd=check, check=True)
    report = {**provenance, "archive": destination.name, "archive_members": len(members),
              "bytes": destination.stat().st_size, "sha256": sha256(destination.read_bytes()),
              "extracted_manifest_check_exit_code": 0, "extracted_audit_regeneration_exit_code": 0,
              "reproduction_script_syntax_exit_code": 0}
    (output / "research_build_report.json").write_text(json.dumps(report, indent=2) + "\n")
    (output / "research_bundle.sha256").write_text(f"{sha256(destination.read_bytes())}  {destination.name}\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
