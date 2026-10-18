#!/usr/bin/env python3
"""Produce the authoritative unified paper and clean reproducibility archives."""
from pathlib import Path
from zipfile import ZipFile, ZipInfo, ZIP_DEFLATED
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
CURRENT = ROOT / "submission/current"
PAPER = ROOT / "submission/integrated/combined_manuscript.tex"
PDF = ROOT / "submission/integrated/combined_manuscript.pdf"
TITLE = ("Sharp Hypergeometric Concentration: Exact Exchangeability Constants, "
         "Fixed-Sample Extremizers, and Piecewise KL Bounds")
BLOCKED_DIRS = {"logs", "release", "current", ".git", ".lake", "__pycache__", "build_evidence"}
BLOCKED_EXTS = {".zip",".pdf",".png",".jpg",".jpeg",".log",".pyc",".aux",".out",".gz",".tar"}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def writezip(path, contents):
    with ZipFile(path, "w", ZIP_DEFLATED, compresslevel=9) as z:
        for k in sorted(contents):
            item = ZipInfo(k,(2026,10,17,0,0,0))
            item.compress_type = ZIP_DEFLATED
            item.external_attr = 0o644 << 16
            z.writestr(item,contents[k])
    with ZipFile(path) as z:
        if z.testzip() is not None:
            raise RuntimeError("ZIP failed verification: "+str(path))

def files_in(path, contents):
    if not path.exists():
        raise RuntimeError("Missing reproducibility input: "+str(path))
    items=path.rglob("*") if path.is_dir() else [path]
    for p in items:
        if not p.is_file():
            continue
        rel=p.relative_to(ROOT)
        # The release generator is a publisher utility, not a mathematical reproducer.
        if rel.as_posix() == "checks/build_current_release.py":
            continue
        if any(part in BLOCKED_DIRS for part in rel.parts):
            continue
        if p.suffix.lower() in BLOCKED_EXTS:
            continue
        contents[rel.as_posix()]=p.read_bytes()

def main():
    tex = PAPER.read_bytes()
    frozen = CURRENT / "manuscript.tex"
    if frozen.exists() and frozen.read_bytes() != tex:
        raise RuntimeError("Generated source differs from the frozen official manuscript")
    pdf = PDF.read_bytes()
    src = tex.decode("utf-8")
    required_publication_fixes = {
        "Lee-Kim contemporaneous attribution": r"\bibitem{LeeKimSerfling}",
        "supported factorial threshold": r"for every integer $\mu<d\le m$",
        "outside-support factorial event": r"For integer $d>m$",
        "explicit consecutive candidate ratio": r"\frac{c_{j+1}}{c_j}",
        "actual tilted-variance barrier lemma": r"Lemma \ref{odd:lem:barrier} establishes",
    }
    missing_fixes = [name for name, marker in required_publication_fixes.items() if marker not in src]
    if missing_fixes:
        raise RuntimeError("Mathematical manuscript repair regression: " + ", ".join(missing_fixes))
    if r"\author{Zinan Wang" not in src or r"\and Xinhao Yang" not in src:
        raise RuntimeError("Author order in official manuscript incorrect")
    if "The University of Manchester" not in src or "University of Southern California" not in src:
        raise RuntimeError("Institutional affiliations missing")
    lines = subprocess.check_output(["pdfinfo",str(PDF)],text=True)
    if not re.search(r"(?m)^Author:\s*Zinan Wang and Xinhao Yang\s*$",lines):
        raise RuntimeError("PDF author metadata incorrect")
    pages = int(re.search(r"(?m)^Pages:\s*(\d+)",lines).group(1))
    if pages < 30:
        raise RuntimeError("Unified paper unexpectedly short")
    labels = re.findall(r"\\label\{([^{}]+)\}",src)
    refs = set(re.findall(r"\\(?:ref|eqref|autoref|pageref)\{([^{}]+)\}",src))
    cited = {k.strip() for group in re.findall(r"\\cite(?:\[[^\]]+\])?\{([^{}]+)\}",src) for k in group.split(",")}
    bib = set(re.findall(r"\\bibitem(?:\[[^\]]+\])?\{([^{}]+)\}",src))
    if len(labels) != len(set(labels)) or refs-set(labels) or cited-bib:
        raise RuntimeError("Label or bibliography verification failed")
    CURRENT.mkdir(parents=True,exist_ok=True)
    (CURRENT/"manuscript.tex").write_bytes(tex)
    (CURRENT/"manuscript.pdf").write_bytes(pdf)
    meta={"title":TITLE,"authors":[{"name":"Zinan Wang","affiliation":"The University of Manchester"},
           {"name":"Xinhao Yang","affiliation":"University of Southern California"}],
          "date":"2026-10-17","primary_category":"math.PR","optional_cross_list":"math.ST",
          "entry_point":"manuscript.tex","pages":pages,"references":len(bib)}
    (CURRENT/"metadata.json").write_text(json.dumps(meta,indent=2,ensure_ascii=False)+"\n")
    writezip(CURRENT/"arxiv-source.zip",{"manuscript.tex":tex})
    clean={"manuscript.tex":tex,"manuscript.pdf":pdf,
           "metadata.json":(CURRENT/"metadata.json").read_bytes()}
    clean["SHA256SUMS.txt"]="".join(sha(clean[k])+"  "+k+"\n" for k in sorted(clean)).encode()
    writezip(CURRENT/"clean-submission.zip",clean)
    reproducer={}
    for f in ["ExactHoeffding.lean","ExactHoeffding","checks","formal_status",
              "goal_b/code","goal_b/checks","goal_b/paper/main.tex",
              "goal_b/requirements.txt","goal_b/build.sh",
              "source","research/tail_bounds/benchmark_cases.json",
              "research/tail_bounds/minimum_variance_tail.tex",
              "submission/manuscript.tex","submission/integrated/build_clean_submission.py",
              "submission/current/manuscript.tex","submission/current/theorem_lean_concordance.md",
              "submission/current/theorem_lean_manifest.json","lean-toolchain","lakefile.toml",
              "lake-manifest.json","requirements.txt","run_all.sh",
              "build_manuscript.sh","LICENSE","COPYRIGHT.md",
              "THIRD_PARTY_NOTICES.md","theorem_to_lean.csv",
              "LEAN_PROOF_STATUS.md","proof_gap_register.md"]:
        p=ROOT/f
        if p.exists():
            files_in(p,reproducer)
    # Historical proof-check modules are part of the repository's Lean source inventory.
    for historical_lean in (ROOT/"research/history").rglob("*.lean"):
        files_in(historical_lean,reproducer)
    reproducer["submission/current/manuscript.pdf"]=pdf
    # Current source and correspondence are part of the reproduction archive.
    for current_file in ("manuscript.tex", "metadata.json", "theorem_lean_concordance.md", "theorem_lean_manifest.json", "display_formula_inventory.json"):
        current_path = CURRENT / current_file
        if current_path.exists():
            reproducer[f"submission/current/{current_file}"] = current_path.read_bytes()

    # Exact byte-for-byte coverage of every tracked Lean file.
    lean_count = sum(k == "ExactHoeffding.lean" or
                     (k.startswith("ExactHoeffding/") and k.endswith(".lean"))
                     for k in reproducer)
    expected = 1 + len(list((ROOT / "ExactHoeffding").rglob("*.lean")))
    if lean_count != expected:
        raise RuntimeError(f"Incomplete core Lean sources {lean_count}/{expected}")
    tracked_lean = set(subprocess.check_output(
        ["git", "ls-files", "--", "*.lean"], cwd=ROOT, text=True).splitlines())
    archived_lean = {key for key in reproducer if key.endswith(".lean")}
    if archived_lean != tracked_lean:
        raise RuntimeError("Lean file coverage failure: missing=" +
                           str(sorted(tracked_lean - archived_lean)) +
                           "; extra=" + str(sorted(archived_lean - tracked_lean)))
    mismatched = [key for key in sorted(tracked_lean)
                  if reproducer[key] != (ROOT / key).read_bytes()]
    if mismatched:
        raise RuntimeError("Lean source content differs from this checkout: " + str(mismatched))

    member_count = len(reproducer) + 3  # current README, reproduction README, SHA256SUMS
    release_readme = (
        "# Current Main+A+B submission\n\n" + TITLE + "\n\n"
        "Zinan Wang — The University of Manchester<br>\n"
        "Xinhao Yang — University of Southern California\n\n"
        f"**{pages} pages · {len(bib)} references · {len(archived_lean)} Lean files** "
        f"({lean_count} core; {len(archived_lean) - lean_count} audit/history) "
        f"· {member_count} reproduction archive members.\n\n"
        "- [Paper PDF](manuscript.pdf)\n"
        "- [LaTeX source](manuscript.tex)\n"
        "- [arXiv source ZIP](arxiv-source.zip)\n"
        "- [Clean submission ZIP](clean-submission.zip)\n"
        "- [Complete reproducibility ZIP](complete-reproducibility.zip)\n"
        "- [Theorem–Lean concordance](theorem_lean_concordance.md)\n"
        "- [Submission metadata](metadata.json)\n\n"
        "The exact paper-statement coverage and any open scope qualifications are recorded in the concordance and formal_status reports. "
        "Main, A and B share the integrated formal proof project. "
        "Original research and earlier manuscript editions are archived "
        "in their respective directories.\n"
    )
    (CURRENT / "README.md").write_text(release_readme, encoding="utf-8")
    reproducer["submission/current/README.md"] = release_readme.encode("utf-8")

    disclosure = "AI-assisted tools were used in Lean 4 formalization and verification."
    readme = (
        TITLE + "\n"
        "Zinan Wang — The University of Manchester\n"
        "Xinhao Yang — University of Southern California\n\n"
        "Lean 4 build and axiom audit:\n"
        "  lake exe cache get\n"
        "  lake build ExactHoeffding\n"
        "  python3 checks/generate_axiom_audit.py --check\n"
        "  python3 checks/check_full_manuscript_concordance.py\n"
        "  lake env lean checks/full_closure_axioms.lean\n\n"
        "Numerical verification:\n"
        "  python3 -m pip install -r requirements.txt\n"
        "  python3 checks/verify_piecewise_kl.py\n"
        "  python3 goal_b/code/verify_goal_b.py --maxN 60 --numericN 18 "
        "--output goal_b/checks/verification.json\n\n"
        "Rebuild the unified manuscript:\n"
        "  python3 submission/integrated/build_clean_submission.py\n"
        "  (cd submission/integrated && latexmk -pdf -halt-on-error combined_manuscript.tex)\n\n"
        + disclosure + "\n"
    )
    reproducer["README.txt"] = readme.encode("utf-8")
    disclosure_files = [p for p, data in reproducer.items()
                        if disclosure.encode("utf-8") in data]
    if disclosure_files != ["README.txt"] or readme.count(disclosure) != 1:
        raise RuntimeError("Expected the formalization disclosure once in README.txt")
    reproducer["SHA256SUMS.txt"] = "".join(
        sha(reproducer[k]) + "  " + k + "\n" for k in sorted(reproducer)
    ).encode()
    if len(reproducer) != member_count:
        raise RuntimeError("Reproducibility member count mismatch")
    writezip(CURRENT / "complete-reproducibility.zip", reproducer)
    print(f"Release PASS: {pages} pages; {len(bib)} references; "
          f"{len(archived_lean)} Lean files ({lean_count} core); "
          f"{len(reproducer)} reproducibility members; one disclosure.")

if __name__ == "__main__":
    main()
