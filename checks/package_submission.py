#!/usr/bin/env python3
"""Build and verify the article, arXiv upload source, and reference companion."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import zipfile

from sync_submission import ROOT, synchronize

DATE = "2026-10-16"
PREFIX = "Wang_Zinan_Exact_Hoeffding"
STAMP = (2026, 10, 16, 0, 0, 0)
ENV = {**os.environ, "SOURCE_DATE_EPOCH": "1792108800", "FORCE_SOURCE_DATE": "1", "TZ": "UTC"}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_evidence(path: Path, text: str) -> None:
    path.write_text("\n".join(line.rstrip() for line in text.splitlines()).rstrip() + "\n")


def write_zip(path: Path, members: dict[str, bytes]) -> None:
    with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
        for name, data in sorted(members.items()):
            item = zipfile.ZipInfo(name, date_time=STAMP)
            item.compress_type = zipfile.ZIP_DEFLATED
            item.external_attr = 0o100644 << 16
            archive.writestr(item, data)


def run(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, cwd=cwd, env=ENV, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, check=True)


def compile_tex(directory: Path, stem: str, evidence: Path) -> dict:
    for number in range(1, 4):
        process = run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", stem + ".tex"], directory)
        write_evidence(evidence / f"{stem}_pass{number}.stdout", process.stdout)
    log = (directory / (stem + ".log")).read_text()
    write_evidence(evidence / (stem + ".log"), log)
    problems = re.findall(r"(?m)^.*(?:Warning:|Overfull|Underfull|undefined|multiply defined|^!).*$", log)
    if problems:
        raise RuntimeError(f"{stem}: final-pass TeX diagnostics: " + "\n".join(problems))
    info = run(["pdfinfo", stem + ".pdf"], directory).stdout
    write_evidence(evidence / (stem + ".pdfinfo"), info)
    pages = int(re.search(r"(?m)^Pages:\s+(\d+)", info).group(1))
    if not re.search(r"(?m)^Author:\s+Zinan Wang and Xinhao Yang\s*$", info):
        raise RuntimeError("Unexpected PDF author in " + stem)
    return {"pages": pages, "passes": 3, "exit_code": 0, "final_diagnostics": []}


def source_counts(text: str) -> dict:
    labels = re.findall(r"\\label\{([^}]+)\}", text)
    if len(labels) != len(set(labels)):
        raise RuntimeError("Duplicate labels in combined source")
    references = set(re.findall(r"\\(?:eqref|ref|pageref)\{([^}]+)\}", text))
    if references - set(labels):
        raise RuntimeError("Missing labels: " + repr(references - set(labels)))
    bibliography = re.findall(r"\\bibitem(?:\[[^]]*\])?\{([^}]+)\}", text)
    citations = {key.strip() for group in re.findall(r"\\cite(?:\[[^]]*\])?\{([^}]+)\}", text) for key in group.split(",")}
    if citations - set(bibliography) or len(bibliography) != len(set(bibliography)):
        raise RuntimeError("Bibliography key mismatch")
    if text.count(r"\begin{document}") != 1 or text.count(r"\begin{thebibliography}") != 1:
        raise RuntimeError("The arXiv source must have one document and one bibliography")
    return {"theorem_statements": len(re.findall(r"\\begin\{(?:theorem|proposition|lemma|corollary)\}", text)),
            "bibliographic_entries": len(bibliography), "unique_labels": len(labels)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "submission" / "release")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    evidence = output / "build_evidence"
    evidence.mkdir(exist_ok=True)
    entries = synchronize()
    combined = entries["combined_all.tex"].read_bytes()
    counts = source_counts(combined.decode())
    if counts["theorem_statements"] != 30 or counts["bibliographic_entries"] != 16:
        raise RuntimeError("Review the statement and bibliography counts before release")
    upload_name = f"{PREFIX}_arXiv_Source_{DATE}.zip"
    upload = output / upload_name
    write_zip(upload, {"combined_all.tex": combined})
    references = {str(path.relative_to(ROOT)): path.read_bytes() for path in sorted((ROOT / "refs").rglob("*")) if path.is_file()}
    references["THIRD_PARTY_NOTICES.md"] = (ROOT / "THIRD_PARTY_NOTICES.md").read_bytes()
    records = json.loads((ROOT / "refs/SOURCES.json").read_text())
    verified = []
    for record in records:
        if record.get("local_pdf"):
            key = "refs/" + record["local_pdf"]
            if sha256(references[key]) != record["sha256"]:
                raise RuntimeError("Reference PDF checksum mismatch: " + key)
            verified.append(key)
    if len(verified) != 4:
        raise RuntimeError("Review the reference PDF inventory")
    references["README.txt"] = ("Reference companion for Zinan Wang and Xinhao Yang, Exact Hoeffding Constants for Finite Exchangeable Sequences.\n"
        "The catalogue identifies all 16 cited works. Four unchanged CC BY 4.0 PDFs are included.\n"
        "See THIRD_PARTY_NOTICES.md and refs/SOURCES.json for authorship, source versions, licenses and hashes.\n"
        "Other references are supplied as bibliographic records and source links.\n").encode()
    references["SHA256SUMS.txt"] = "".join(f"{sha256(data)}  {name}\n" for name, data in sorted(references.items())).encode()
    refs_name = f"{PREFIX}_References_{DATE}.zip"
    write_zip(output / refs_name, references)
    with tempfile.TemporaryDirectory(prefix="wang-arxiv-clean-") as temporary:
        clean = Path(temporary)
        extracted = clean / "arxiv"
        extracted.mkdir()
        with zipfile.ZipFile(upload) as archive:
            archive.extractall(extracted)
        if sorted(path.name for path in extracted.iterdir()) != ["combined_all.tex"]:
            raise RuntimeError("Unexpected file in the arXiv upload archive")
        builds = {"combined_all": compile_tex(extracted, "combined_all", evidence)}
        shutil.copyfile(extracted / "combined_all.pdf", output / "combined_all.pdf")
        modular = clean / "modular"
        (modular / "source").mkdir(parents=True)
        (modular / "build").mkdir()
        for path in (ROOT / "source").glob("*.tex"):
            shutil.copyfile(path, modular / "source" / path.name)
        # The supplement reads main labels from ../build/manuscript.aux.
        for stem in ("manuscript", "supplement"):
            for number in range(1, 4):
                process = run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "-output-directory=../build", stem + ".tex"], modular / "source")
                write_evidence(evidence / f"modular_{stem}_pass{number}.stdout", process.stdout)
            log = (modular / "build" / (stem + ".log")).read_text()
            write_evidence(evidence / ("modular_" + stem + ".log"), log)
            if re.search(r"Warning:|Overfull|Underfull|undefined|multiply defined|(?m:^!)", log):
                raise RuntimeError("Final modular TeX diagnostic in " + stem)
            info = run(["pdfinfo", str(modular / "build" / (stem + ".pdf"))], modular).stdout
            pages = int(re.search(r"(?m)^Pages:\s+(\d+)", info).group(1))
            builds[stem] = {"pages": pages, "passes": 3, "exit_code": 0, "final_diagnostics": []}
        article = {"article/combined_all.tex": combined, "article/combined_all.pdf": (output / "combined_all.pdf").read_bytes()}
        for stem, destination in (("manuscript", "manuscript.pdf"), ("supplement", "supplementary_refinements.pdf")):
            article[destination] = (modular / "build" / (stem + ".pdf")).read_bytes()
        for path in (ROOT / "source").glob("*.tex"):
            article["source/" + path.name] = path.read_bytes()
    pages = builds["combined_all"]["pages"]
    abstract = (r"We determine the least constant in the Hoeffding-type exponential-moment inequality for arbitrary centered linear contrasts of bounded exchangeable sequences of length $N$. The sharp coefficient is $C_N^\star=N/(N-1)$ for even $N$ and $C_N^\star=2/[(N-1)\log((N+1)/(N-1))]$ for odd $N$. The even coefficient coincides with the maximal normalized variance. In odd populations the optimal Laplace parameter is nonzero, and the sharp coefficient strictly exceeds the variance benchmark. We prove an all-tilt hypergeometric variance bound and a parity-uniform mean-dependent Laplace envelope, and determine all odd-population extremizers. Further results give fourth-order optimal-proxy expansions, fixed-sample success-count extremality, and analytic contraction on compact success-proportion intervals." + "\n")
    (output / "abstract.txt").write_text(abstract)
    metadata = {"title": "Exact Hoeffding Constants for Finite Exchangeable Sequences", "authors": ["Zinan Wang", "Xinhao Yang"],
                "affiliations": {"Xinhao Yang": "University of Southern California"},
                "date": DATE, "primary_category": "math.PR", "optional_cross_list": "math.ST",
                "comments": f"{pages} pages, including all technical refinements; no figures",
                "msc_2020": ["60E15", "60F10", "33C45", "62E15"],
                "upload_archive": upload_name, "entry_point": "combined_all.tex",
                "copyright": "Copyright (c) 2026 Zinan Wang. All rights reserved."}
    (output / "arxiv_metadata.json").write_text(json.dumps(metadata, ensure_ascii=False, indent=2) + "\n")
    build_script = """#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
for stem in manuscript supplement; do
  for pass in 1 2 3; do
    (cd source && pdflatex -interaction=nonstopmode -halt-on-error -output-directory=../build "$stem.tex")
  done
done
for pass in 1 2 3; do
  (cd article && pdflatex -interaction=nonstopmode -halt-on-error combined_all.tex)
done
"""
    article["build_articles.sh"] = build_script.encode()
    for name in ("LICENSE", "COPYRIGHT.md", "CITATION.cff", "THIRD_PARTY_NOTICES.md", "docs/contributions_zh.md"):
        article[name] = (ROOT / name).read_bytes()
    article.update(references)
    article[upload_name] = upload.read_bytes()
    article["arxiv_metadata.json"] = (output / "arxiv_metadata.json").read_bytes()
    article["abstract.txt"] = (output / "abstract.txt").read_bytes()
    article["README.md"] = (f"# Exact Hoeffding Constants for Finite Exchangeable Sequences\n\nZinan Wang and Xinhao Yang · {DATE}\n\nXinhao Yang: University of Southern California.\n\n"
        f"The complete article is `article/combined_all.pdf` ({pages} pages). Its single LaTeX entry point is `article/combined_all.tex`.\n\n"
        "The principal paper and technical supplement are also supplied separately as `manuscript.pdf` and `supplementary_refinements.pdf`. "
        "Their modular sources are in `source/`. Run `bash build_articles.sh` with pdfLaTeX to rebuild all three PDFs.\n\n"
        f"For arXiv, upload `{upload_name}`, the dedicated single-entry source archive included here. `abstract.txt` and `arxiv_metadata.json` provide the submission fields.\n\n"
        "The `refs/` catalogue covers 16 cited works and includes four unchanged CC BY 4.0 PDFs, with source and license records.\n\n"
        "Copyright (c) 2026 Zinan Wang. All rights reserved in the original work. See LICENSE, COPYRIGHT.md and THIRD_PARTY_NOTICES.md.\n").encode()
    article["SHA256SUMS.txt"] = "".join(f"{sha256(data)}  {name}\n" for name, data in sorted(article.items()) if name != "SHA256SUMS.txt").encode()
    publication_name = f"{PREFIX}_Publication_Bundle_{DATE}.zip"
    write_zip(output / publication_name, article)
    with tempfile.TemporaryDirectory(prefix="wang-publication-clean-") as temporary:
        complete = Path(temporary)
        with zipfile.ZipFile(output / publication_name) as archive:
            archive.extractall(complete)
        process = run(["bash", "build_articles.sh"], complete)
        write_evidence(evidence / "publication_bundle_build.stdout", process.stdout)
        for relative in ("build/manuscript.log", "build/supplement.log", "article/combined_all.log"):
            log = (complete / relative).read_text()
            if re.search(r"Warning:|Overfull|Underfull|undefined|multiply defined|(?m:^!)", log):
                raise RuntimeError("Final extracted-bundle TeX diagnostic in " + relative)
        checksums = run(["sha256sum", "-c", "SHA256SUMS.txt"], complete)
        write_evidence(evidence / "publication_bundle_sha256.stdout", checksums.stdout)
    report = {"date": DATE, "clean_directory_build": True, "publication_bundle_build_exit_code": 0, "publication_bundle_hash_check_exit_code": 0, "builds": builds, "source_structure": counts,
              "arxiv_archive_members": ["combined_all.tex"], "reference_pdfs_verified": verified,
              "artifacts": {name: {"bytes": (output / name).stat().st_size, "sha256": sha256((output / name).read_bytes())}
                            for name in (upload_name, refs_name, publication_name, "combined_all.pdf")}}
    (output / "build_report.json").write_text(json.dumps(report, indent=2) + "\n")
    manifest_files = sorted(path for path in output.iterdir() if path.is_file() and path.name != "SHA256SUMS.txt")
    (output / "SHA256SUMS.txt").write_text("".join(f"{sha256(path.read_bytes())}  {path.name}\n" for path in manifest_files))
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
