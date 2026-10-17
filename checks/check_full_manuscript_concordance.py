#!/usr/bin/env python3
"""Validate theorem-to-Lean coverage against the frozen current manuscript.

This check requires every theorem-class environment (including unlabeled ones)
and explicitly listed supplementary claims to have a reviewed concordance row.
For rows marked Complete, every cited public theorem must occur in the generated
Lean axiom audit. Partial rows are reported as blockers and make the check fail.
"""
from __future__ import annotations

import argparse
import json
import hashlib
import re
import sys
import subprocess
import shlex
from pathlib import Path

from check_a1_variance_contract import audit_contract as audit_a1_variance_contract

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lean-command", default="lake env lean",
                    help="Lean command used for the kernel-side axiom audit")
args = parser.parse_args()

ROOT = Path(__file__).resolve().parents[1]
MANUSCRIPT = ROOT / "submission/current/manuscript.tex"
MAP = ROOT / "checks/manuscript_lean_map.json"
AUDIT = ROOT / "checks/full_closure_axioms.lean"

source = MANUSCRIPT.read_text()
items = []
pattern = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary)\}"
    r"(?:\[(.*?)\])?(.*?)\\end\{\1\}", re.S
)
for idx, match in enumerate(pattern.finditer(source), 1):
    kind, title, body = match.groups()
    label_match = re.search(r"\\label\{([^}]+)\}", body)
    label = label_match.group(1) if label_match else None
    compact_title = re.sub(r"\s+", " ", title or "").strip()
    line = source.count("\n", 0, match.start()) + 1
    key = label or f"unlabeled:{compact_title}"
    items.append({"index": idx, "key": key, "kind": kind, "title": compact_title, "line": line})

mapping = json.loads(MAP.read_text())
if mapping.get("source_sha256") != hashlib.sha256(MANUSCRIPT.read_bytes()).hexdigest():
    raise SystemExit("Frozen manuscript SHA-256 differs from the reviewed source")
rows = mapping["results"]
manifest_path = ROOT / "submission/current/theorem_lean_manifest.json"
if not manifest_path.is_file():
    raise SystemExit("missing inspected theorem manifest; run checks/export_theorem_manifest.py first")
try:
    manifest = json.loads(manifest_path.read_text())
    audit_a1_variance_contract(mapping, manifest, ROOT)
except (ValueError, KeyError, OSError) as error:
    raise SystemExit(f"A1 variance contract failed: {error}") from error
by_key = {}
for row in rows:
    key = row["key"]
    if key in by_key:
        raise SystemExit(f"duplicate concordance key: {key}")
    by_key[key] = row

paper_keys = {item["key"] for item in items}
row_paper_keys = {row["key"] for row in rows if row.get("paper_environment", True)}
if paper_keys != row_paper_keys:
    raise SystemExit(
        "manuscript coverage mismatch: "
        f"missing={sorted(paper_keys-row_paper_keys)}; "
        f"extra={sorted(row_paper_keys-paper_keys)}"
    )

for item in items:
    row = by_key[item["key"]]
    if row["title"] != item["title"]:
        raise SystemExit(f"title changed at {item['key']}: {item['title']!r} != {row['title']!r}")
    if row["kind"] != item["kind"]:
        raise SystemExit(f"environment kind changed at {item['key']}")
    if row["line"] != item["line"]:
        raise SystemExit(f"manuscript source line changed at {item['key']}")

# Execute the generated kernel-side axiom audit. Parsing declarations out of
# the Lean source alone would let comments or unused audit entries look valid.
audit_proc = subprocess.run(
    shlex.split(args.lean_command) + [str(AUDIT.relative_to(ROOT))], cwd=ROOT,
    text=True, capture_output=True, timeout=1200)
if audit_proc.returncode:
    raise SystemExit("Lean axiom audit failed:\n" + audit_proc.stdout + audit_proc.stderr)
audit_output = audit_proc.stdout + audit_proc.stderr
audit_pattern = re.compile(
    r"^'?(?P<name>ExactHoeffding\.[^']+?)'? depends on axioms:\s*\[(?P<axioms>.*?)\]",
    re.M | re.S,
)
audit_rows = audit_pattern.findall(audit_output)
audited_axioms = {
    name: {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
    for name, axioms in audit_rows
}
audited = set(audited_axioms)
if len(audited) != len(audit_rows):
    raise SystemExit("Lean axiom audit output contains duplicate or malformed theorem records")
allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in audited_axioms.items():
    unexpected = axioms - allowed_axioms
    if unexpected:
        raise SystemExit(f"Lean kernel audit found disallowed axioms for {name}: {sorted(unexpected)}")
manifest_declarations = {d["name"]: d for d in manifest["declarations"]}
missing = []
typed_contracts = 0
CONTRACT_TYPE_MARKERS = {
    "manuscript_exchangeability_constants_contract": (
        "exactExchangeableConstant", "manuscriptExchangeabilityConstantFormula",
        "IsExchangeableCoefficient", "IsLeast", "normalizedHypergeomProxy",
        "Real.artanh", "Tendsto"),
    "manuscript_cor_tail_contract": (
        "IsProbabilityMeasure", "FiniteExchangeableMeasure", "realCube",
        "manuscriptTailStatistic", "projectedWeightVariance", "Real.exp",
        "log", "sqrt"),
    "manuscript_variational_full_contract": (
        "exactExchangeableConstant", "manuscriptVariationalMaximum",
        "IsExchangeableCoefficient", "Iff"),
    "manuscript_A_integration_contract": (
        "FiniteSupportLawData", "rawLegendreRate", "rawUpperTail",
        "rawLowerTail", "ContinuousOn", "Ioo"),
    "manuscript_A3_four_symmetric_binomial_KL_contract": (
        "fourBinomialKLRate2", "fourBinomialKLRate3", "fourBinomialKLRate4",
        "fourBinomialKLRateMax", "binomialKLRate", "binomialKLSlope",
        "fourBinomialKLRate2Slope", "fourBinomialKLRate3Slope",
        "fourBinomialKLRate4Slope"),
    "manuscript_A4_exact_variance_bennett_bernstein_contract": (
        "hypergeomBennettRate", "hypergeomBernsteinRate", "hypergeomTiltVariance",
        "canonicalPiecewiseRate"),
    "manuscript_integer_two_sided_contract": (
        "canonicalPiecewiseRate", "hypergeomUpperDeviationMass",
        "hypergeomLowerDeviationMass", "hypergeomTwoSidedDeviationMass"),
    "manuscript_A_factorial_full_contract": (
        "finiteIntegerTailMass", "finiteFactorialBound", "sInf",
        "hypergeomMass", "hypergeomKLRate", "canonicalPiecewiseRate"),
}
for row in rows:
    row_names = {decl["name"] for decl in row.get("declarations", [])}
    contract = row.get("semantic_contract_declaration")
    if contract:
        typed_contracts += 1
        unqualified_contract = contract.removeprefix("ExactHoeffding.")
        if unqualified_contract not in {name.removeprefix("ExactHoeffding.") for name in row_names}:
            missing.append((row["key"], f"semantic contract is not mapped: {contract}"))
        fq_contract = contract if contract.startswith("ExactHoeffding.") else "ExactHoeffding." + contract
        contract_record = manifest_declarations.get(fq_contract)
        if contract_record is None:
            missing.append((row["key"], f"semantic contract is absent from inspected Lean manifest: {contract}"))
        else:
            required_type_markers = CONTRACT_TYPE_MARKERS.get(unqualified_contract)
            if required_type_markers:
                missing_markers = [marker for marker in required_type_markers
                                   if marker not in contract_record["type_pretty"]]
                if missing_markers:
                    missing.append((row["key"],
                                    f"semantic contract type omits required statement components {missing_markers}: {contract}"))
            # The contract can inline proof steps or call helpers outside the
            # row, so requiring a direct edge to a sibling theorem is unsound.
            if set(contract_record["axioms"]) - {"propext", "Classical.choice", "Quot.sound"}:
                missing.append((row["key"], f"semantic contract has disallowed axioms: {contract}"))
    if row["status"] == "Complete" and not row.get("declarations"):
        missing.append((row["key"], "Complete row has no theorem declaration"))
    if row["status"] == "Complete" and not contract:
        missing.append((row["key"], "Complete result lacks a proposition-level Lean statement contract"))
    for decl in row.get("declarations", []):
        name = decl["name"]
        fqname = name if name.startswith("ExactHoeffding.") else "ExactHoeffding." + name
        if fqname not in audited:
            missing.append((row["key"], fqname))
        file = ROOT / decl["file"]
        if not file.is_file():
            missing.append((row["key"], f"missing source file {decl['file']}"))
        elif not re.search(
            rf"\b(?:theorem|lemma)\s+{re.escape(name.removeprefix('ExactHoeffding.'))}\b",
            file.read_text(),
        ):
            missing.append((row["key"], f"declaration absent from {decl['file']}: {name}"))

mapped_names = {
    name if name.startswith("ExactHoeffding.") else "ExactHoeffding." + name
    for row in rows
    for decl in row.get("declarations", [])
    for name in [decl["name"]]
}
if not mapped_names <= audited:
    missing.extend(("axiom-audit", name) for name in sorted(mapped_names - audited))
if missing:
    for key, name in missing:
        print(f"FAIL: {key}: {name}")
    raise SystemExit(1)

print(f"PASS: {len(items)} theorem-class environments and {len(rows)-len(items)} supplementary claims are mapped to audited Lean declarations")
print(f"PASS: {typed_contracts} of {len(rows)} result rows have explicit typed Lean statement contracts")
print(f"PASS: actual Lean #print axioms output checked for {len(audited_axioms)} declarations; allowed set is {sorted(allowed_axioms)}")
print("PASS: A1 finite-law statements omit a positive-variance premise; the no-premise curve adapter derives positivity from endpoint support assumptions")
print("NOTE: Typed contracts are kernel-checked Lean transcriptions; the TeX-to-Lean translation remains a mathematical review, not an automatic TeX equivalence proof.")
print("PASS: every mapped result has a typed Lean statement contract; contract types are kernel checked and axiom audited.")

incomplete = [row for row in rows if row["status"] != "Complete"]
if incomplete:
    for row in incomplete:
        print(f"OPEN: {row['key']}: {row['gap']}")
    raise SystemExit(f"FAIL: {len(incomplete)} of {len(rows)} mapped results remain incomplete")
