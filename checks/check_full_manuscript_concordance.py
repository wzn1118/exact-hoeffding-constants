#!/usr/bin/env python3
"""Validate theorem-to-Lean coverage against the frozen current manuscript.

This check requires every theorem-class environment (including unlabeled ones)
and explicitly listed supplementary claims to have a reviewed concordance row.
For rows marked Complete, every cited public theorem must occur in the generated
Lean axiom audit. Partial rows are reported as blockers and make the check fail.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

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
rows = mapping["results"]
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
        raise SystemExit(
            f"manuscript line changed at {item['key']}: "
            f"actual={item['line']} mapped={row['line']}"
        )

for key, heading in {
    "extra:A3-four-binomial-KL": r"\subsubsection{Four binomial KL bounds}",
    "extra:A4-Bennett-Bernstein": r"\subsubsection{Exact-variance Bennett and Bernstein bounds}",
}.items():
    offset = source.find(heading)
    if offset < 0 or key not in by_key:
        raise SystemExit(f"supplementary result section missing: {key}")
    actual_line = source.count("\n", 0, offset) + 1
    if by_key[key]["line"] != actual_line:
        raise SystemExit(
            f"supplementary result line changed at {key}: "
            f"actual={actual_line} mapped={by_key[key]['line']}"
        )


# The names printed by `#print axioms` are independently parsed from the
# generated audit source, so misspellings and unimported declarations fail.
audit = AUDIT.read_text()
audited = set(re.findall(r"^#print axioms ExactHoeffding\.(\S+)", audit, re.M))
missing = []
for row in rows:
    for decl in row.get("declarations", []):
        fqname = decl["name"]
        if row["status"] == "Complete" and fqname not in audited:
            missing.append((row["key"], fqname))
        if row["status"] == "Complete":
            file = ROOT / decl["file"]
            if not file.is_file():
                missing.append((row["key"], f"missing source file {decl['file']}"))
            elif not re.search(rf"\b(?:theorem|lemma)\s+{re.escape(fqname)}\b", file.read_text()):
                missing.append((row["key"], f"declaration absent from {decl['file']}: {fqname}"))
if missing:
    for key, name in missing:
        print(f"FAIL: {key}: {name}")
    raise SystemExit(1)

incomplete = [row for row in rows if row["status"] != "Complete"]
if incomplete:
    for row in incomplete:
        print(f"OPEN: {row['key']}: {row['gap']}")
    raise SystemExit(f"FAIL: {len(incomplete)} of {len(rows)} mapped results remain incomplete")

print(f"PASS: {len(items)} theorem-class environments and {len(rows)-len(items)} supplementary claims are mapped to audited Lean declarations")
