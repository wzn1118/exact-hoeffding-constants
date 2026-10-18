#!/usr/bin/env python3
"""Verify all displayed-formula review records bind to the current source.

This checks byte identity, source locations, record coverage, and declared review
provenance. It does not infer mathematical equivalence from hashes or names.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "submission/current/manuscript.tex"
INVENTORY = ROOT / "submission/current/display_formula_inventory.json"
BINDINGS = ROOT / "submission/current/display_formula_review_bindings.json"
AUDIT = ROOT / "formal_status/display_formula_audit_current_20261018.md"
OLD_MAIN = ROOT / "formal_status/display_formula_audit_main_appendices.md"
OLD_AB = ROOT / "formal_status/display_formula_audit_AB.md"
PATTERN = re.compile(
    r"\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}.*?"
    r"\\end\{\1\}|\\\[.*?\\\]", re.S
)
PRIOR_COMMIT = "8b75977b138205c4ba402000b25d226d55994682"
PRIOR_SHA256 = "b1bb1e3df8d8b651c4872692a8b0f4424541b4e9b3a5576d39a2be485d26e23f"
EXPECTED_DELTA = {"D187", "D188", "D197", "D200", "D204"}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    source_bytes = SOURCE.read_bytes()
    source_text = source_bytes.decode("utf-8")
    inventory = json.loads(INVENTORY.read_text(encoding="utf-8"))
    binding = json.loads(BINDINGS.read_text(encoding="utf-8"))
    audit_text = AUDIT.read_text(encoding="utf-8")
    current_sha = sha(source_bytes)

    if inventory.get("source") != "submission/current/manuscript.tex":
        raise SystemExit("Display inventory names a different source")
    if inventory.get("source_sha256") != current_sha:
        raise SystemExit("Display inventory is not bound to current manuscript bytes")
    if binding.get("source_sha256") != current_sha:
        raise SystemExit("Review bindings are not bound to current manuscript bytes")
    if binding.get("prior_review_commit") != PRIOR_COMMIT or binding.get("prior_review_source_sha256") != PRIOR_SHA256:
        raise SystemExit("Unexpected prior-review provenance")
    for path in (OLD_MAIN, OLD_AB):
        text = path.read_text(encoding="utf-8")
        if PRIOR_COMMIT not in text or PRIOR_SHA256 not in text:
            raise SystemExit(f"Prior audit provenance is absent from {path.relative_to(ROOT)}")
    if current_sha not in audit_text:
        raise SystemExit("Current audit does not record the current whole-source SHA-256")

    matches = list(PATTERN.finditer(source_text))
    displays = inventory.get("displays", [])
    rows = binding.get("displays", [])
    if len(matches) != 240 or inventory.get("display_count") != 240 or binding.get("display_count") != 240:
        raise SystemExit("Expected exactly 240 current display blocks")
    if len(displays) != len(matches) or len(rows) != len(matches):
        raise SystemExit("Inventory, review binding, and source display counts differ")
    if [row.get("id") for row in rows] != [f"D{i}" for i in range(1, 241)]:
        raise SystemExit("Review bindings do not enumerate D1 through D240 exactly once")

    statuses = {"unchanged_exact_display": 0, "current_delta_reviewed": 0}
    for match, inv, row in zip(matches, displays, rows):
        block = match.group(0)
        start = source_text.count("\n", 0, match.start()) + 1
        end = source_text.count("\n", 0, match.end()) + 1
        labels = re.findall(r"\\label\{([^}]+)\}", block)
        block_sha = sha(block.encode("utf-8"))
        identity = (row.get("id"), row.get("start_line"), row.get("end_line"), row.get("labels"), row.get("sha256"))
        expected = (inv.get("id"), start, end, labels, block_sha)
        if identity != expected or (inv.get("start_line"), inv.get("end_line"), inv.get("labels"), inv.get("sha256")) != (start, end, labels, block_sha):
            raise SystemExit(f"Current display binding mismatch at {inv.get('id')}")
        if row.get("review_file") != "formal_status/display_formula_audit_current_20261018.md":
            raise SystemExit(f"Wrong review file for {row['id']}")
        if f'id="display-{row["id"].lower()}"' not in audit_text:
            raise SystemExit(f"Current audit omits {row['id']}")
        status = row.get("review_status")
        if status not in statuses:
            raise SystemExit(f"Unknown review status for {row['id']}: {status}")
        statuses[status] += 1
        if status == "unchanged_exact_display":
            if row.get("prior_display_sha256") != block_sha or not row.get("prior_display_id"):
                raise SystemExit(f"Exact-transfer record is not exact for {row['id']}")
            if row.get("prior_source_commit") != PRIOR_COMMIT or row.get("prior_source_sha256") != PRIOR_SHA256:
                raise SystemExit(f"Exact-transfer provenance mismatch for {row['id']}")
            if row.get("delta_note") is not None:
                raise SystemExit(f"Unchanged row unexpectedly has a delta note: {row['id']}")
        else:
            if not row.get("delta_note") or not row.get("lean_anchor"):
                raise SystemExit(f"Delta review lacks a mathematical note or Lean anchor: {row['id']}")

    if {row["id"] for row in rows if row["review_status"] == "current_delta_reviewed"} != EXPECTED_DELTA:
        raise SystemExit("Current-source delta review set changed; review and update the audit explicitly")
    if statuses != {"unchanged_exact_display": 235, "current_delta_reviewed": 5}:
        raise SystemExit(f"Unexpected display-review coverage: {statuses}")
    if binding.get("unchanged_exact_display_count") != 235 or binding.get("current_delta_reviewed_count") != 5:
        raise SystemExit("Review-binding summary counts disagree")

    print(f"PASS: all 240 displayed formulas bind to current source {current_sha}")
    print("PASS: 235 exact-content transfers and 5 explicitly reviewed current-source changes")


if __name__ == "__main__":
    main()
