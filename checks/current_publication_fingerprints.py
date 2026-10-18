#!/usr/bin/env python3
"""Bind current audit documents to the published PDF, independently of Git."""
from __future__ import annotations

import json
from pathlib import Path
import re

PDF_BINDINGS = {
    "formal_status/current_pdf_lean_reconciliation_20261018.md":
        r"(`submission/current/manuscript\.pdf`: SHA-256 `)([0-9a-f]{64})(`)",
    "formal_status/manuscript_concordance.md":
        r"(the current PDF SHA-256 is `)([0-9a-f]{64})(`)",
    "formal_status/semantic_contract_audit_20261017.md":
        r"(`submission/current/manuscript\.pdf`: SHA-256 `)([0-9a-f]{64})(`)",
}
BASELINE = "formal_status/baseline_protection_20261017.json"


def validate_pdf_fingerprints(root: Path, digest: str) -> None:
    for relative, pattern in PDF_BINDINGS.items():
        matches = re.findall(pattern, (root / relative).read_text(encoding="utf-8"))
        if len(matches) != 1 or matches[0][1] != digest:
            raise ValueError(f"published PDF fingerprint mismatch: {relative}")
    baseline = json.loads((root / BASELINE).read_text(encoding="utf-8"))
    if baseline.get("manuscript_pdf_sha256") != digest:
        raise ValueError(f"published PDF fingerprint mismatch: {BASELINE}")


def sync_pdf_fingerprints(root: Path, digest: str) -> None:
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError("invalid PDF SHA-256")
    # All anchors must exist uniquely before any document is changed.
    patches = []
    for relative, pattern in PDF_BINDINGS.items():
        path = root / relative
        text = path.read_text(encoding="utf-8")
        if len(re.findall(pattern, text)) != 1:
            raise ValueError(f"expected one published PDF anchor: {relative}")
        patches.append((path, re.sub(pattern, lambda m: m[1] + digest + m[3], text)))
    baseline_path = root / BASELINE
    baseline = json.loads(baseline_path.read_text(encoding="utf-8"))
    if "manuscript_pdf_sha256" not in baseline:
        raise ValueError("baseline PDF anchor missing")
    baseline["manuscript_pdf_sha256"] = digest
    for path, text in patches:
        path.write_text(text, encoding="utf-8")
    baseline_path.write_text(json.dumps(baseline, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    validate_pdf_fingerprints(root, digest)
