#!/usr/bin/env python3
"""Refresh checksums of the published repository's maintained files."""
from pathlib import Path
from hashlib import sha256
import re

root = Path(__file__).resolve().parents[1]
manifest = root / "SHA256SUMS.txt"
old = manifest.read_text().splitlines()
tracked = set()
for line in old:
    match = re.fullmatch(r"[0-9a-f]{64}  \./(.+)", line)
    if match:
        tracked.add(match.group(1))
tracked.update({
    "manuscript.pdf", "README.md", "README_zh.md", "CITATION.cff",
    "REVISION_NOTES_2026-10-11.md", "submission/manuscript.tex",
    ".github/workflows/publish-manuscript.yml",
    "checks/refresh_checksums.py",
})
output = []
for relative in sorted(tracked):
    file = root / relative
    if file.is_file():
        output.append(f"{sha256(file.read_bytes()).hexdigest()}  ./{relative}")
manifest.write_text("\n".join(output) + "\n")
print(f"Updated {len(output)} checksums")
