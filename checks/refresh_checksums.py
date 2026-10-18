#!/usr/bin/env python3
"""Recompute the checksums for the current, validated paper and test outputs."""
from pathlib import Path
from hashlib import sha256
import re

root=Path(__file__).resolve().parents[1]
manifest=root/'SHA256SUMS.txt'
tracked=set()
if manifest.exists():
    for line in manifest.read_text().splitlines():
        match=re.fullmatch(r'[0-9a-f]{64}  \./(.+)',line)
        if match:
            tracked.add(match.group(1))
tracked.update({
    'README.md','README_zh.md','CITATION.cff','REVISION_NOTES_2026-10-11.md','release_notes.md',
    '.gitignore','CITATION.cff','.github/workflows/clean-integrated-submission.yml',
    'submission/manuscript.tex','requirements.txt',
    'checks/refresh_checksums.py',
    'ExactHoeffding.lean','lean-toolchain','lakefile.toml','lake-manifest.json',
    'LEAN_PROOF_STATUS.md','README_LEAN4.md','proof_gap_register.md',
    'theorem_to_lean.csv','checks/lean_axioms.lean','checks/verify_research.sh',
    '.github/workflows/lean4.yml','.github/workflows/research-validation.yml',
})
for group in ['source/*.tex','submission/*.tex','submission/*.md','submission/current/**/*','submission/integrated/*.py','research/history/release-archives/**/*','checks/*.py','checks/*.sh','checks/logs/*.log','docs/*.md','docs/*.tex','docs/proof_certification_2026-10-11.pdf']:
    tracked.update(p.relative_to(root).as_posix() for p in root.glob(group) if p.is_file())
for group in ['ExactHoeffding/*.lean','formal_status/*.md','checks/*.lean','checks/logs/full_closure/*.log','research/history/release-archives/**/*','research/tail_bounds/**/*','checks/results/piecewise_kl_*']:
    tracked.update(p.relative_to(root).as_posix() for p in root.glob(group) if p.is_file())
lines=[]
for name in sorted(tracked):
    p=root/name
    if p.is_file():
        lines.append(f'{sha256(p.read_bytes()).hexdigest()}  ./{name}')
manifest.write_text('\n'.join(lines)+'\n')
print(f'PASS: refreshed {len(lines)} maintained-file SHA256 checksums')
