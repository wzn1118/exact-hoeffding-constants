#!/usr/bin/env python3
"""Refresh checksums for the current source, publication and test logs."""
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
    'README.md','README_zh.md','CITATION.cff','REVISION_NOTES_2026-10-11.md',
    'manuscript.pdf','supplementary_refinements.pdf',
    'submission/manuscript.tex','requirements.txt','run_all.sh',
    'build_manuscript.sh','.github/workflows/publish-manuscript.yml',
    'checks/refresh_checksums.py',
})
for group in ['source/*.tex','checks/*.py','checks/logs/*.log']:
    tracked.update(p.relative_to(root).as_posix() for p in root.glob(group) if p.is_file())
lines=[]
for name in sorted(tracked):
    p=root/name
    if p.is_file():
        lines.append(f'{sha256(p.read_bytes()).hexdigest()}  ./{name}')
manifest.write_text('\n'.join(lines)+'\n')
print(f'PASS: refreshed {len(lines)} maintained-file SHA256 checksums')
