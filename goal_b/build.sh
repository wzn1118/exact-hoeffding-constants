#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT/.."
python3 goal_b/code/verify_goal_b.py --maxN 60 --numericN 18 --output goal_b/checks/verification.json
(cd goal_b/paper && pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null && pdflatex -interaction=nonstopmode -halt-on-error main.tex >/dev/null)
mkdir -p goal_b/dist
python3 - <<'PY'
from pathlib import Path
import hashlib, zipfile
root=Path('goal_b')
files=['README.md','requirements.txt','paper/main.tex','paper/main.pdf','code/verify_goal_b.py','checks/verification.json','checks/independent_audit.md','checks/lean_tasks.md','build.sh']
(root/'SHA256SUMS.txt').write_text(''.join(f'{hashlib.sha256((root/f).read_bytes()).hexdigest()}  {f}\n' for f in files),encoding='utf-8')
files.append('SHA256SUMS.txt')
archive=root/'dist/GoalB_FixedSample_FiniteN_Research_Package.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
    for file in files:z.write(root/file,arcname=file)
print('Generated:',archive,archive.stat().st_size,'bytes')
PY
