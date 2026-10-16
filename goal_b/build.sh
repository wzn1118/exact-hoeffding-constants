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
entries=[
    (root/'README.md','README.md'),
    (root/'requirements.txt','requirements.txt'),
    (root/'paper/main.tex','paper/main.tex'),
    (root/'paper/main.pdf','paper/main.pdf'),
    (root/'code/verify_goal_b.py','code/verify_goal_b.py'),
    (root/'checks/verification.json','checks/verification.json'),
    (root/'checks/independent_audit.md','checks/independent_audit.md'),
    (root/'checks/lean_tasks.md','checks/lean_tasks.md'),
    (root/'build.sh','build.sh'),
    (root/'formal/README.md','formal/README.md'),
    (Path('research/goal_B_all_finite_fixed_sample_extremizers.md'),'research/goal_B_all_finite_fixed_sample_extremizers.md'),
]
formal_files=[
    Path('lean-toolchain'), Path('lakefile.toml'), Path('lake-manifest.json'),
    Path('ExactHoeffding.lean'), Path('checks/goal_b_fixed_sample_axioms.lean'),
    Path('checks/full_closure_axioms.lean'),
]
formal_files.extend(sorted(Path('ExactHoeffding').glob('*.lean')))
entries.extend((path, Path('formal') / path) for path in formal_files)
(root/'SHA256SUMS.txt').write_text(''.join(
    f'{hashlib.sha256(path.read_bytes()).hexdigest()}  {Path(arcname).as_posix()}\n'
    for path,arcname in entries),encoding='utf-8')
entries.append((root/'SHA256SUMS.txt','SHA256SUMS.txt'))
archive=root/'dist/GoalB_FixedSample_FiniteN_Research_Package.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
    for path,arcname in entries:z.write(path,arcname=Path(arcname).as_posix())
print('Generated:',archive,archive.stat().st_size,'bytes')
PY
