#!/usr/bin/env python3
"""Reject loss of existing core proof sources and changes to frozen inputs."""
from pathlib import Path
import hashlib, json, subprocess
ROOT = Path(__file__).resolve().parents[1]
CORE_BASE = '8b75977b138205c4ba402000b25d226d55994682'
PAPER_SOURCE_COMMIT = '91719272750df6103358d8daccc4de8526a0d101'
PAPER_SOURCE_SHA256 = '617cce1f87272bd5d5d58e3d91342bba658bb490cb901643fb9436ecc6e2894b'

def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)

def main():
    files = git('ls-tree', '-r', '--name-only', CORE_BASE, '--', 'ExactHoeffding/').decode().splitlines()
    files = [file for file in files if file.endswith('.lean')]
    missing = [file for file in files if not (ROOT/file).is_file()]
    removed = []
    for file in files:
        patch = git('diff', '--no-ext-diff', '--unified=0', CORE_BASE, '--', file).decode()
        removed.extend({'file': file, 'line': line[1:]} for line in patch.splitlines()
                       if line.startswith('-') and not line.startswith('---'))
    frozen_dependencies = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']
    changed_dependencies = [
        file for file in frozen_dependencies
        if (ROOT/file).read_bytes() != git('show', f'{CORE_BASE}:{file}')
    ]
    paper_bytes = (ROOT/'submission/current/manuscript.tex').read_bytes()
    paper_sha256 = hashlib.sha256(paper_bytes).hexdigest()
    paper_changed = paper_sha256 != PAPER_SOURCE_SHA256
    if missing or removed or changed_dependencies or paper_changed:
        raise SystemExit(json.dumps({
            'missing': missing,
            'removed': removed,
            'changed_dependencies': changed_dependencies,
            'paper_source_commit': PAPER_SOURCE_COMMIT,
            'expected_paper_sha256': PAPER_SOURCE_SHA256,
            'actual_paper_sha256': paper_sha256,
            'paper_changed': paper_changed,
        }, ensure_ascii=False, indent=2))
    print(
        f'PASS: all {len(files)} existing mathematical modules retained; no old source lines removed; '
        f'Lean dependencies match {CORE_BASE}; paper matches GitHub main {PAPER_SOURCE_COMMIT}'
    )
if __name__ == '__main__':
    main()
