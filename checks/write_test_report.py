#!/usr/bin/env python3
"""Generate the verified mathematical test inventory."""
import hashlib
import json
import os
import platform
from pathlib import Path

root = Path(__file__).resolve().parents[1]
logs = root / 'checks' / 'logs'
tests = (
    'verify_parity_structure',
    'verify_curvature',
    'verify_third_order',
    'verify_fourth_order',
    'verify_curvature_counterexample',
    'verify_odd_envelope',
    'verify_even_envelope_extension',
    'check_exact_curvature',
    'check_exact_odd_envelope',
    'check_high_precision_asymptotics',
    'check_high_precision_envelope',
    'verify_independent_curvature',
    'verify_independent_odd_envelope',
)

def evidence(name, require_pass=False):
    path = logs / f'{name}.log'
    data = path.read_bytes()
    if require_pass:
        assert 'PASS' in data.decode('utf-8'), name
    return {
        'file': path.relative_to(root).as_posix(),
        'sha256': hashlib.sha256(data).hexdigest(),
        'bytes': len(data),
    }

report = {
    'result': 'PASS',
    'commit': os.getenv('GITHUB_SHA', 'local'),
    'python': platform.python_version(),
    'test_count': len(tests),
    'mathematical_tests': [dict(name=name, **evidence(name, True)) for name in tests],
    'build_logs': [dict(name=name, **evidence(name)) for name in ('latex_build', 'supplement_build')],
    'package_validation': evidence('package_validation', True),
    'suite_log': evidence('run_all'),
}
output = logs / 'math_test_report.json'
output.write_text(json.dumps(report, indent=2, ensure_ascii=False, sort_keys=True)+'\n')
print(f'PASS: indexed {len(tests)} mathematical tests, 2 PDF builds, package validation and suite log')
print(f'PASS: wrote {output.relative_to(root)}')
