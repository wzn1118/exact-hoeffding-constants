#!/usr/bin/env python3
"""Require an audited result for every theorem and only standard Lean axioms."""
from pathlib import Path
import re
import sys

root = Path(__file__).resolve().parents[1]
expected = set(re.findall(r'^#print axioms (\S+)',
                         (root / 'checks/full_closure_axioms.lean').read_text(), re.M))
text = Path(sys.argv[1]).read_text()
if re.search(r'\berror:|sorryAx|Lean\.ofReduceBool|native_decide', text):
    raise SystemExit('Failed theorem audit or disallowed dependency')
actual = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
    actual[name] = {x.strip() for x in axioms.split(',') if x.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    actual[name] = set()
if expected != set(actual):
    raise SystemExit(f'Audit coverage mismatch: missing={sorted(expected - set(actual))}; '
                     f'extra={sorted(set(actual) - expected)}')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
bad = {name: sorted(axioms - allowed) for name, axioms in actual.items() if axioms - allowed}
if bad:
    raise SystemExit(f'Unexpected axiom dependencies: {bad}')
print(f'PASS: {len(actual)} public theorems; only propext, Classical.choice, Quot.sound')
