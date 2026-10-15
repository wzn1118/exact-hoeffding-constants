#!/usr/bin/env python3
"""Check all named manuscript results against the imported Lean declarations."""
from pathlib import Path
import re
from generate_axiom_audit import generate

root = Path(__file__).resolve().parents[1]
labels = set()
for path in (root / 'source').glob('*.tex'):
    source = path.read_text()
    for match in re.finditer(r'\\begin\{(?:theorem|lemma|proposition|corollary)\}(?:\[[^\]]*\])?\s*\\label\{([^}]+)\}', source):
        if match[1] in labels:
            raise SystemExit('Duplicate named result: ' + match[1])
        labels.add(match[1])
text = (root / 'formal_status/manuscript_concordance.md').read_text()
rows = {}
for line in text.splitlines():
    if not re.match(r'^\| \d+ \|', line):
        continue
    fields = line.split('|')
    key = re.fullmatch(r'`([^`]+)`', fields[2].strip())
    if not key or key[1] in rows:
        raise SystemExit('Malformed or duplicate concordance row: ' + line)
    rows[key[1]] = (fields[3], fields[4])
if set(rows) != labels:
    raise SystemExit(f'Coverage mismatch: missing={sorted(labels-set(rows))}; extra={sorted(set(rows)-labels)}')
audit, _, _ = generate()
proved = set(re.findall(r'^#print axioms ExactHoeffding\.(\S+)', audit, re.M))
for label, (declarations, status) in rows.items():
    if not status.strip().startswith('Complete'):
        raise SystemExit('Uncompleted named result: ' + label)
    cited = [name for name in re.findall(r'`([^`]+)`', declarations) if name in proved]
    if not cited:
        raise SystemExit('No imported public theorem for ' + label)
    for name in re.findall(r'`([^`]+)`', declarations):
        if '_' in name and name not in proved:
            raise SystemExit(f'Unimported or misspelled theorem: {label}: {name}')
print(f'PASS: all {len(labels)} named manuscript results have complete concordance rows and imported public Lean theorem references')
