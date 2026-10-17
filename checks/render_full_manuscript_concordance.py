#!/usr/bin/env python3
"""Render the checked JSON theorem map as a reviewer-readable concordance."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / 'checks/manuscript_lean_map.json').read_text())

MANUSCRIPT = ROOT / 'submission/integrated/combined_manuscript.tex'
if not MANUSCRIPT.exists():
    MANUSCRIPT = ROOT / 'submission/current/manuscript.tex'
source = MANUSCRIPT.read_text(encoding='utf-8')
import re
locations = {}
pattern = re.compile(r"\\begin\{(theorem|lemma|proposition|corollary)\}(?:\[(.*?)\])?(.*?)\\end\{\1\}", re.S)
for match in pattern.finditer(source):
    kind, title, body = match.groups()
    label = re.search(r"\\label\{([^}]+)\}", body)
    name = label.group(1) if label else 'unlabeled:' + re.sub(r'\s+', ' ', title or '').strip()
    locations[name] = source.count('\n', 0, match.start()) + 1
for name, marker in {
    'extra:A3-four-binomial-KL': r'\subsubsection{Four binomial KL bounds}',
    'extra:A4-Bennett-Bernstein': r'\subsubsection{Exact-variance Bennett and Bernstein bounds}',
}.items():
    offset = source.find(marker)
    if offset < 0: raise RuntimeError('Missing supplementary claim section: ' + name)
    locations[name] = source.count('\n', 0, offset) + 1

out = [
    '# Unified manuscript theorem–Lean concordance',
    '',
    'This register maps theorem-class environments in the current integrated manuscript to Lean declarations. The automated gate checks environment keys, titles, kinds, source declarations, and axiom-audit coverage; matching mathematical hypotheses and full prose semantics require independent review.',
    '',
    f"The parser found **{sum(r.get('paper_environment', False) for r in data['results'])} theorem-class environments** and this map separately records **{sum(not r.get('paper_environment', False) for r in data['results'])} supplementary formal claims** (the four-KL and Bennett/Bernstein comparisons are equations/prose, not theorem environments). The exact theorem names are checked against `checks/full_closure_axioms.lean`; a `Complete` row must name an existing declaration, source file, and `#print axioms` entry. The gate fails while any row is `Partial`.",
    '',
    '| # | Paper location / result | Lean declaration(s) and source | Scope and correspondence | Kernel/audit status |',
    '|---:|---|---|---|---|',
]
for r in data['results']:
    decls = '<br>'.join(f"`{d['name']}` — `{d['file']}`" for d in r.get('declarations', [])) or '—'
    if r['status'] == 'Complete':
        audit = 'Declaration and axiom-gate verified; correspondence requires theorem-specific review'
    else:
        audit = f"**{r['status']}** — {r['gap']}"
    loc = f"L{locations[r['key']]}: `{r['key']}` — {r['title']}"
    out.append(f"| {r['index']} | {loc} | {decls} | {r['coverage']} | {audit} |")
out += [
    '',
    '## Build and audit policy',
    '',
    '`checks/check_full_manuscript_concordance.py` reparses the current manuscript, compares theorem environment keys, kinds and titles with this register, and rejects missing declaration names, missing source paths or non-Complete results. Listed line numbers are descriptive navigation aids, not proof checks; the script does not establish semantic equivalence of every displayed equation or prose deduction. `checks/full_closure_axioms.lean` is the generated public theorem audit input. The permitted audit axioms remain the repository policy: `propext`, `Classical.choice`, and `Quot.sound`.',
    '',
    'This concordance is a coverage register, not evidence that a partial item is closed. No item is marked Complete merely because a nearby lemma or a theorem with a similar name exists.',
    ''
]
(ROOT / 'submission/current/theorem_lean_concordance.md').write_text('\n'.join(out))
