#!/usr/bin/env python3
"""Render the checked JSON theorem map as a reviewer-readable concordance."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / 'checks/manuscript_lean_map.json').read_text())
out = [
    '# Unified manuscript theorem–Lean concordance',
    '',
    'Source of truth: frozen `submission/current/manuscript.tex` on current `main`. The body and labels are checked byte-for-byte by the repository release workflow; this table does not edit the manuscript.',
    '',
    f"The parser found **{sum(r.get('paper_environment', False) for r in data['results'])} theorem-class environments** and this map separately records **{sum(not r.get('paper_environment', False) for r in data['results'])} supplementary formal claims** (the four-KL and Bennett/Bernstein comparisons are equations/prose, not theorem environments). The exact theorem names are checked against `checks/full_closure_axioms.lean`; a `Complete` row must name an existing declaration, source file, and `#print axioms` entry. The gate fails while any row is `Partial`.",
    '',
    '| # | Paper location / result | Lean declaration(s) and source | Scope and correspondence | Kernel/audit status |',
    '|---:|---|---|---|---|',
]
for r in data['results']:
    decls = '<br>'.join(f"`{d['name']}` — `{d['file']}`" for d in r.get('declarations', [])) or '—'
    if r['status'] == 'Complete':
        audit = 'Complete in baseline audit; exact type and source checked'
    else:
        audit = f"**{r['status']}** — {r['gap']}"
    loc = f"L{r['line']}: `{r['key']}` — {r['title']}"
    out.append(f"| {r['index']} | {loc} | {decls} | {r['coverage']} | {audit} |")
out += [
    '',
    '## Build and audit policy',
    '',
    '`checks/check_full_manuscript_concordance.py` reparses the frozen manuscript, checks the exact environment count, kinds, titles, labels and source line identities, and rejects any missing declaration or non-Complete result. `checks/full_closure_axioms.lean` is the generated public theorem audit input. The permitted audit axioms remain the repository policy: `propext`, `Classical.choice`, and `Quot.sound`.',
    '',
    'This concordance is a coverage register, not evidence that a partial item is closed. No item is marked Complete merely because a nearby lemma or a theorem with a similar name exists.',
    ''
]
(ROOT / 'submission/current/theorem_lean_concordance.md').write_text('\n'.join(out))
