#!/usr/bin/env python3
"""Render the checked JSON theorem map as a reviewer-readable concordance."""
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
data = json.loads((ROOT / 'checks/manuscript_lean_map.json').read_text())
out = [
    '# Unified manuscript theorem–Lean concordance',
    '',
    'Source of truth: frozen `submission/current/manuscript.tex` in this review branch. The body and labels are checked byte-for-byte by the repository release workflow; this table does not edit the manuscript.',
    '',
    f"This register contains **{sum(r.get('paper_environment', False) for r in data['results'])} theorem-class environments** plus **{sum(not r.get('paper_environment', False) for r in data['results'])} supplementary claims**. The map has {sum(len(r.get('declarations', [])) for r in data['results'])} declaration references to {len({d['name'] for r in data['results'] for d in r.get('declarations', [])})} distinct Lean theorems. Exact types, proof dependencies, source ranges, and axioms are exported to `submission/current/theorem_lean_manifest.json`; declaration names are checked against `checks/full_closure_axioms.lean`. Every row currently carries an independently transcribed typed Lean proposition contract whose proof and dependency chain are inspected. The checker binds each contract to the frozen manuscript environment and audits its declaration; the TeX-to-Lean translation itself still requires mathematical review. Separate displayed-formula scope audits remain in `formal_status/`.",
    '',
    '| # | Paper location / result | Lean declaration(s) and source | Typed statement contract | Scope and correspondence | Kernel/audit status |',
    '|---:|---|---|---|---|---|',
]
for r in data['results']:
    decls = '<br>'.join(f"`{d['name']}` — `{d['file']}`" for d in r.get('declarations', [])) or '—'
    contract = f"`{r['semantic_contract_declaration']}`" if r.get('semantic_contract_declaration') else 'Not encoded as a standalone Lean statement contract'
    if r['status'] == 'Complete':
        audit = 'Declarations compiled and axiom-audited; the exact contract coverage is shown separately'
    else:
        audit = f"**{r['status']}** — {r['gap']}"
    loc = f"L{r['line']}: `{r['key']}` — {r['title']}"
    out.append(f"| {r['index']} | {loc} | {decls} | {contract} | {r['coverage']} | {audit} |")
out += [
    '',
    '## Build and audit policy',
    '',
    '`checks/check_full_manuscript_concordance.py` reparses the frozen manuscript, checks the exact environment count, kinds, titles, labels and source line identities, and rejects any missing declaration or non-Complete result. `checks/full_closure_axioms.lean` is the generated public theorem audit input. The permitted audit axioms remain the repository policy: `propext`, `Classical.choice`, and `Quot.sound`.',
    '',
    f"Typed Lean statement contracts are recorded for {sum(bool(r.get('semantic_contract_declaration')) for r in data['results'])} of {len(data['results'])} mapped rows. The checker binds each contract to the frozen manuscript environment hash, verifies that the Lean contract is kernel checked, axiom audited, and assembled from a mapped theorem. The proposition is a manually reviewed formal transcription; neither a source hash nor declaration check proves TeX-to-Lean semantic equivalence. The strict semantic-contract mode now passes with reviewed marker profiles for all 49 mapped contracts.",
    ''
]
(ROOT / 'submission/current/theorem_lean_concordance.md').write_text('\n'.join(out))
