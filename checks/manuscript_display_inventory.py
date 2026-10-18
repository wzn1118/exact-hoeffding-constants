#!/usr/bin/env python3
"""Bind every displayed formula to frozen source and independent scope reviews.

This inventory detects omitted display blocks and source changes. Review routing
is not a declaration correspondence or proof-completeness assertion; exact
statement obligations remain in manuscript_lean_map.json.
"""
from pathlib import Path
import argparse, hashlib, json, re
ROOT = Path(__file__).resolve().parents[1]
SOURCE = 'submission/current/manuscript.tex'
OUTPUT = ROOT / 'submission/current/display_formula_inventory.json'
PATTERN = re.compile(r'\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}(.*?)\\end\{\1\}|\\\[(.*?)\\\]', re.S)

def generate():
    data = (ROOT / SOURCE).read_bytes()
    text = data.decode('utf-8')
    rows = []
    for index, match in enumerate(PATTERN.finditer(text), 1):
        line = text.count('\n', 0, match.start()) + 1
        review = 'formal_status/display_formula_audit_current_20261018.md'
        rows.append({'id': f'D{index}', 'start_line': line,
            'end_line': text.count('\n', 0, match.end()) + 1,
            'environment': match.group(1) or 'displaymath',
            'labels': re.findall(r'\\label\{([^}]+)\}', match.group()),
            'tex': match.group(),
            'sha256': hashlib.sha256(match.group().encode()).hexdigest(),
            'scope_review': review,
            'proof_status': 'consult_current_source_review_binding_and_concordance'})
    return {'source': SOURCE, 'source_sha256': hashlib.sha256(data).hexdigest(),
        'display_count': len(rows),
        'policy': 'Inventory and review routing only; no proof is certified by parsing TeX.',
        'displays': rows}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = generate()
    content = json.dumps(result, ensure_ascii=False, indent=2) + '\n'
    if args.check:
        if not OUTPUT.is_file() or OUTPUT.read_text() != content:
            raise SystemExit('Display inventory is absent or stale')
        for row in result['displays']:
            if not (ROOT / row['scope_review']).is_file():
                raise SystemExit('Missing independent scope review: ' + row['scope_review'])
    else:
        OUTPUT.write_text(content)
    print(f"PASS: all {result['display_count']} display blocks are frozen and routed to scope review")
if __name__ == '__main__':
    main()
