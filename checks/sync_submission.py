#!/usr/bin/env python3
"""Produce a single-file submission/manuscript.tex from the modular LaTeX source."""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[1]
src=root/'source'
pattern=re.compile(r'(?m)^\\input\{([A-Za-z0-9_-]+)\.tex\}\s*$')
def expand(source,chain):
    def repl(match):
        name=match.group(1)+'.tex'
        if name in chain:
            raise RuntimeError('Circular TeX include: '+' -> '.join(chain+[name]))
        path=src/name
        if not path.is_file():
            raise FileNotFoundError(path)
        return '\n% begin '+name+'\n'+expand(path.read_text(),chain+[name])+'\n% end '+name+'\n'
    return pattern.sub(repl,source)
output=root/'submission/manuscript.tex'
output.parent.mkdir(exist_ok=True)
output.write_text(expand((src/'manuscript.tex').read_text(),['manuscript.tex']))
assert not pattern.search(output.read_text())
print(f'PASS: regenerated standalone submission source ({output.stat().st_size} bytes)')
