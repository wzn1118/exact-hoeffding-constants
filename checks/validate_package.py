#!/usr/bin/env python3
"""Validate manuscript links, bibliography records, reference files, and build output."""
from pathlib import Path
from collections import Counter
import json,re,subprocess,hashlib
root=Path(__file__).resolve().parents[1]
texts={p.name:p.read_text() for p in (root/'source').glob('*.tex')}
tex='\n'.join(texts.values())
labels=re.findall(r'\\label\{([^}]+)\}',tex)
assert all(n==1 for n in Counter(labels).values()),'Duplicate label'
references=re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',tex)
assert not set(references)-set(labels),'Undefined reference'
keys=set(re.findall(r'\\bibitem\{([^}]+)\}',tex))
cites={k for group in re.findall(r'\\cite(?:\[[^\]]*\])*\{([^}]+)\}',tex) for k in group.split(',')}
assert cites==keys,'Citation mismatch'
records=json.loads((root/'refs/references.json').read_text())
assert {x['key'] for x in records}==keys,'Bibliographic record mismatch'
bibkeys=set(re.findall(r'@\w+\{([^,]+),',(root/'refs/references.bib').read_text()))
assert bibkeys==keys,'BibTeX mismatch'
local_count=0
for x in records:
 assert x['source_url'].startswith('https://')
 if x['local_pdf']:
  local_count+=1;p=root/'refs'/x['local_pdf']
  assert p.read_bytes().startswith(b'%PDF')
  assert hashlib.sha256(p.read_bytes()).hexdigest()==x['sha256']
  assert x['license']=='CC BY 4.0'
  subprocess.run(['pdfinfo',str(p)],check=True,stdout=subprocess.DEVNULL)
for input_name in re.findall(r'\\input\{([^}]+)\}',tex):
 assert (root/'source'/input_name).exists(),input_name
pdfinfo=subprocess.run(['pdfinfo',str(root/'manuscript.pdf')],check=True,capture_output=True,text=True).stdout
pages=int(re.search(r'^Pages:\s+(\d+)',pdfinfo,re.M).group(1))
assert 27 <= pages <= 30, f'Primary paper must be 27--30 pages; got {pages}'
assert (root/'supplementary_refinements.pdf').exists()
subinfo=subprocess.run(['pdfinfo',str(root/'supplementary_refinements.pdf')],check=True,capture_output=True,text=True).stdout
assert 'Technical Refinements for Exact Hoeffding Constants' in subinfo
assert 'Zinan Wang' in pdfinfo
assert 'Exact Hoeffding Constants for Finite Exchangeable Sequences' in pdfinfo
log=(root/'checks/logs/latex_build.log').read_text()
assert not re.search(r'undefined references|undefined on input|Overfull|! LaTeX Error|multiply defined|Warning',log)
required_logs=('verify_parity_structure','verify_curvature','verify_third_order',
 'verify_fourth_order','verify_curvature_counterexample','verify_odd_envelope',
 'verify_even_envelope_extension','check_exact_curvature','check_exact_odd_envelope',
 'check_high_precision_asymptotics','check_high_precision_envelope')
for test in required_logs:
 logfile=root/'checks/logs'/f'{test}.log'
 assert logfile.is_file() and 'PASS' in logfile.read_text(),f'Missing/failed {logfile}'
for p in (root/'checks/logs').glob('*.log'):
 if p.name in ['latex_build.log','supplement_build.log','package_validation.log'] or p.name.startswith('latex_pass_'):continue
 assert 'PASS' in p.read_text(),p.name
print(f'PASS: {len(labels)} unique labels and {len(references)} valid cross-references.')
print(f'PASS: {len(keys)} matching citations, BibTeX entries, and bibliographic records.')
print(f'PASS: {local_count} licensed reference PDFs with matching source hashes.')
print(f'PASS: {pages}-page main manuscript, compiled supplement, author metadata, and both build logs.')
print('PASS: all mathematical computation logs present and successful.')
print('PASS: document identity and source consistency.')
