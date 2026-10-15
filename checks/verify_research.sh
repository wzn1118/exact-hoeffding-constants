#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p build/tail_bounds research/tail_bounds/evidence
python3 checks/verify_piecewise_kl.py | tee research/tail_bounds/evidence/verify_piecewise_kl.log
for pass in 1 2; do
  pdflatex -no-shell-escape -halt-on-error -interaction=nonstopmode \
    -output-directory=build/tail_bounds research/tail_bounds/minimum_variance_tail.tex \
    > "build/tail_bounds/pass_${pass}.log"
done
if grep -E 'Warning|Overfull|undefined|^!' build/tail_bounds/pass_2.log; then
  exit 1
fi
cp build/tail_bounds/minimum_variance_tail.pdf research/tail_bounds/minimum_variance_tail.pdf
printf 'PASS: piecewise KL manuscript compiled without warnings\n'
