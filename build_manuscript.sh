#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build checks/logs
for pass in 1 2 3; do
  (cd source && pdflatex -interaction=nonstopmode -halt-on-error -output-directory=../build manuscript.tex) > "build/latex_pass_$pass.log" 2>&1
done
cp build/latex_pass_3.log checks/logs/latex_build.log
if grep -E 'undefined references|undefined on input|Overfull|! LaTeX Error|multiply defined' checks/logs/latex_build.log; then
  printf 'Build check failed. See checks/logs/latex_build.log.\n' >&2
  exit 1
fi
cp build/manuscript.pdf manuscript.pdf
printf 'Manuscript compiled successfully.\n'
