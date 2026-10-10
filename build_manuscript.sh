#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build checks/logs
for pass in 1 2 3; do
  (cd source && pdflatex -interaction=nonstopmode -halt-on-error -output-directory=../build manuscript.tex) > "build/latex_pass_$pass.log" 2>&1
  (cd source && pdflatex -interaction=nonstopmode -halt-on-error -output-directory=../build supplement.tex) > "build/supplement_pass_$pass.log" 2>&1
done
cp build/latex_pass_3.log checks/logs/latex_build.log
cp build/supplement_pass_3.log checks/logs/supplement_build.log
for name in latex_build supplement_build; do
 if grep -E 'undefined references|undefined on input|Overfull|! LaTeX Error|multiply defined' "checks/logs/$name.log"; then
   printf 'Build check failed. See checks/logs/%s.log.\n' "$name" >&2
   exit 1
 fi
done
cp build/manuscript.pdf manuscript.pdf
cp build/supplement.pdf supplementary_refinements.pdf
for pass in 1 2; do
  (cd docs && pdflatex -interaction=nonstopmode -halt-on-error proof_certification_2026-10-11.tex) > "build/proof_certification_pass_$pass.log" 2>&1
done
cp build/proof_certification_pass_2.log checks/logs/proof_certification_build.log
if grep -E 'undefined references|undefined on input|Overfull|! LaTeX Error|multiply defined' checks/logs/proof_certification_build.log; then
  printf 'Proof certification build failed.\n' >&2
  exit 1
fi
printf 'Main manuscript and supplement compiled successfully.\n'
