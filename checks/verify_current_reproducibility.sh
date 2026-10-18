#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

for tool in python3 sha256sum lake latexmk pdfinfo; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    printf 'Missing required command: %s\n' "$tool" >&2
    exit 2
  fi
done

sha256sum -c SHA256SUMS.txt
python3 checks/verify_reproducibility_bundle.py
python3 checks/manuscript_display_inventory.py --check
python3 checks/check_display_formula_review_binding.py
python3 checks/check_semantic_contract_integrity.py --require-contracts
python3 checks/check_theorem_manifest.py --check
python3 checks/generate_axiom_audit.py --check
python3 checks/verify_piecewise_kl.py
python3 goal_b/code/verify_goal_b.py --maxN 60 --numericN 18 \
  --output "${TMPDIR:-/tmp}/exact-hoeffding-goal-b-verification.json"

lake exe cache get
lake build ExactHoeffding
python3 checks/check_full_manuscript_concordance.py

python3 submission/integrated/build_clean_submission.py
(cd submission/integrated && latexmk -pdf -interaction=nonstopmode -halt-on-error combined_manuscript.tex)
test -s submission/integrated/combined_manuscript.pdf
pages="$(pdfinfo submission/integrated/combined_manuscript.pdf | awk '/^Pages:/ {print $2}')"
test "$pages" -eq 37
printf 'PASS: standalone current manuscript, Lean proof, and numerical verification (%s pages).\n' "$pages"
