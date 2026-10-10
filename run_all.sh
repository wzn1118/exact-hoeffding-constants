#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
PYTHON_BIN="${PYTHON_BIN:-python3}"
mkdir -p checks/logs build
scripts=(verify_parity_structure verify_curvature verify_third_order verify_fourth_order verify_curvature_counterexample verify_odd_envelope verify_even_envelope_extension check_exact_curvature check_exact_odd_envelope check_high_precision_asymptotics check_high_precision_envelope)
for name in "${scripts[@]}"; do
  printf '\n== %s ==\n' "$name"
  "$PYTHON_BIN" "checks/$name.py" | tee "checks/logs/$name.log"
done
bash build_manuscript.sh
"$PYTHON_BIN" checks/validate_package.py | tee checks/logs/package_validation.log
printf '\nAll computations and manuscript build completed.\n'
