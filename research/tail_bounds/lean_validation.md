# Piecewise KL proof validation

Date: 2026-10-16. Toolchain: Lean 4.33.0, repository-pinned mathlib.

The assembly `hypergeom_piecewise_kl_end_to_end` covers the exact canonical
parameter domain of the piecewise-rate theorem. It combines the finite
hypergeometric probability law, the two analytic variance envelopes, the
closed three-branch rate, both one-sided tail inequalities and the strict
rate comparisons. The support endpoints are part of the statement.

The proof of the exterior branches follows a scaled Bernoulli Riccati
trajectory to a contact mean and continues along a translated ordinary
Bernoulli trajectory. Ordered initial means are handled by an integrating
factor. A positive log-Laplace gap at the first contact is retained along the
second trajectory. Signed Fenchel comparisons carry that fixed positive gap
to each support endpoint.

Proof reproduction:

```sh
lake build ExactHoeffding
python3 checks/generate_axiom_audit.py --check
python3 checks/check_manuscript_concordance.py
lake env lean checks/full_closure_axioms.lean > full_closure_axioms.log
python3 checks/check_axiom_output.py full_closure_axioms.log
python3 checks/verify_piecewise_kl.py
```

The focused audit `checks/piecewise_kl_full_axioms.lean` lists the public
results in `PiecewiseKLFull`, `PiecewiseKLComparison` and `PiecewiseKLStrict`.
The full audit covers their entire imported project closure.

## Numerical reproduction

`checks/verify_piecewise_kl.py` passes all 292 frozen parameter/threshold
checks at 70 decimal digits, both endpoint integral checks, four symmetry KL
comparisons, uniform quadratic comparisons, and the Bennett/Bernstein checks.
Matrix SHA-256: `b8ecfb7f7eed07026f5004f0359b5f1f7b6a749d490919e60f1127c67a4f8c32`.

## Kernel build

`lake build ExactHoeffding` succeeds: 3,379 build tasks, including the
actual `hypergeom_piecewise_kl_end_to_end` declaration. The main paper
validator also passes all citation, cross-reference, reference-PDF hash
and compiled-document identity checks.

## Axiom audit

The complete imported closure audit passes for 1,637 public theorems in
258 project modules. Every dependency is contained in
`{propext, Classical.choice, Quot.sound}`. The source scan covers all 259
project Lean files and rejects `sorry`, `admit` and new `axiom` declarations.
Full logs: `checks/logs/full_closure/piecewise_kl_end_to_end_build.log` and
`checks/logs/full_closure/piecewise_kl_end_to_end_axioms.log`.
