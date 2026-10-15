# Lean 4 development — Exact Hoeffding Constants

A Mathlib formalization of Zinan Wang's **Exact Hoeffding Constants for Finite Exchangeable Sequences**, including actual finite probability laws, exact parity constants, and their equality cases.

## Main interfaces

- `SharpCurvatureTheorem`: sharp all-tilt hypergeometric curvature for every legal population and margin, with all-parameter equality in `AllParameterCurvatureEquality`.
- `LaplaceEnvelopeTheorem`, `UniformLaplace`, `StrictUniformLaplace`: the scaled Bernoulli envelope, balanced limit, and quadratic domination.
- `OddHypergeomExtremizers`, `EvenHypergeomExtremizers`: complete classifications of the maximizing margin pairs, including all sample sizes.
- `VariationalIdentity`, `ExactParityConstants`, `ExactOddGlobalTheorem`: the actual real-cube exchangeability reduction, least valid coefficient, closed forms, and attaining margins.
- `SharpWeightedTail`: weighted concentration and zero-variance endpoints.
- `JacobiStandardNormalization`, `HypergeomBernoulliLaw`: classical Jacobi normalization and the actual tilted independent-Bernoulli representation.
- `FixedSampleGlobalExtrema`: every fixed positive sample size, all success counts, and shared finite-range thresholds.
- `JointGlobalOptimizer`, `JointOptimizedValue`: the jointly analytic unique global optimizer of the actual real-margin law near independent population and imbalance parameters, its normalized supremum value, balanced identity, and reflection.
- `ActualMomentCumulantRecursion`: all-order actual moment–cumulant recursion; `FourthOrderMainTheorem`, `ActualNormalizedFourthCoefficient` and `OptimalProxyFourthExpansion`: the same actual global optimizer, third tilt coefficient, fourth optimized-value coefficient, analytic fifth-order remainder, and fourth-order singleton gap.

The umbrella `ExactHoeffding.lean` imports the certified development. The precise manuscript coverage and verification inventory are recorded in [theorem_to_lean.csv](theorem_to_lean.csv) and [proof_gap_register.md](proof_gap_register.md).

## Reproduction

Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` are pinned by `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get
lake build ExactHoeffding
lake env lean ExactHoeffding.lean
python3 checks/generate_axiom_audit.py --check
lake env lean checks/full_closure_axioms.lean > lean_axioms.log
python3 checks/check_axiom_output.py lean_axioms.log
```

The `Lean 4 proof kernel` workflow reproduces these checks. The generated audit covers every public theorem in the actual umbrella import closure and checks its complete transitive axiom dependencies. The integrated 15 October checkpoint verifies **1450 public theorems in 239 project modules**; the reported dependencies are `propext`, `Classical.choice`, and `Quot.sound`. Evidence is retained in `checks/logs/full_closure/integrated_compact_umbrella_audit.log`.

Copyright © 2026 Zinan Wang. Original source and documentation are governed by the repository's rights notices.
