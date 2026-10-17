# Lean 4 formalization — Sharp Hypergeometric Concentration

**Zinan Wang** — The University of Manchester  
**Xinhao Yang** — University of Southern California

The Lean 4 development formalizes the principal results of the Main+A+B manuscript, including sharp exchangeability constants, finite-sample extremizers and piecewise KL concentration bounds.

## Mathematical interfaces

- **Exact constants:** `ExactParityConstants`, `ExactOddGlobalTheorem`, `VariationalIdentity`, `SharpCurvatureTheorem` and `LaplaceEnvelopeTheorem` establish the parity-sharp coefficient and its equality cases for actual finite exchangeable laws.
- **Fixed-sample extremizers:** `GoalBFixedSample`, `GoalBIndividualMargin`, `GoalBOddVariation` and `OddCentralStrict` cover every admissible fixed sample size, the central maximizing counts, quantitative off-center gaps and odd-population variational formulas.
- **Piecewise KL bounds:** `PiecewiseKLStrict` assembles the actual finite-mass upper and lower tails and sharp rate comparisons. `PiecewiseKLFourRates`, `HypergeomBennettBernstein`, `BernsteinKernel` and `ManuscriptIntegerTails` establish the additional comparisons and integer thresholds.
- **Finite-support and factorial methods:** `FiniteSupportMeanEnvelope`, `FiniteSupportTiltCurveOfLaw`, `FiniteSupportChernoffEnvelope` and `FactorialChernoffExact` give generic integral envelopes, actual finite-law interfaces and factorial-moment Chernoff comparisons.
- **Analytic expansions:** `FourthOrderMainTheorem`, `OptimalProxyFourthExpansion`, `JointGlobalOptimizer` and `ActualMomentCumulantRecursion` formalize the optimizer, cumulants and asymptotic coefficients stated in the manuscript.

The umbrella file [`ExactHoeffding.lean`](ExactHoeffding.lean) imports the mathematical development. The project contains **281 core Lean files** (280 modules and the umbrella), plus **21 audit files and one historical checker**, giving **303 tracked Lean files**.

## Reproduce the kernel verification

The project pins Lean 4.33.0 and Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d` through `lean-toolchain` and `lake-manifest.json`.

```bash
lake exe cache get
lake build ExactHoeffding
lake env lean ExactHoeffding.lean
python3 checks/generate_axiom_audit.py --check
python3 checks/check_full_manuscript_concordance.py
lake env lean checks/full_closure_axioms.lean > lean_axioms.log
python3 checks/check_axiom_output.py lean_axioms.log
```

The latest completed audit covers **1,723 public theorems in 280 imported project modules**. Their axiom dependencies lie in `propext`, `Classical.choice` and `Quot.sound`. The current [GitHub Actions Lean workflow](.github/workflows/lean4.yml) executes the build and audit.

[Current 36-page manuscript](submission/current/manuscript.pdf) · [Theorem–Lean concordance](submission/current/theorem_lean_concordance.md) · [Complete reproducibility archive](submission/current/complete-reproducibility.zip) · [Theorem index](theorem_to_lean.csv)

Copyright © 2026 Zinan Wang. See [license](LICENSE) and [third-party notices](THIRD_PARTY_NOTICES.md).
