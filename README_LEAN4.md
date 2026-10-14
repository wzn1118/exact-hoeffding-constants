# Lean 4 development — Exact Hoeffding Constants

A Mathlib-backed formalization accompanying Zinan Wang's 2026 probability manuscript **Exact Hoeffding Constants for Finite Exchangeable Sequences**. The source code follows the manuscript's finite-population hypergeometric reduction and precise odd/even variance analysis.

## Structure

- `ExactHoeffding/Basic.lean`: quadratic finite-population algebra.
- `ExactHoeffding/Contrasts.lean`: zero-sum contrasts and centering.
- `ExactHoeffding/Hypergeometric.lean`: combinatorial sample masses.
- `ExactHoeffding/Normalization.lean`: Vandermonde normalization, exact single-draw masses and MGF at zero.
- `ExactHoeffding/Laplace.lean`: finite MGFs and a Bernoulli log-odds identity.
- `ExactHoeffding/Sampling.lean`: one-draw hypergeometric/Bernoulli MGF identification and centering.
- `ExactHoeffding/SharpExample.lean`: nonzero-tilt exact candidate and quadratic saturation.
- `ExactHoeffding/Parity.lean`: even/odd normalized variance expressions.
- `ExactHoeffding/CurvatureBridge.lean`: abstract curvature-to-Laplace theorem via global convexity.
- `ExactHoeffding/MomentGenerating.lean`: first and second derivatives of finite moment-generating functions.
- `ExactHoeffding/FactorialMoments.lean`: all-parameter first and second hypergeometric factorial-moment convolution identities.
- `ExactHoeffding/OrdinaryMoments.lean`: normalized hypergeometric expectation for positive sample/success margins.
- `ExactHoeffding/TiltedVariance.lean`: exact all-tilt log-Laplace second derivative as a normalized central moment.
- `ExactHoeffding/CurvatureNonnegative.lean`: finite Cauchy–Schwarz and nonnegative log-Laplace curvature.

The umbrella file `ExactHoeffding.lean` imports the complete source library. Toolchain: Lean 4 v4.33.0 + matching Mathlib. The committed `lake-manifest.json` locks dependency revisions.

The research extension adds `PoissonBinomial.lean` (finite variance algebra),
`VarianceComparison.lean` (symmetry-envelope comparisons), and
`Chernoff.lean` (finite exponential Markov). The full library and thirteen
selected axiom audits have been checked locally; evidence is in
`research/tail_bounds/evidence/`. Run `lake env lean checks/lean_axioms.lean`
to reproduce the axiom inspection.

## Build and check

```bash
lake exe cache get
lake build ExactHoeffding
lake env lean ExactHoeffding.lean
```

The `Lean 4 proof kernel` GitHub Actions workflow executes the build and scans for unsound proof placeholders.

## Scope of certification

The package establishes genuine combinatorial identities, first and second factorial moments, normalized expectation, exact all-tilt variance identities, nonnegative curvature, the exact odd-population single-coordinate **lower-bound equality**, and an abstract implication from a sharp upper-curvature certificate to a quadratic Laplace inequality.

**Baseline CI success:** [Lean kernel #38606516354](https://github.com/wzn1118/exact-hoeffding-constants/actions/runs/38606516354), commit `ebf534362f596175a24fc33e9eebc1cd4145349f`. Research-branch CI is checked separately for its own commit.

**Research CI success:** [Lean kernel #38620327901](https://github.com/wzn1118/exact-hoeffding-constants/actions/runs/38620327901), commit `167b616e44815440732c86af7c471a5af56f14a3`; the corresponding analytic research run `38620327863` also succeeds. The work is reviewed in draft PR 5.

**The complete sharp constant theorem is not yet formalized.** In particular, the global tilted-variance curvature inequality, uniform Riccati/Laplace barrier, all odd extremizers, and the exchangeability-to-hypergeometric variational reduction remain open formalization obligations. The repository maintains an explicit theorem-by-theorem status table in `LEAN_PROOF_STATUS.md` and does not treat Python test passes as Lean proofs.
