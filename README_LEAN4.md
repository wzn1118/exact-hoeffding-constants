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

The umbrella file `ExactHoeffding.lean` imports the complete source library. Toolchain: Lean 4 v4.33.0 + matching Mathlib.

## Build and check

```bash
lake update
lake exe cache get
lake build ExactHoeffding
lake env lean ExactHoeffding.lean
```

The `Lean 4 proof kernel` GitHub Actions workflow executes the build and scans for unsound proof placeholders.

## Scope of certification

The package establishes genuine combinatorial identities, normalized finite probabilities, the exact odd-population single-coordinate **lower-bound equality**, and an abstract implication from a second-derivative certificate to a quadratic Laplace inequality.

**The complete sharp constant theorem is not yet formalized.** In particular, the global tilted-variance curvature inequality, uniform Riccati/Laplace barrier, all odd extremizers, and the exchangeability-to-hypergeometric variational reduction remain open formalization obligations. The repository maintains an explicit theorem-by-theorem status table in `LEAN_PROOF_STATUS.md` and does not treat Python test passes as Lean proofs.
