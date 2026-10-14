# Lean 4 formal verification — Exact Hoeffding Constants

This is a Mathlib-backed Lean 4 subproject for the paper **Exact Hoeffding Constants for Finite Exchangeable Sequences** (Zinan Wang, 2026).

The first modules mechanize selected exact combinatorial and analytic-algebraic identities needed for the main proof, with one source module for each mathematical ingredient. All demonstrated theorem statements have real proof terms. There are no admitted results and no fabricated kernel attestations.

## Modules

- `ExactHoeffding/Basic.lean`: centered quadratic identities, balanced margin inequality, Bernoulli variance ceiling.
- `ExactHoeffding/Contrasts.lean`: contrast centering and translation invariance.
- `ExactHoeffding/Hypergeometric.lean`: finite combinatorial probability weights and generating polynomial.
- `ExactHoeffding/Laplace.lean`: finite exponential moments and Bernoulli log-odds identity.
- `ExactHoeffding/Parity.lean`: exact even/odd normalized variance algebra.
- `ExactHoeffding.lean`: library umbrella import.

## Run locally

Install Lean's elan toolchain manager, then from the repository root:

```bash
lake update
lake exe cache get
lake build ExactHoeffding
lake env lean ExactHoeffding.lean
```

## Verification coverage

Refer to `LEAN_PROOF_STATUS.md` before citing this formalization. The full sharp constant, Riccati curvature theorem and uniform hypergeometric envelope are **not currently Lean-proved**. Building this library certifies only declarations actually present in its source files.
