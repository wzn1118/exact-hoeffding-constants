# Lean 4 verification ledger

The manuscript's analytic claims are not automatically proved by this new repository's Lean package. The table below states the precise difference between **kernel-checked statements** and **open formalization tasks**.

| Manuscript result | Lean name / location | Status |
| --- | --- | --- |
| Quadratic finite-population margin envelope | `balance_product_bound`, `min_margin_product_bound` | Proof implemented; pending CI compilation |
| Centered singleton coefficient norm | `centered_singleton_norm` | Proof implemented; pending CI compilation |
| Zero-sum contrast projection algebra | `centerContrast_difference`, `centerContrast_fixed` | Partial; pending CI compilation |
| Nonnegative hypergeometric weights | `hypergeomMass_nonneg` | Proof implemented; pending CI compilation |
| Finite MGF normalization and shift | `finiteMGF_*` | Proof implemented; pending CI compilation |
| Bernoulli log-odds balance | `bernoulli_log_odds_balance` | Proof implemented; pending CI compilation |
| Parity-dependent variance algebra | `even_variance_formula`, `odd_variance_formula` | Proof implemented; pending CI compilation |
| Hypergeometric PMF normalization (Vandermonde) | — | Open |
| Hypergeometric mean / all-tilt variance | — | Open |
| Theorem `thm:curvature`, global tilted-variance bound | — | Open |
| Theorem `thm:main_laplace`, quadratic envelope | — | Open |
| Theorem `thm:exchange`, exact odd constant and all extremizers | — | Open |
| Exchangeability-to-hypergeometric variational identity | — | Open |

All Lean files intentionally avoid `sorry`, `admit` and auxiliary `axiom` declarations. Unformalized theorems are not given placeholder definitions that would confuse theorem provers or readers.

## Reproduce

```bash
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
lake update
lake exe cache get
lake build ExactHoeffding
lake env lean ExactHoeffding.lean
```

The Lean toolchain is pinned in `lean-toolchain` and mathlib is pinned in `lakefile.toml` to the same Lean minor version. A dedicated GitHub Actions workflow builds the entire library and disallows proof holes.

## Formalization roadmap

1. Prove Vandermonde normalization and hypergeometric factorial moments.
2. Formalize exchangeable laws on `Fin N → ℝ`, permutations and convexity reduction to Hamming slices.
3. Prove a real-rootedness or equivalent Poisson–binomial tilt representation.
4. Prove the Riccati and curvature inequalities as analytic statements with Mathlib derivatives and ODE comparison.
5. Prove the uniform quadratic Laplace envelope, strictness and the three-mass special case.
6. Deduce sharp even/odd constants and classify odd maximizers.

The main target is an end-to-end formalization of Theorem `thm:exchange`, not a numerical check of the formula. None of steps 1–6 is asserted complete by the current package.
