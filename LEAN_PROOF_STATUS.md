# Lean 4 proof coverage and mathematical audit

Paper: **Exact Hoeffding Constants for Finite Exchangeable Sequences** (Zinan Wang, 2026).

**Certification rule.** A mathematical result is recorded as proved only if a Lean declaration with the same mathematical content has a proof term accepted by the Lean 4 kernel on the referenced commit. A successful build of a subset is *not* an end-to-end formal proof of the manuscript. This ledger is intentionally explicit about open theorems.

## Verified mathematical ingredients

| Paper ingredient | Lean declarations | Scope |
| --- | --- | --- |
| Quadratic margin ceiling; Bernoulli variance ceiling | `balance_product_bound`, `min_margin_product_bound`, `bernoulli_variance_bound` | All real parameters |
| Centered contrast algebra | `centerContrast_difference`, `centerContrast_fixed` | Finite real coefficient vectors |
| Hypergeometric nonnegative mass | `hypergeomMass_nonneg` | Finite discrete masses |
| Exact Vandermonde sum | `hypergeomCount_total` | Every `k ≤ N`, any draw index `m` |
| Hypergeometric PMF normalization | `hypergeomMass_total` | Every `k,m ≤ N` |
| Hypergeometric MGF at zero and nonnegativity | `hypergeomMGF_zero`, `hypergeomMGF_nonneg` | All valid parameters |
| Single-draw hypergeometric masses | `hypergeomMass_one_success`, `hypergeomMass_one_failure_complement` | Exact finite populations |
| Finite MGF shift and normalization | `finiteMGF_shift`, `finiteMGF_zero_of_normalized` | Finite weights |
| Bernoulli log-odds equality | `bernoulli_log_odds_balance`, `bernoulli_centered_log_odds_equality` | Nondegenerate Bernoulli parameters |
| Odd-population single-coordinate candidate equality | `singleton_odd_log_mgf_certificate`, `singleton_odd_quadratic_saturation` | Every real population parameter `N > 1`; gives sharp **lower-bound certificate**, not global optimality |
| Parity margin and normalized variance algebra | `even_variance_formula`, `odd_variance_formula` | Exact real identities |
| Convex curvature-to-quadratic envelope implication | `convex_stationary_global_minimum`, `quadratic_envelope_of_convex_gap`, `quadratic_envelope_of_gap_second_derivative` | Abstract twice-differentiable real functions, **conditional on a verified curvature hypothesis** |

The modules `Sampling.lean` and `CurvatureBridge.lean` additionally connect normalized one-draw hypergeometric MGFs to Bernoulli MGFs and isolate the curvature-to-Laplace implication. Their exact full-project CI verdict must be read from the branch's latest GitHub Actions run, rather than inferred from this list.

Last independently confirmed green build before the latest additions:
[GitHub Actions #38597444686](https://github.com/wzn1118/exact-hoeffding-constants/actions/runs/38597444686).

## Open mathematical proof obligations

1. Formalize the hypergeometric first and second moments and the entire exponentially tilted variance formula.
2. Formalize the Jacobi real-rootedness argument / Poisson–binomial admissibility and its constrained mean–variance inequality.
3. Prove the all-tilt hypergeometric curvature theorem `thm:curvature` for all finite `N,k,m,t`.
4. Prove the parity-uniform Riccati barrier and scaled-Bernoulli Laplace comparison `thm:main_laplace`, including strictness.
5. Prove the `m=2` three-mass optimal-proxy theorem and strict comparison.
6. Prove the global odd-population maximizing margins and their exhaustive equality classification.
7. Formalize finite exchangeable measures, their reduction to Hamming slices and the complete Lee–Kim variational identity for arbitrary zero-sum contrasts.
8. Combine all the previous theorems into an **unconditional, end-to-end Lean theorem** establishing the exact `C_N^★` formula for both parities, including the weighted tail corollary and asymptotic claims.

**Status:** The complete manuscript has **not** been formally certified. No source file claims the unproved upper bound as a Lean theorem, and there are no `sorry`, `admit`, or newly introduced axioms used to conceal it.

## Reproduce

```bash
lake update
lake exe cache get
lake build ExactHoeffding
lake env lean ExactHoeffding.lean
```

The dedicated workflow `.github/workflows/lean4.yml` rejects proof placeholders and builds every imported module. Check the commit SHA reported by the workflow; the success of an earlier SHA does not certify a later commit.
