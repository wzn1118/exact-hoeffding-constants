# Lean 4 proof coverage and mathematical audit

Paper: **Exact Hoeffding Constants for Finite Exchangeable Sequences** (Zinan Wang, 2026).

**Certification rule.** A mathematical result is recorded as proved only if a Lean declaration with the same mathematical content has a proof term accepted by the Lean 4 kernel on the referenced commit. A successful build of a subset is *not* an end-to-end formal proof of the manuscript. This ledger is intentionally explicit about open theorems.

## Current full-closure branch

The 15 October 2026 development on `formal/full-closure-20261015` is tracked
in [`formal_status/full_closure.md`](formal_status/full_closure.md). It adds
all-parameter ordinary moments, actual hypergeometric Riccati identities and
strict tilted positivity, direct tilted mean-variance admissibility,
one-/two-draw sharp curvature, the all-degree stationary certificate,
positive Riccati residual certificates, global crossing and bilateral
strict integration. The dated baseline inventory below is retained as
history; its old statement that ordinary-moment edge cases or actual
admissibility are still absent is superseded by the current branch ledger.
The complete manuscript theorem remains an open composition obligation.

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

The modules `Sampling.lean` and `CurvatureBridge.lean` connect normalized one-draw hypergeometric MGFs to Bernoulli MGFs and isolate the conditional curvature-to-Laplace implication. Both are included in the successful baseline kernel build #38606516354.

Baseline complete kernel build:
[GitHub Actions #38606516354](https://github.com/wzn1118/exact-hoeffding-constants/actions/runs/38606516354)
at commit `ebf534362f596175a24fc33e9eebc1cd4145349f`: **SUCCESS**.

## Formalization added on 15 October 2026

| Result | Lean name(s) | Verified |
| --- | --- | --- |
| First derivative of any finite exponential moment | `finiteMGF_hasDerivAt`, `finiteMGF_deriv_zero` | Kernel checked |
| Second raw tilted moment derivative | `finiteTiltFirst_hasDerivAt`, `finiteTiltSecond_zero` | Kernel checked |
| General first hypergeometric factorial moment | `hypergeomCount_first_moment_succ` | Kernel checked |
| General second hypergeometric factorial moment | `hypergeomCount_second_factorial_succ` | Kernel checked |
| Normalized hypergeometric expectation `E[H] = km/N` | `hypergeom_mean_succ` | Kernel checked for positive marked and sample margins; edge cases require an explicit separate normalization theorem |
| Strict positivity of finite normalized MGF for every tilt | `finiteMGF_pos_of_normalized` | Kernel checked |
| Exact first log-MGF derivative | `finiteLogMGF_hasDerivAt` | Kernel checked |
| Exact second log-MGF derivative as tilted variance | `finiteLogMGF_second_deriv`, `hypergeomLogMGF_second_deriv` | Kernel checked |
| Tilted mean derivative | `finiteTiltedMean_hasDerivAt` | Kernel checked |
| Finite weighted Cauchy–Schwarz and curvature nonnegativity | `finiteTilt_cauchy_schwarz`, `finiteLogMGF_second_deriv_nonneg`, `hypergeomLogMGF_second_deriv_nonneg` | Kernel checked |

These are analytically significant prerequisites for the paper's global curvature theorem. In particular **nonnegative curvature** is a *lower* bound on the second derivative of log MGF; the manuscript requires a **sharp global upper bound**. The latter remains open in Lean. Both first and second factorial-moment identities have exact all-parameter natural-number proofs, including over-sampling cases.

## Research integration on 15 October 2026

Verified research commit: `167b616e44815440732c86af7c471a5af56f14a3`.
Its [Lean kernel run 38620327901](https://github.com/wzn1118/exact-hoeffding-constants/actions/runs/38620327901)
and [analytic research run 38620327863](https://github.com/wzn1118/exact-hoeffding-constants/actions/runs/38620327863)
both completed successfully. [PR 5](https://github.com/wzn1118/exact-hoeffding-constants/pull/5)
is a draft research milestone, separate from a claim of full formalization.

The integrated library builds with Lean 4.33.0 and pinned Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. All existing theorem statements
are preserved; broad Mathlib imports are replaced by their actual dependencies.

The complete `lake build ExactHoeffding`, umbrella check and thirteen axiom
audits pass. Evidence is in `research/tail_bounds/evidence/`:
`lean_integrated_build.log`, `lean_umbrella.log` and `lean_axioms.log`.
All audited declarations use only `propext`, `Classical.choice`, `Quot.sound`.

Nine added declarations are kernel-checked: three finite Bernoulli-list
variance lemmas in `PoissonBinomial.lean`, five reciprocal/symmetry-envelope
algebra lemmas in `VarianceComparison.lean`, and `finite_markov_exp_bound`
in `Chernoff.lean`. The first module supplies the algebra needed after a
Poisson--binomial representation; it does not prove that representation.
The last supplies the exponential Markov step; it does not prove the
Bernoulli KL optimizer or instantiate the hypergeometric envelope.

The six-page piecewise KL note has a written analytic proof and finite
high-precision verification. Its variance-envelope integration remains
unformalized. The proof chain below therefore remains incomplete.

## Open mathematical proof obligations

1. Finish the zero-margin and positive-denominator edge cases of ordinary hypergeometric moments; derive the closed-form un-tilted variance from verified factorial moments. The general all-tilt variance *identity* is now formalized.
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
lake exe cache get
lake build ExactHoeffding
lake env lean ExactHoeffding.lean
```

The dedicated workflow `.github/workflows/lean4.yml` rejects proof placeholders and builds every imported module. Check the commit SHA reported by the workflow; the success of an earlier SHA does not certify a later commit.
