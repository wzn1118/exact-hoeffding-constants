# Lean proof coverage

Paper: **Exact Hoeffding Constants for Finite Exchangeable Sequences**.
Author: **Zinan Wang**. Updated 16 October 2026.

The current source branch is `formal/full-closure-20261015`, using Lean 4.33.0
and pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
The detailed inventory is [formal_status/full_closure.md](formal_status/full_closure.md).

## Main conclusions

- The sharp hypergeometric curvature upper bound holds for every legal
  `N,k,m` and every real tilt, including deterministic and small-support cases.
- The strict mean-dependent Bernoulli envelope and its zero-scale limit are
  formalized for the stated domains.
- Odd-population normalized proxies are maximized exactly at singleton or
  complementary-singleton samples and the two nearest-balanced success counts.
  This is an all-parameter finite statement; no `m_N` regime is omitted.
- The real-cube exchangeability reduction and the matching actual Hamming
  lower bound prove the hypergeometric variational identity.
- Every actual tilted hypergeometric law is identified with a shifted independent
  Bernoulli sum on a finite product probability space, including degeneracies.
- Fifth and sixth actual cumulants, their log-MGF derivative identities, and
  the stated κ₄/κ₅/κ₆ fixed-margin asymptotic remainders are kernel checked.
- For every `N ≥ 2`, the actual least finite-exchangeability coefficient is
  `N/(N-1)` for even `N` and `1/((N-1) artanh(1/N))` for odd `N`.
- Weighted concentration for actual probability measures is proved through
  coefficient validity and projected weight normalization.
- The main theorem's first-order limit `N(C_N-1) → 1` is proved for the
  entire natural population sequence, covering both parities at once.

- For each fixed positive sample size and success imbalance, all global maximizing
  tilts localize to zero and form a unique analytic branch for sufficiently large
  admissible populations. Its first three coefficients are `4s`, `4s(m-1)`, and `4s(6m+s²-6)/3`. The actual normalized
  optimum has fourth coefficient `1-(4m²-2m-1)s²/3-4s⁴/45` and an analytic fifth-order remainder.
  The odd nearly balanced singleton gap has fourth coefficient `2(m-1)(2m+1)/3`.
- Both parity maximizing-margin classifications are complete: for even populations
  the normalized optimum is attained exactly at balanced success counts.

Public entry points include `hypergeomTiltVariance_sharp`,
`hypergeom_laplace_envelope`, `odd_normalized_proxy_all_equality`,
`exactExchangeableConstant_eq_variational`,
`exact_finite_exchangeability_constants`, and the six closed-form interfaces
in `ExactOddGlobalTheorem.lean`.

## Manuscript coverage

The compact success-proportion argument now has both an independent finite comparison and an analytic proof for the actual global optimum. The analytic development includes the full binomial axis, the exact continuous population/imbalance factor, its positive boundary value, and the explicit first population correction with a uniform quadratic remainder through balance. Exact finite-population imbalance response includes the actual optimizing tilt, explicit T/A coefficients, odd/even analytic remainders and strict Bernoulli comparison.

All 30 named results in the principal paper and technical supplement have complete theorem mappings in [formal_status/manuscript_concordance.md](formal_status/manuscript_concordance.md). The actual variance supremum, its strict odd gap and fourth-order expansion, and the explicit Hamming-law extremizer with its full Bernoulli pushforward and both parity contact mechanisms are included.

The complete integrated umbrella build and generated audit pass: **1637 public theorems in 258 project modules**. The audit reports only `propext`, `Classical.choice`, and `Quot.sound`. All project Lean modules are imported by the umbrella.

## Verification

`checks/full_closure_axioms.lean` is generated from every public theorem in
the umbrella's project import closure. The audit checker verifies both full
coverage and the permitted axiom set. Build and audit commands are in the
detailed inventory and `.github/workflows/lean4.yml`.

`theorem_to_lean.csv` maps manuscript assertions to their precise Lean modules;
the per-result concordance distinguishes assembled statements from their proved components.

## Piecewise KL tail theorem

`hypergeom_piecewise_kl_end_to_end` supplies the actual closed-support upper
and lower tails on `3 ≤ m ≤ k`, `2*k ≤ N`, `2*m < N`. It proves
`I > J > I_B` at every noncentral threshold and classifies `J = I_P` exactly
on the central switching interval. See
[the KL concordance](research/tail_bounds/lean_concordance.md) and
[reproduction record](research/tail_bounds/lean_validation.md).
