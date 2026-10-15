# Lean proof coverage

Paper: **Exact Hoeffding Constants for Finite Exchangeable Sequences**.
Author: **Zinan Wang**. Updated 15 October 2026.

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

Public entry points include `hypergeomTiltVariance_sharp`,
`hypergeom_laplace_envelope`, `odd_normalized_proxy_all_equality`,
`exactExchangeableConstant_eq_variational`,
`exact_finite_exchangeability_constants`, and the six closed-form interfaces
in `ExactOddGlobalTheorem.lean`.

## Scope of the remaining work

The full manuscript includes further assertions beyond the exact constants:
standard Jacobi normalization (the actual canonical PGF simple-root statement is now proved),
optimized fourth-order asymptotics,
fixed-sample uniform extremizers, exact imbalance response, and analytic
contraction. Their precise state is recorded in
[proof_gap_register.md](proof_gap_register.md). A proof of a fixed-population
Taylor formula does not establish the global optimized population expansion.

## Verification

`checks/full_closure_axioms.lean` is generated from every public theorem in
the umbrella's project import closure. The audit checker verifies both full
coverage and the permitted axiom set. Build and audit commands are in the
detailed inventory and `.github/workflows/lean4.yml`.

`theorem_to_lean.csv` maps manuscript assertions to their precise Lean modules;
partial and open assertions are listed separately from proved results.
