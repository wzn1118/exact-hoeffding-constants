# Lean proof coverage

## Current status — 18 October 2026

The canonical paper is the GitHub `main` source at commit `91719272750df6103358d8daccc4de8526a0d101`; its TeX SHA-256 is `617cce1f87272bd5d5d58e3d91342bba658bb490cb901643fb9436ecc6e2894b`. The current concordance has 49 rows (35 theorem-class environments plus 14 supplements), all with typed contracts and status `Complete`, and 394 distinct mapped theorem declarations. The current PDF and theorem manifest are byte-bound to that source.

`lake build ExactHoeffding` passed 3,454 jobs. The generated `#print axioms` audit covers 2,028 public declarations in 333 imported project modules and uses only `propext`, `Classical.choice`, and `Quot.sound`. A1, `prop:odd2`, `A:factorial`, and `cor:fixedm_gap` are covered by their current aggregate contracts. The old 46/49 status, old source hash, and old job/declaration counts below are historical records and are not the current release status.

The remaining process item is statement-level review of 35 typed contracts that do not yet have individual marker profiles in strict checker mode. This does not weaken the kernel proofs; it prevents a claim that a generic checker has mechanically established every TeX-to-Lean semantic translation.

## Historical status notes


## Current statement-scope audit — 17 October 2026

The Main+A+B core results remain proved. This working extension is on
`formal/end-to-end-scope-audit-20261017`. The frozen whole-paper gate is
**not closed**: `A:factorial` has the two definition-domain qualifications
recorded in `formal_status/a2_factorial_denominator_audit.md`. The requested
A1–A5 and B1–B2 proof families are now represented in the current concordance;
the only incomplete row is A2 because the frozen display omits two domain
conditions. The Q-expansion's jointly uniform local remainder and the odd
central variational boundary cases have also been added. The current concordance has 49 rows: 35 theorem environments and 14 supplements, with 377 declaration references to 339 distinct Lean theorems. Ten rows now carry separately transcribed Lean proposition contracts: A1, A3, A4, curvature, main Laplace, MGF, integer tails, exact exchangeability, weighted tails, and the variational identity. The other 39 rows still need standalone contracts. A2 remains scope-qualified. The integrated build passed 3,445 jobs, and the full audit passed for 1,971 theorems in 324 modules. The manuscript and pinned dependencies remain unchanged; no final-main merge has been performed.


Paper: **Exact Hoeffding Constants for Finite Exchangeable Sequences**.
Authors: **Zinan Wang and Xinhao Yang**. Updated 17 October 2026.

The canonical source branch is `main`, using Lean 4.33.0
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

The earlier baseline register listed complete mappings for all 35 theorem-class environments and 6 supplementary claims; the current scope audit and generated concordance supersede that blanket statement. Detailed mappings remain in [submission/current/theorem_lean_concordance.md](submission/current/theorem_lean_concordance.md). The actual variance supremum, its strict odd gap and fourth-order expansion, the finite-support mean-coordinate envelope, and the explicit Hamming-law extremizer with its full Bernoulli pushforward and both parity contact mechanisms are included.

Current integrated checkpoint (17 October 2026): the umbrella build passed 3,445 jobs and the generated axiom audit passed for **1,971 public theorems in 324 project modules**. The audit reports only `propext`, `Classical.choice`, and `Quot.sound`. The 49-row concordance contains 377 declaration references to 339 distinct Lean theorems. Ten rows have kernel-checked typed Lean proposition contracts; these are manually transcribed and reviewed against the frozen TeX, since the checker does not prove arbitrary TeX-to-Lean semantic equivalence. The other 39 rows still lack standalone proposition contracts. The sole mathematical scope row still open is A2. Detailed A1–A5/B1–B2 coverage is in [formal_status/A1_A5_B1_B2_scope_audit_20261017.md](formal_status/A1_A5_B1_B2_scope_audit_20261017.md).

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
