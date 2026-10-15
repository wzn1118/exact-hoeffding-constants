# Manuscript proof obligations

Updated 15 October 2026. Current branch: `formal/full-closure-20261015`.

## Completed core obligations

Support and degeneracies; all-degree factorial moments; actual tilted
feasibility; all-parameter sharp curvature and curvature equality;
stationary and Riccati polynomial certificates; global crossing and Laplace
envelopes; Bernoulli optimal proxy; two-draw specialization and extremizers;
odd all-parameter proxy optimum and complete odd margin equality; actual
finite-exchangeability variational identity; exact parity constants;
projected-weight exponential tail and confidence inequalities.

The formerly open `m_N → ∞` odd comparison is closed by
`odd_normalized_proxy_all_upper` and `odd_normalized_proxy_all_equality`.
These quantify over every legal sample size for each odd population.

## Remaining obligations

| ID | Manuscript assertion | Proved input | Remaining statement |
| --- | --- | --- | --- |
| F-01 | Classical Jacobi zeros | Actual canonical PGF splits over ℝ, has `j` negative roots, is simple by its ODE, factors into Bernoulli PGFs, and the normalized Rodrigues roots map into `(-1,1)` | Named standard Jacobi polynomial identity/normalization remains open |
| F-02 | Full tilted Poisson–binomial law | Actual canonical coefficient/tilted PGF and product-space construction | Completed: `hypergeom_tilted_law_eq_shifted_independent_bernoulli` covers every legal margin, tilt, and degeneracy |
| F-03 | Main first-order population limit | `ConstantAsymptotics` proves finite bounds and both exact-coefficient limits | Completed; module compiled successfully |
| F-04 | Fourth-order log-MGF Taylor formula | `MGFDerivatives` and `LogMGFTaylor` | Completed: actual first four derivatives and fixed-population Peano/Lagrange remainders |
| F-05 | Fourth-order sharp-proxy expansion | Actual jointly analytic inverse-population family; compact convergence and uniform tails; localization and unique global analytic optimizer; tilt coefficient 4s; normalized optimum coefficients 1 and 1-s²/3 with analytic cubic remainder | Tilt coefficients at orders N⁻² and N⁻³; normalized optimum coefficients at N⁻³ and N⁻⁴ and analytic fifth-order remainder |
| F-06 | Fixed-sample all-success maximum | Odd two-draw and complementary N-2 maxima and complete equality classifications are proved in `FixedSampleExtrema` | The corresponding theorem for every fixed sample size `m` and the eventual all-`m` statement remain open |
| F-07 | Exact imbalance coefficient | `ExactImbalanceAlgebra`: continuous-margin cumulants, D/T/A identities and strict algebraic gap | Analytic optimizer and complete response coefficient theorem |
| F-08 | Higher cumulant expansions | All-degree factorial moments and exact cumulants through four | Completed through sixth order, including actual fifth/sixth log-MGF derivatives and displayed κ₄, κ₅, κ₆ asymptotic remainders; higher optimized proxy expansion remains F-05 |
| F-09 | Compact success-proportion comparison | `CompactAnalyticContraction` proves the original full inequality with explicit threshold, both parities, strictness and complete equality | Main theorem completed; independent joint-analytic first-order correction and B-factor identities in its proof remain separate |
| F-10 | Reverse even proxy classification | `EvenHypergeomExtremizers` | Completed: `even_normalized_proxy_all_equality` proves exactly k=N/2 for every legal nondegenerate sample size |

An incorrect pointwise odd constant curvature shortcut remains excluded:
the odd sharp quadratic proxy must follow from integrated mean-dependent
comparison. Its counterexample is recorded in `source/auxiliary_curvature.tex`.
This excluded route is not used in the exact-constant proof.

## Certification

A completed item requires a proof of its actual mathematical statement and a
successful kernel check. No scalar inequality about a supplied Bernoulli list
is counted as proof that a hypergeometric law has that representation.
No symbolic script substitutes for a Lean proof term. The generated theorem
audit records transitive axiom dependencies for the whole imported development.
