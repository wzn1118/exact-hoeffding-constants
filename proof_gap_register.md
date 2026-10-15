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
| F-01 | Classical Jacobi zeros | Actual canonical PGF splits over ℝ, has `j` negative roots, is simple by its ODE, and factors into Bernoulli PGFs | Standard Jacobi normalization and `(-1,1)` localization |
| F-02 | Full tilted Poisson–binomial law | Actual canonical coefficient/tilted PGF and product-space construction | Completed: `hypergeom_tilted_law_eq_shifted_independent_bernoulli` covers every legal margin, tilt, and degeneracy |
| F-03 | Main first-order population limit | `ConstantAsymptotics` proves finite bounds and both exact-coefficient limits | Completed; module compiled successfully |
| F-04 | Fourth-order log-MGF Taylor formula | `MGFDerivatives` and `LogMGFTaylor` | Completed: actual first four derivatives and fixed-population Peano/Lagrange remainders |
| F-05 | Fourth-order sharp-proxy expansion | Exact constants and strict finite singleton dominance | Joint analytic family, localization, unique global optimizing tilt, optimized coefficients and analytic remainder |
| F-06 | Fixed-sample all-success maximum | All-parameter bound below the odd singleton benchmark | Success-count extremizers at fixed sample size, uniformly for all success counts at sufficiently large population |
| F-07 | Exact imbalance coefficient | `ExactImbalanceAlgebra`: continuous-margin cumulants, D/T/A identities and strict algebraic gap | Analytic optimizer and complete response coefficient theorem |
| F-08 | Higher cumulant expansions | All-degree factorial moments and exact cumulants through four | Completed through sixth order, including actual fifth/sixth log-MGF derivatives and displayed κ₄, κ₅, κ₆ asymptotic remainders; higher optimized proxy expansion remains F-05 |
| F-09 | Supplementary refinements | Sharp curvature, actual Bernoulli tilt geometry, and Jacobi root dispersion are proved | Analytic contraction on compact success-proportion intervals |
| F-10 | Reverse even proxy classification | Balanced success margins attain the even bound for every nondegenerate sample size | Public `iff` for the complete even proxy maximizing-margin set |

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
