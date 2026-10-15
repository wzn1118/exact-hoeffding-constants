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

## Assertion coverage

| ID | Manuscript assertion | Proved input | Remaining statement |
| --- | --- | --- | --- |
| F-01 | Classical Jacobi zeros | `JacobiStandardNormalization`: independently defined standard binomial Jacobi polynomial; exact Rodrigues and hypergeometric normalizations; both root maps; degree, simplicity and all roots in `(-1,1)` | Completed for every natural canonical parameter, including degree zero |
| F-02 | Full tilted Poisson–binomial law | Actual canonical coefficient/tilted PGF and product-space construction | Completed: `hypergeom_tilted_law_eq_shifted_independent_bernoulli` covers every legal margin, tilt, and degeneracy |
| F-03 | Main first-order population limit | `ConstantAsymptotics` proves finite bounds and both exact-coefficient limits | Completed; module compiled successfully |
| F-04 | Fourth-order log-MGF Taylor formula | `MGFDerivatives` and `LogMGFTaylor` | Completed: actual first four derivatives and fixed-population Peano/Lagrange remainders |
| F-05 | Fourth-order sharp-proxy expansion | `FourthOrderMainTheorem`, `ActualNormalizedFourthCoefficient`, `OptimalProxyFourthExpansion`: same globally optimizing branch, tilt through N⁻³, normalized value through N⁻⁴, analytic fifth-order remainder, actual supremum bridge | Completed, including the nearly balanced odd singleton gap and its fourth-order limit |
| F-06 | Fixed-sample all-success maximum | `FixedSampleGlobalExtrema`: every fixed positive m, all legal success counts, eventual odd-population optimum and complete equality; shared thresholds over every finite sample range; strict singleton comparison for m≥2 | Completed, including the independent joint analytic global optimizer and its actual normalized supremum value |
| F-07 | Exact imbalance coefficient | `RealMarginExactImbalance`, `RealMarginPhysicalSpecialization`: actual fixed-N unique global optimizer, exact T/A derivatives, odd/even analytic remainders, least-proxy and physical-law bridges | Completed for N≥5, 0<m, 2m≤N, including strict Bernoulli domination for m≥2 |
| F-08 | Higher cumulant expansions | All-degree factorial moments and exact cumulants through four | Completed through sixth order, including actual fifth/sixth log-MGF derivatives and displayed κ₄, κ₅, κ₆ asymptotic remainders; optimized proxy fourth-order expansion is completed in F-05 |
| F-09 | Compact success-proportion comparison | `CompactCanonicalContraction`, `CompactAnalyticHypergeomContraction`: actual canonical global optimum on full binomial axis, exact continuous e*d² factor, explicit boundary, uniform compact positivity and physical proxy bridge | Completed: actual compact analytic comparison; continuous factor with exact boundary; explicit first population coefficient; uniform quadratic remainder through balance in `CanonicalOptimizedPopulationRemainder` and `ActualCompactFirstCorrection` |
| F-10 | Reverse even proxy classification | `EvenHypergeomExtremizers` | Completed: `even_normalized_proxy_all_equality` proves exactly k=N/2 for every legal nondegenerate sample size |


## Final manuscript consolidation

The thirty-result audit in `formal_status/manuscript_concordance.md` identifies two additional proposition-level obligations: the actual exchangeable variance supremum and odd variance-gap expansion (`prop:variance_parity`), and the assembled actual single-coordinate Hamming-law extremizer (`prop:explicit_extremizer`). Both are being proved in dedicated modules; their separate component lemmas do not count as completed assembled propositions.

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
