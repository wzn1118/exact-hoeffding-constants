> **Historical snapshot.** This dated report records an earlier verification state. The current release status is maintained in `formal_status/current_pdf_lean_reconciliation_20261018.md` and `formal_status/manuscript_concordance.md`.

# Formal proof coverage — 16 October 2026

## Historical statement-scope audit — 17 October 2026

The Main+A+B core results were proved at this checkpoint. This working
extension was on `formal/end-to-end-scope-audit-20261017`. The frozen whole-paper
gate was then **not closed**: `A:factorial` had the two definition-domain
qualifications recorded in `formal_status/a2_factorial_denominator_audit.md`.
The requested A1–A5 and B1–B2 families were represented in that concordance,
but A2 remained scope-qualified. A1 endpoint extensions followed from the
actual endpoint atom costs and finite one-sided integral limits. The actual
proxy's joint local Taylor remainder and odd-central variational boundary cases
were included. The checkpoint had 3,445 build jobs, an audit of 1,971 theorems
in 324 modules, 339 mapped declarations across 49 rows, and ten typed contracts.
The other 39 rows still needed standalone contracts then. The current release
supersedes this historical snapshot.


Canonical branch: `main`.
Lean 4.33.0; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Exact constants and actual probability laws

The committed development proves the all-parameter odd hypergeometric
maximum and its complete margin-extremizer classification. There is no
bounded-sample-size assumption, fixed-sample assumption, or growth-rate
restriction. Thus it covers sequences with `m_N → ∞` as well as bounded
sample sizes.

For `N = 2n+1`, `n > 0`, every `0 < k,m < N` satisfies

```
normalizedHypergeomProxy N k m ≤ oddHypergeomConstant N
```

Equality holds exactly when `m = 1` or `m = N-1`, and `k = n` or `k = n+1`.
The proxy is the supremum of the actual centered log-MGF quotient over all
nonzero real tilts. It is not an auxiliary polynomial coefficient.

`exactExchangeableConstant N` is the infimum of valid coefficients over all
exchangeable probability measures supported on the real cube, all zero-sum
coefficient vectors, and all real tilts. `VariationalIdentity` proves that
this infimum equals the hypergeometric variational supremum. The coefficient
at the infimum is valid. `ExactParityConstants` then proves, for every `N ≥ 2`,

```
C_N = N / (N-1)                       if N is even
C_N = 1 / ((N-1) * artanh (1/N))       if N is odd.
```

`ExactOddGlobalTheorem` exposes the actual odd optimum, its closed form,
validity, leastness, and an attaining singleton margin.

`ConstantAsymptotics` proves `N(C_N-1) → 1` along the complete natural
population sequence. Its finite bound is
`1 ≤ N(C_N-1) ≤ N/(N-1)` for every `N ≥ 2`, so both parities are covered by
one squeeze argument. The identical limit holds for the actual infimum
`exactExchangeableConstant`.

## Kernel-checked proof chain

| Component | Modules and scope |
| --- | --- |
| Support and degeneracies | `Support`, `OrdinaryMomentsComplete`, `ZeroTiltMoments`: exact support, totalized mass, zero/full margins, mean and ordinary variance, including `N=0,1` |
| Sampling and symmetries | `Symmetries`, `SliceSampling`, `PermutationSlice`: actual transpose/complements, uniform subset sampling, and finite random permutation sampling |
| Factorial moments | `GeneralFactorialMoments`, `Cumulants`, `HighCumulants`, `HigherLogMGFDerivatives`: all-degree factorial moment identity, actual raw moments through order six, exact log-MGF derivatives through six, and fixed-margin asymptotic interfaces |
| Actual tilted feasibility | `CrossSum`, `TiltedAdmissibilityDirect`, `StrictAdmissibility`: actual tilted mean–variance inequality and its strict version |
| Riccati and stationary algebra | `HypergeometricODE`, `HypergeometricODEMargins`, `StationaryCertificates`, `RiccatiCertificates`: actual differential identities, all-degree positive expansions, stationary comparison and residual certificates |
| Global curvature | `StationaryGlobal`, `SmallSupportCurvature`, `CanonicalCurvatureComplete`, `SharpCurvatureTheorem`: the sharp symmetric minimum for every legal `N,k,m,t` |
| Curvature equality | `AllParameterCurvatureEquality`: interior, one-point-width, complementary and deterministic cases; interior equality is `t=0` with at least one balanced margin |
| Global Laplace comparison | `GlobalCrossing`, `WholeLineCrossing`, `RiccatiComparison`, `VarianceBarrierFlow`, `HypergeometricBarrier`, `LaplaceEnvelopeTheorem`: strict scaled Bernoulli domination, with actual-law inputs |
| Zero scale and quadratic domination | `BernoulliBalancedLimit`, `UniformLaplace`, `StrictUniformLaplace`: balanced limit, quadratic envelope and equality |
| Bernoulli optimum | `BernoulliOptimal`: sharp quadratic upper bound and leastness for the whole closed probability interval |
| Two draws | `TwoDrawProxyComplete`, `TwoDrawComparison`, `TwoDrawSingletonComparison`, `FixedSampleExtrema`: actual three-mass specialization, all-success-count odd extremizers, and fixed-sample odd two-draw and complementary `N-2` maxima with equality classifications |
| Fixed-sample global extremizers | `FixedSampleGlobalExtrema`: all successes for every fixed positive sample size, shared finite-range thresholds and complete equality |
| Real-parameter curvature | `RealMarginMasses`, `RealRecurrenceCurvature`: actual real-margin masses, normalization, mean, recurrence and degree≥3 sharp all-tilt curvature |
| Odd global optimum | `StrictGlobalGap`, `StrictHypergeometricProxy`, `OddHypergeomExtremizers`: strict global proxy comparison and all legal margin pairs |
| Real-cube reduction | `CubeVertexReduction`, `MeasureExchangeability`: convex vertex reduction and averaging for actual exchangeable probability measures |
| Two-level reduction | `ThreePointExclusion`, `TwoLevelOptimization`, `TwoLevelExistence`, `TwoLevelRepresentation`, `TwoLevelReduction`: compact maximizer, two-valued form, exact contrast norm and hypergeometric MGF |
| Matching lower bound | `HammingMeasure`, `HammingExchangeableLower`: actual probability measures realizing Hamming slices |
| Variational identity and exact coefficient | `ExchangeableConstants`, `VariationalUpper`, `VariationalIdentity`, `ExactParityConstants`, `ExactOddGlobalTheorem` |
| Weighted concentration | `ProjectedWeights`, `GeneralWeightedTail`: projected squared norm, actual-measure exponential Markov bound and confidence threshold |
| Jacobi factorization | `JacobiRoots`, `JacobiMobius`, `JacobiFactorization`, `JacobiActualPGF`, `JacobiSimpleRoots`, `JacobiRootLocalization`: Rodrigues real splitting, exact Möbius bridge, simple actual PGF roots, interior Bernoulli factors, and normalized Rodrigues roots mapped into `(-1,1)`; `JacobiStandardNormalization` identifies the independently defined standard polynomial with exact normalization and complete simple root theorem |

The Bernoulli sharp proxy is also bounded by the universal quarter coefficient,
with strict inequality for nonbalanced interior parameters.

The scalar contraction coefficient and its zero-imbalance continuous extension are proved in `AnalyticContractionCoefficient`; this supplies the strict logarithmic-odds gap used by the compact comparison.

The curvature and finite-exchangeability constant proofs use the direct
adjacent-weight feasibility argument. They do not require a presumed Jacobi
factorization or an external Lee–Kim conclusion as an axiom. The two-draw
three-mass formula is a specialization of the attributed three-point theory;
the formal proof does not change that literature attribution.

## Globally optimized population expansion

`RescaledFactorialFamily` constructs the actual factorial-basis analytic
family in inverse population. `RescaledActualProxy` identifies its removable
zero-tilt value with the actual variance and its other values with the actual
centered log-MGF quotient. Compact convergence includes zero tilt.
`ActualProxyTail` supplies a uniform tail bound;
`ActualOptimizerLocalization` localizes all global maxima.
`ActualUniqueOptimizer` and `RescaledAnalyticOptimizer` establish existence,
uniqueness and analytic dependence of the actual global optimizing tilt.

`FourthOrderMainTheorem` combines the same uniquely globally maximizing analytic
branch with its tilt expansion
`4s e + 4s(m-1)e² + 4s(6m+s²-6)e³/3 + e⁴T(e)`.
`ActualNormalizedFourthCoefficient` proves its normalized optimal value has
fourth coefficient `1-(4m²-2m-1)s²/3-4s⁴/45`, with analytic fifth-order remainder.
`ActualNormalizedFourthAsymptotics` and `OptimalProxyFourthExpansion` transfer
this to the actual supremum-defined proxy along every admissible population
sequence. The singleton gap has explicit coefficients through fourth order;
at the nearly balanced odd margin the cubic and fourth coefficients are
`2(m-1)/3` and `2(m-1)(2m+1)/3`. The corresponding rescaled fourth-order
limit is also proved.

## Complete analytic appendix chains

The joint analytic optimizer and actual normalized supremum are proved in `JointGlobalOptimizer`, `JointOptimizedValue`, and `JointFullAxisGlobalOptimizer`. The local strict imbalance monotonicity follows from the actual binomial Hessian, joint analyticity, and evenness in `JointLocalImbalanceMonotonicity`.

`RealMarginExactImbalance` and `RealMarginPhysicalSpecialization` prove the finite-population optimizing tilt and optimal coefficient, with explicit T/A derivatives, analytic cubic/quartic remainders, least-proxy identification, and strict local Bernoulli domination. `AuxiliaryCurvature` proves the actual curvature counterexample and the integrated curvature identity. `GeneralCGFCurvature` derives the same identity from a centered probability law and explicit exponential-integrability domain hypotheses.

`CanonicalGapPopulationDerivative`, `CompactCanonicalContraction`, and `CompactAnalyticHypergeomContraction` prove the exact continuous factorization, its explicit boundary, uniform compact positivity, and strict actual hypergeometric comparison. `CanonicalOptimizedPopulationRemainder` and `ActualCompactFirstCorrection` prove the explicit first population correction and a uniform quadratic remainder on compact success-proportion intervals, including balance.

`EvenHypergeomExtremizers` and `OddHypergeomExtremizers` classify all maximizing hypergeometric margin pairs. `ExchangeableVarianceSupremum` proves the actual variance supremum, nearest-balanced Hamming attainment, parity comparison, integral gap and fourth-order expansion. `ExplicitExtremizerTheorem` gives the actual single-coordinate sharpness witness, including the Bernoulli pushforward and both parity equality mechanisms. The earlier baseline register listed all 35 theorem-class environments and 6 supplementary claims as complete. The current scope audit and generated concordance supersede that blanket statement.

## Reproduction and evidence

The canonical build is `lake build ExactHoeffding`, with pinned dependencies.
The theorem audit is generated from the actual project import closure:

```
python3 checks/generate_axiom_audit.py --check
lake env lean checks/full_closure_axioms.lean > lean_axioms.log
python3 checks/check_axiom_output.py lean_axioms.log
```

The checker requires one result for every public theorem and accepts only
`propext`, `Classical.choice`, and `Quot.sound`. CI builds the umbrella and
performs this audit. Individual module evidence is retained under
`checks/logs/full_closure/`; each log applies to its recorded source checkpoint.
New modules under development are added to the umbrella after their successful
kernel check. `proof_gap_register.md` records completed assertion coverage; `checks/check_full_manuscript_concordance.py` verifies every theorem-class environment and supplementary claim against the generated audit.

## Integrated verification checkpoint

The following module-specific logs record the 16 October control-worktree
checkpoint. That report pointed to the 17 October audit state: **1,971 public
theorems in 324 project modules**, with only `propext`, `Classical.choice`, and
`Quot.sound`. Both dated counts are superseded by the current release record.

Evidence: `checks/logs/full_closure/jacobi_tilt_second_rootverify.log`,
`fixed_sample_global_rootverify.log`, `real_recurrence_curvature.log`,
`optimized_third_rootverify.log`, `global_analytic_equality_rootverify.log`,
`actual_joint_normalized_rootverify.log`, `actual_fourth_final_rootverify.log`, and `final_all_manuscript_umbrella_audit.log`.
The audit source is `checks/full_closure_axioms.lean`.

## Piecewise KL integration — 16 October 2026

`PiecewiseKLFull`, `PiecewiseKLComparison`, and `PiecewiseKLStrict` complete
the actual piecewise KL tail theorem on the note’s canonical domain, including
both support endpoints, strict `I > J > I_B` away from the mean and the exact
central equality interval against `I_P`. The assembled theorem is
`hypergeom_piecewise_kl_end_to_end`. The focused audit and exact statement
coverage are recorded in `research/tail_bounds/lean_validation.md` and
`research/tail_bounds/lean_concordance.md`.


## 16 October 2026 closure additions

At that stage the umbrella added the integer-tail, four-rate KL, Bennett/Bernstein,
factorial-Chernoff, odd-global, and finite-support mean-coordinate modules.
`FiniteSupportMeanEnvelope` proves the Legendre-to-envelope comparison by change
of variables; its strict and endpoint variants cover strict gaps and one-sided
endpoint continuation. `FiniteSupportTiltCurveOfLaw` realizes the interface from
an actual normalized finite weighted law with ordered positive endpoint atoms and
positive tilted variance, while `FiniteSupportRecurrenceBridge` specializes it to
the paper's recurrence laws. The 17 October concordance snapshot then had 35
theorem-class rows and 6 supplementary claims; the current 49-row register is
maintained in `submission/current/theorem_lean_concordance.md`.

## Initial 17 October scope-audit snapshot (superseded by the latest results below)

The independent A3, A4, A5, B1 and B2 review confirms the current exact
statements, including closed supported thresholds and the stated strictness
conditions. A2's factorial comparison uses the actual hypergeometric
Legendre transform; it is not the binomial KL rate.

A1 is being strengthened to the manuscript's open-support envelope domain
and actual finite-law tail events. The new open-support comparison and
finite-law endpoint rate bounds have passed focused kernel compilation;
the raw-coordinate assembly, strict endpoints and final global audit remain
in progress. This checkpoint does not supersede the final audit gate.

A2's adjacent integer-cutoff tie and endpoint-cutoff theorems have passed
focused kernel compilation. The reflected lower-tail chain is being checked.
The unrestricted factorial-ratio display in the frozen manuscript needs an
explicit denominator domain (`j ≤ N`) if thresholds are allowed beyond the
population size. The source manuscript remains unchanged pending the
scope decision. Consequently the full manuscript concordance gate is
currently marked Partial at A:integration and A:factorial.


## 17 October: proof extensions and frozen statement audit

Work continues on branch `formal/end-to-end-scope-audit-20261017`; the local
`main` reference and the remote `main` have not been advanced by this audit.
The in-progress upstream merge and all existing verified sources are retained.
No frozen manuscript source was edited (SHA-256
`b1bb1e3df8d8b651c4872692a8b0f4424541b4e9b3a5576d39a2be485d26e23f`).

The newly checked actual-law A1 interfaces require continuity and positivity
only on the open support. They derive tilted-variance positivity from the
finite law, prove the optimized Legendre comparison, and bound actual finite
weighted tail events without a caller-supplied Markov inequality. Original
mean coordinates, interval strictness, and non-strict finite-limit endpoints
have compiled successfully. Strict finite-limit endpoints are under integration.

The corrected A2 theorem family includes both supported tails, exact
falling-factorial candidates on their nonzero-denominator domain, the separate
zero branch above population degree, and adjacent integer minimizer ties.
The unrestricted frozen wording has two domain qualifications described in
`a2_factorial_denominator_audit.md`: ordinary division at `j>N`, and the stated
support domain of `J` in the strict chain. These do not reverse the proved
factorial–Chernoff comparison. The manuscript concordance gate remains open;
no completion or final-main merge is asserted at this checkpoint.


## 17 October typed-contract continuation

At that checkpoint the integrated build passed 3,445 jobs. The 1,971-declaration
axiom audit and live 49-row manifest passed; 339 distinct declarations were
mapped. Ten rows had Lean-proved statement transcriptions: A1, A3, A4,
`thm:curvature`, `thm:main_laplace`, `cor:mgf`, integer tails, `thm:exchange`,
`cor:tail`, and `prop:variational`. Their proof terms depended on the mapped
underlying results, and the checker bound them to frozen TeX result hashes. A1
positivity followed from finite support, normalized nonnegative weights, distinct
endpoint values, and positive endpoint masses, with no variance-positivity
premise in the direct law interface. The full correspondence gate was still open
then because A2's frozen statement omitted its quotient and strict-rate domains;
the current release supersedes that checkpoint.
