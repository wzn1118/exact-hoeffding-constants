# Formal proof coverage — 15 October 2026

Branch: `formal/full-closure-20261015`.
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

`AnalyticOptimizerLeading` computes its leading coefficient `4s`.
`ActualTiltSecondCoefficient` computes the second optimizing-tilt coefficient
`4s(m-1)`. `ActualNormalizedThirdCoefficient` proves the normalized optimum
through its cubic coefficient `1-(2m-1)s²/3`, with analytic quartic remainder.
`OptimalProxyAsymptotics` identifies the nonzero maximizing value with the
supremum defining `hypergeomOptimalProxy` and transfers the expansion to
`normalizedHypergeomProxy`, along every admissible population sequence.
Its odd-singleton gap has coefficients `(s²-1)/3` at order `N⁻²` and
`((2m-1)s²-1)/3` at order `N⁻³`, with quartic remainder; when `s>1`, this also proves eventual strict separation.

## Work remaining for the entire manuscript

1. The explicit third optimizing-tilt and fourth optimized-value coefficients,
   with analytic fifth-order remainder. Global localization, uniqueness,
   analyticity and value coefficients through cubic order are complete.
2. The joint analytic optimizer lemma for independently varying inverse
   population and success imbalance. Its three-variable analytic objective is
   proved. The fixed-sample all-success theorem is separately complete.
3. The continuous-margin optimizer/localization theorem for the exact
   finite-population imbalance response. Actual positive normalized masses,
   their recurrence and the real-parameter sharp curvature bound for support
   degree at least three are proved. The `D,T,A` algebra is complete.
4. Independent joint-analytic first-order correction and factorization identities
   in the compact-comparison proof. The compact comparison theorem itself is
   complete in `CompactAnalyticContraction`, with an explicit threshold, both
   parities, and equality exactly at balanced success counts.

`EvenHypergeomExtremizers` gives the full reverse `iff` for even normalized
proxy maximizers: precisely the balanced success margin, for every legal
nondegenerate sample size. The odd classification is likewise exhaustive
for hypergeometric proxy margins. These statements classify margin pairs.

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
kernel check. `proof_gap_register.md` lists open obligations explicitly.

## Integrated verification checkpoint

The control worktree independently recompiled the standard Jacobi module,
real-margin masses, second optimizing-tilt coefficient, five fixed-sample
extremizer modules and the cubic optimized-value chain. The real-parameter
recurrence module was compiled from identical source in the isolated Jacobi
worktree. Every module returned exit code zero. The complete umbrella and
generated audit pass: **1120 public theorems in 172 project modules**, with
only `propext`, `Classical.choice`, and `Quot.sound`.

Evidence: `checks/logs/full_closure/jacobi_tilt_second_rootverify.log`,
`fixed_sample_global_rootverify.log`, `real_recurrence_curvature.log`,
`optimized_third_rootverify.log`, and `integrated_third_umbrella_audit.log`.
The audit source is `checks/full_closure_axioms.lean`.
