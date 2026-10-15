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
| Two draws | `TwoDrawProxyComplete`, `TwoDrawComparison`, `TwoDrawSingletonComparison`: actual three-mass specialization, all-success-count odd extremizers, strict singleton comparison |
| Odd global optimum | `StrictGlobalGap`, `StrictHypergeometricProxy`, `OddHypergeomExtremizers`: strict global proxy comparison and all legal margin pairs |
| Real-cube reduction | `CubeVertexReduction`, `MeasureExchangeability`: convex vertex reduction and averaging for actual exchangeable probability measures |
| Two-level reduction | `ThreePointExclusion`, `TwoLevelOptimization`, `TwoLevelExistence`, `TwoLevelRepresentation`, `TwoLevelReduction`: compact maximizer, two-valued form, exact contrast norm and hypergeometric MGF |
| Matching lower bound | `HammingMeasure`, `HammingExchangeableLower`: actual probability measures realizing Hamming slices |
| Variational identity and exact coefficient | `ExchangeableConstants`, `VariationalUpper`, `VariationalIdentity`, `ExactParityConstants`, `ExactOddGlobalTheorem` |
| Weighted concentration | `ProjectedWeights`, `GeneralWeightedTail`: projected squared norm, actual-measure exponential Markov bound and confidence threshold |
| Jacobi factorization | `JacobiRoots`, `JacobiMobius`, `JacobiFactorization`, `JacobiActualPGF`: Rodrigues real splitting, exact Möbius bridge, `j` negative roots counted with multiplicity, actual canonical tilted PGF product with interior Bernoulli parameters |

The Bernoulli sharp proxy is also bounded by the universal quarter coefficient,
with strict inequality for nonbalanced interior parameters.

The curvature and finite-exchangeability constant proofs use the direct
adjacent-weight feasibility argument. They do not require a presumed Jacobi
factorization or an external Lee–Kim conclusion as an axiom. The two-draw
three-mass formula is a specialization of the attributed three-point theory;
the formal proof does not change that literature attribution.

## Work remaining for the entire manuscript

1. Classical Jacobi identification, root location and simple-root statement;
   all-parameter shifted Poisson–binomial distribution on an explicit product
   probability space. The actual law equality is now proved by `HypergeomBernoulliLaw`; Jacobi PGF roots
   are also proved simple by the ODE, while standard Jacobi normalization remains open.
2. The main theorem's first-order limit is complete in `ConstantAsymptotics`.
3. The fixed-population fourth-order Taylor formula is complete in
   `MGFDerivatives` and `LogMGFTaylor`, with actual derivatives, `o(t^4)`
   remainder and a fifth-derivative Lagrange remainder for both signs of tilt.
4. The globally optimized `N⁻⁴` expansion, analytic optimizer, localization,
   and uniform remainder in `source/new_results.tex`.
5. The fixed-sample, all-success-count eventual maximum, joint analytic
   optimizer, and exact imbalance coefficient in `source/uniform_results.tex`.
6. Standard Jacobi normalization; the globally optimized fourth-order/fixed-sample
   appendix theorems; and the exact continuous-margin response theorem.

Item 1 is being extended in separate modules. Fixed-population Taylor
expansion is a different statement from the optimized population asymptotics
in item 4. The odd global exact constant does not depend on those appendices.

The exhaustive odd classification concerns the hypergeometric proxy margins.
It is not a classification of every probability measure and vector that can
saturate an MGF inequality. Even balanced-margin attainment is proved; an
additional reverse `iff` interface for all even proxy maximizers remains to
be assembled.

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
