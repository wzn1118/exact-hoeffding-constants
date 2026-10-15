# Whole-manuscript formalization — 15 October 2026

Branch: `formal/full-closure-20261015`.
Pinned kernel: Lean 4.33.0; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

## Kernel-checked advances

- `Support`: true support, totalized point masses, zero/full margins.
- `OrdinaryMomentsComplete`, `ZeroTiltMoments`: every legal `N,k,m`, including
  `N=0,1`, exact mean and ordinary variance, and their actual tilted-zero values.
- `HypergeometricODE`: actual adjacent mass recurrence, normalized tilted
  expectation identity, `u'=v`, differentiated variance equation, stationary
  balance, positive variance and open-support mean.
- `HypergeometricODEMargins`: original-parameter versions and centered equation
  `F+N(u-mk/N)v_t=0`.
- `CrossSum`, `TiltedAdmissibilityDirect`: actual tilted mean-variance bound
  `v<=u(m-u)/m`, proved from adjacent weights, independent of Jacobi factorization.
- `StationaryCertificates`: exact elimination, universal stationary comparison,
  all-degree positive coefficient certificate, and admissible sharp stationary bound.
- `StationaryGlobal`: endpoint limits plus stationary bounds imply a global bound.
- `SmallSupportCurvature`: actual one- and two-draw sharp curvature upper bounds,
  with balanced zero-tilt equality examples.
- `RiccatiCertificates`: residual, determinant and sum-of-squares identities;
  positivity across the real parameter domain; endpoint signs and contact algebra.
- `GlobalCrossing`, `WholeLineCrossing`: finite-interval and whole-line strict
  crossing comparison, including the unique central equality point.
- `RiccatiComparison`: nonstrict and strict two-sided comparison/integration.
- `BernoulliRiccati`, `ScaledBernoulliComparison`: concrete scaled solution,
  endpoints, separate zero-scale branch, and four Laplace comparison interfaces.
- `TiltedEndpoints`: arbitrary finite tilted expectations converge to the
  unique endpoint value at either infinite tilt.
- `BernoulliKL`: global Fenchel inequality including endpoints.
- `JacobiRoots`: Rodrigues derivative/quotient splits over the reals.

## Actual-law composition completed

- `HypergeometricEndpoints`: tilted means approach true support endpoints and
  tilted variance approaches zero at both infinities.
- `StrictAdmissibility`: actual strict mean–variance feasibility for degree >=2.
- `CanonicalCurvature`, `CanonicalCurvatureComplete`: actual all-tilt sharp
  curvature, every support degree, on canonical margins.
- `CurvatureSymmetries`: actual variance under transpose and both complements.
- `CanonicalCurvatureEquality`: degree >=3 equality holds precisely at zero
  tilt with a balanced larger margin.
- `VarianceBarrierFlow`, `HypergeometricBarrier`: actual strict mean-dependent
  variance envelope and its unique equality point.
- `HypergeometricLaplace`, `LaplaceEnvelopeTheorem`: original-parameter
  parity-uniform Bernoulli envelope, strict for all nonzero real tilts.
- `BernoulliBalancedLimit`: genuine two-sided scale-zero limit and continuous
  extension, including deterministic probability endpoints.
- `TwoDrawProxyComplete`: complete positive three-mass least quadratic proxy,
  both asymmetry directions and balance, specialized to actual two-draw laws.
- `SliceSampling`, `PermutationSlice`: actual uniform subset and permutation
  sampling, exact hypergeometric PMF, expectations and MGF.
- `FiniteExchangeability`: finite Boolean exchangeable slice mixture, exact
  two-level contrast norm and hypergeometric MGF realization.

## Remaining whole-manuscript obligations

The all-parameter curvature reduction, exhaustive equality classification,
uniform quadratic Laplace corollary and actual hypergeometric tail bound are
now kernel-checked. The full Jacobi-to-PGF Möbius/factorization chain, general
Bernoulli optimal proxy, odd singleton dominance and complete parity constants remain in progress.

The real-cube vertex reduction and complete Lee–Kim two-level optimization,
including a genuine compact maximizer, its at-most-two values and exact
hypergeometric MGF/norm parameterization, are now kernel-checked. The remaining
general finite exchangeable measures, the unconditional exact-constant and
weighted-tail theorems, and higher-order appendices still require proof.
The entire manuscript is not yet certified.

Individual checks and axiom outputs are in `checks/logs/full_closure/`.
Earlier checkpoints certify only their exact source trees.
