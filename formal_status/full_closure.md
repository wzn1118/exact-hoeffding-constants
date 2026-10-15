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

## Precise remaining joins

The hypergeometric canonical curvature and mean-dependent barrier composition
are under kernel checking. Their current source drafts are not certification.
General transpose/complement reduction, the full Jacobi-to-PGF Möbius identity,
root factorization and Bernoulli-sum law, general Bernoulli optimal proxy,
three-mass proxy extrema, and the odd discrete optimization remain in progress.

Finite exchangeable measures, cube-vertex reduction, the complete two-level
variational reduction, the unconditional exact-constant theorem and the
higher-order appendix still require formal proofs. The entire manuscript is
not yet certified. Generic comparison lemmas are recorded as generic results,
not as unconditional hypergeometric main theorems.

Individual checks and axiom outputs are in `checks/logs/full_closure/`.
A successful earlier source commit does not certify later unverified drafts.
