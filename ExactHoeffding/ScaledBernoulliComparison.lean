import ExactHoeffding.RiccatiComparison
import ExactHoeffding.BernoulliRiccati

namespace ExactHoeffding

/-- A quadratic tilted-variance bound implies the explicit scaled Bernoulli
log-Laplace envelope. -/
theorem variance_bound_implies_scaled_bernoulli_laplace
    {F y v : ℝ → ℝ} {M p a : ℝ}
    (hM : M ≠ 0) (ha : a ≠ 0) (hp0 : 0 < p) (hp1 : p < 1)
    (hyd : ∀ t, HasDerivAt y (v t) t) (hFd : ∀ t, HasDerivAt F (y t) t)
    (hv : ∀ t, v t ≤ M*p*(1-p) + a*(1-2*p)*y t - a^2/M*(y t)^2)
    (hy0 : y 0 = 0) (hF0 : F 0 = 0) :
    ∀ t, F t ≤ scaledBernoulliLogLaplace M p a t := by
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun t => (hyd t).continuousAt
  exact quadratic_riccati_log_laplace_domination hyc
    (scaledBernoulliMean_continuous hM ha hp0 hp1) hyd
    (scaledBernoulliMean_hasDerivAt hM ha hp0 hp1) hFd
    (scaledBernoulliLogLaplace_hasDerivAt ha hp0 hp1) hv
    (fun _ => rfl) (by simpa using hy0) (by simpa using hF0)

/-- Strictness of the variance envelope away from zero propagates to strict
scaled Bernoulli log-Laplace domination at every nonzero tilt. -/
theorem strict_variance_bound_implies_scaled_bernoulli_laplace
    {F y v : ℝ → ℝ} {M p a : ℝ}
    (hM : M ≠ 0) (ha : a ≠ 0) (hp0 : 0 < p) (hp1 : p < 1)
    (hyd : ∀ t, HasDerivAt y (v t) t) (hFd : ∀ t, HasDerivAt F (y t) t)
    (hv : ∀ t, t ≠ 0 → v t < M*p*(1-p) + a*(1-2*p)*y t - a^2/M*(y t)^2)
    (hy0 : y 0 = 0) (hF0 : F 0 = 0) :
    ∀ t, t ≠ 0 → F t < scaledBernoulliLogLaplace M p a t := by
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun t => (hyd t).continuousAt
  exact strict_quadratic_riccati_log_laplace_domination hyc
    (scaledBernoulliMean_continuous hM ha hp0 hp1) hyd
    (scaledBernoulliMean_hasDerivAt hM ha hp0 hp1) hFd
    (scaledBernoulliLogLaplace_hasDerivAt ha hp0 hp1) hv
    (fun _ => rfl) (by simpa using hy0) (by simpa using hF0)

/-- The zero-scale branch is the quadratic Gaussian envelope, obtained from
the constant-variance Riccati solution without division by the scale. -/
theorem variance_bound_implies_balanced_laplace
    {F y v : ℝ → ℝ} {M p : ℝ}
    (hyd : ∀ t, HasDerivAt y (v t) t) (hFd : ∀ t, HasDerivAt F (y t) t)
    (hv : ∀ t, v t ≤ M*p*(1-p)) (hy0 : y 0 = 0) (hF0 : F 0 = 0) :
    ∀ t, F t ≤ balancedBernoulliLogLaplace M p t := by
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun t => (hyd t).continuousAt
  apply quadratic_riccati_log_laplace_domination (A := M*p*(1-p)) (B := 0) (C := 0)
    hyc (balancedBernoulliMean_continuous M p) hyd
    (balancedBernoulliMean_hasDerivAt M p) hFd
    (balancedBernoulliLogLaplace_hasDerivAt M p)
  · simpa using hv
  · intro t; ring
  · simpa using hy0
  · simpa using hF0

/-- A strict constant-variance bound away from the origin yields a strict
Gaussian log-Laplace comparison away from the origin. -/
theorem strict_variance_bound_implies_balanced_laplace
    {F y v : ℝ → ℝ} {M p : ℝ}
    (hyd : ∀ t, HasDerivAt y (v t) t) (hFd : ∀ t, HasDerivAt F (y t) t)
    (hv : ∀ t, t ≠ 0 → v t < M*p*(1-p)) (hy0 : y 0 = 0) (hF0 : F 0 = 0) :
    ∀ t, t ≠ 0 → F t < balancedBernoulliLogLaplace M p t := by
  have hyc : Continuous y := continuous_iff_continuousAt.mpr fun t => (hyd t).continuousAt
  apply strict_quadratic_riccati_log_laplace_domination (A := M*p*(1-p)) (B := 0) (C := 0)
    hyc (balancedBernoulliMean_continuous M p) hyd
    (balancedBernoulliMean_hasDerivAt M p) hFd
    (balancedBernoulliLogLaplace_hasDerivAt M p)
  · simpa using hv
  · intro t; ring
  · simpa using hy0
  · simpa using hF0


end ExactHoeffding
