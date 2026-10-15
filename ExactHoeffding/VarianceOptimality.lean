import ExactHoeffding.UniformLaplace
import ExactHoeffding.TwoDrawProxyComplete

open Filter
open scoped Topology

namespace ExactHoeffding

theorem hypergeom_centered_quadratic_limit (N k m : ℕ) (hk : k≤N) (hm : m≤N) :
    Tendsto (fun t => hypergeomCenteredLogMGF N k m t/t^2) (𝓝[≠] (0:ℝ))
      (𝓝 (hypergeomTiltVariance N k m 0/2)) := by
  apply quadratic_quotient_limit
    (hypergeomCenteredLogMGF_hasDerivAt N k m hk hm)
    ((hypergeomTiltMean_hasDerivAt N k m hk hm 0).sub_const _)
    (hypergeomCenteredLogMGF_zero N k m hk hm)
  rw [hypergeomTiltMean_zero N k m hk hm]
  ring

/-- Every global quadratic proxy is at least the true un-tilted variance. -/
theorem hypergeom_quadratic_proxy_ge_variance (N k m : ℕ) (hk : k≤N) (hm : m≤N)
    (D : ℝ) (hD : IsQuadraticProxy (hypergeomCenteredLogMGF N k m) D) :
    hypergeomTiltVariance N k m 0≤D :=
  quadraticProxy_lower_of_quotient_limit _ _ _ (hypergeom_centered_quadratic_limit N k m hk hm) hD

theorem hypergeomTiltVariance_zero_balanced_marks (q m : ℕ) (hq : 0<q) (hm : m≤2*q) :
    hypergeomTiltVariance (2*q) q m 0=
      (m:ℝ)*((((2*q:ℕ):ℝ))-(m:ℝ))/(4*(((2*q:ℕ):ℝ)-1)) := by
  rw [hypergeomTiltVariance_zero (2*q) q m (by omega) hm]
  have hqsub : 2*q-q=q := by omega
  rw [hqsub,Nat.cast_sub hm]
  push_cast
  have hq0 : (q:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hq
  have hN1 : 2*(q:ℝ)-1≠0 := by
    have hh : (1:ℝ)≤q := by exact_mod_cast hq
    linarith
  field_simp [hq0,hN1]
  ring

/-- Balanced marked margins have optimal proxy equal to their variance;
the lower bound is certified by the zero-tilt second-order limit. -/
theorem hypergeom_balanced_marks_optimal_proxy (q m : ℕ) (hq : 0<q) (hm : m≤2*q) :
    IsOptimalQuadraticProxy (hypergeomCenteredLogMGF (2*q) q m)
      (sharpCurvatureConstant (2*q) q m) := by
  refine ⟨hypergeom_uniform_log_laplace_domination (2*q) q m (by omega) hm,?_⟩
  intro D hD
  have h := hypergeom_quadratic_proxy_ge_variance (2*q) q m (by omega) hm D hD
  rw [hypergeomTiltVariance_zero_balanced_marks q m hq hm] at h
  have hprod : (m:ℝ)*(((2*q:ℕ):ℝ)-m)≤(q:ℝ)*(((2*q:ℕ):ℝ)-q) := by
    push_cast
    nlinarith [sq_nonneg ((m:ℝ)-q)]
  unfold sharpCurvatureConstant
  rw [min_eq_right hprod]
  exact h

end ExactHoeffding
