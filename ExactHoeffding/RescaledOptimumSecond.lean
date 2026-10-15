import ExactHoeffding.AnalyticCurveSecondDerivative
import ExactHoeffding.RescaledVarianceSecond

/-! # The actual optimized value's second inverse-population derivative -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem rescaledProxyExtension_optimized_value_deriv2
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0) (hdτ : deriv τ 0 = 4 * s) :
    iteratedDeriv 2 (fun e => rescaledProxyExtension m s e (τ e)) 0 =
      (m : ℝ) * (1 - (m : ℝ) - s ^ 2 / 3) / 2 := by
  let Q : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
  let D := fderiv ℝ (fderiv ℝ Q) (0, 0)
  have hQ : AnalyticAt ℝ Q (0, 0) := rescaledProxyExtension_joint_analytic m s
  have hy : fderiv ℝ Q (0, 0) (0, 1) = 0 := by
    change tiltPartial Q (0, 0) = _
    rw [tiltPartial_eq_deriv Q (0, 0) hQ]
    exact rescaledProxyExtension_limit_deriv_zero m hm s
  have hxx : D (1, 0) (1, 0) = (m : ℝ) * (1 - (m : ℝ) - s ^ 2) / 2 := by
    have h := analytic_curve_iteratedDeriv2 Q (fun _ => 0) hQ analyticAt_const rfl hy
    simp only [deriv_const] at h
    exact h.symm.trans (rescaledProxyExtension_zero_tilt_deriv2 m s)
  have hyx : D (1, 0) (0, 1) = (m : ℝ) * s / 12 := by
    have hins : HasDerivAt (fun e : ℝ => (e, (0 : ℝ))) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
    have hfirst := (analyticAt_tiltPartial Q _ hQ).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt_of_eq 0 hins rfl
    have hslice : (fun e => tiltPartial Q (e, 0)) =ᶠ[𝓝 0]
        (fun e => deriv (rescaledProxyExtension m s e) 0) := by
      filter_upwards [hins.continuousAt.eventually hQ.eventually_analyticAt] with e he
      exact tiltPartial_eq_deriv Q (e, 0) he
    rw [← analytic_directional_fderiv Q (0, 0) (1, 0) (0, 1) hQ]
    exact hfirst.deriv.symm.trans (hslice.deriv_eq.trans
      (rescaledProxyExtension_mixed_hasDerivAt m s).deriv)
  have hxy : D (0, 1) (1, 0) = (m : ℝ) * s / 12 := by
    have hsymm := (hQ.contDiffAt : ContDiffAt ℝ ⊤ Q (0, 0)).isSymmSndFDerivAt (by simp)
    exact (hsymm (0, 1) (1, 0)).trans hyx
  have hyy : D (0, 1) (0, 1) = -(m : ℝ) / 48 := by
    rw [← analytic_directional_fderiv Q (0, 0) (0, 1) (0, 1) hQ]
    change tiltPartial (tiltPartial Q) (0, 0) = _
    rw [tiltPartial2_eq_iteratedDeriv2 Q (0, 0) hQ]
    exact rescaledProxyExtension_limit_deriv2 m s
  rw [analytic_curve_iteratedDeriv2 Q τ hQ hτ hτzero hy, hdτ]
  change D (1, 4 * s) (1, 4 * s) = _
  rw [show ((1, 4 * s) : ℝ × ℝ) = (1, 0) + (4 * s) • ((0, 1) : ℝ × ℝ) by
    ext <;> simp]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  rw [hxx, hyx, hxy, hyy]
  ring

end

end ExactHoeffding
