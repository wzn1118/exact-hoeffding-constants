import ExactHoeffding.RescaledMixedDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # The leading optimizing tilt is `4 s / N`, with positive tilt for `s > 0` -/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

theorem rescaledProxyExtension_critical_branch_hasDerivAt
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) :
    HasDerivAt τ (4 * s) 0 := by
  let Q : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
  let F := tiltPartial Q
  have hQ : AnalyticAt ℝ Q (0, 0) := rescaledProxyExtension_joint_analytic m s
  have hF : AnalyticAt ℝ F (0, 0) := analyticAt_tiltPartial Q _ hQ
  have hins : HasDerivAt (fun e : ℝ => (e, (0 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have hfirst := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hins rfl
  have hslice : (fun e : ℝ => F (e, 0)) =ᶠ[𝓝 0]
      (fun e => deriv (rescaledProxyExtension m s e) 0) := by
    filter_upwards [hins.continuousAt.eventually hQ.eventually_analyticAt] with e he
    exact tiltPartial_eq_deriv Q (e, 0) he
  have hx : fderiv ℝ F (0, 0) (1, 0) = (m : ℝ) * s / 12 := by
    exact hfirst.deriv.symm.trans (hslice.deriv_eq.trans
      (rescaledProxyExtension_mixed_hasDerivAt m s).deriv)
  have hy : fderiv ℝ F (0, 0) (0, 1) = -(m : ℝ) / 48 := by
    change tiltPartial (tiltPartial Q) (0, 0) = _
    rw [tiltPartial2_eq_iteratedDeriv2 Q (0, 0) hQ]
    exact rescaledProxyExtension_limit_deriv2 m s
  have hpath : HasDerivAt (fun e : ℝ => (e, τ e)) (1, deriv τ 0) 0 :=
    (hasDerivAt_id 0).prodMk hτ.differentiableAt.hasDerivAt
  have hcomp := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath
    (by simp only [hτzero])
  have hpathzero : (fun e : ℝ => F (e, τ e)) =ᶠ[𝓝 0] (fun _ => 0) := by
    have hc : Tendsto (fun e : ℝ => (e, τ e)) (𝓝 0) (𝓝 (0, 0)) := by
      have hc' := hpath.continuousAt
      rw [ContinuousAt, hτzero] at hc'
      exact hc'
    filter_upwards [hc.eventually heq, hc.eventually hQ.eventually_analyticAt] with e he ha
    rw [show F (e, τ e) = deriv (rescaledProxyExtension m s e) (τ e) from
      tiltPartial_eq_deriv Q (e, τ e) ha]
    exact he.mpr rfl
  have hlin : fderiv ℝ F (0, 0) (1, deriv τ 0) = 0 := by
    exact hcomp.deriv.symm.trans (hpathzero.deriv_eq.trans (deriv_const _ _))
  rw [show ((1, deriv τ 0) : ℝ × ℝ) = (1, 0) + deriv τ 0 • ((0, 1) : ℝ × ℝ) by
    ext <;> simp, map_add, map_smul, hx, hy, smul_eq_mul] at hlin
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply hτ.differentiableAt.hasDerivAt.congr_deriv
  nlinarith

theorem rescaledProxyExtension_analytic_critical_branch_leading
    (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ τ : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
        deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) := by
  obtain ⟨τ, hτ, hτzero, heq⟩ := rescaledProxyExtension_analytic_critical_branch m hm s
  exact ⟨τ, hτ, hτzero,
    rescaledProxyExtension_critical_branch_hasDerivAt m hm s τ hτ hτzero heq, heq⟩

theorem analytic_branch_eventually_positive (τ : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hτzero : τ 0 = 0) (hτ : HasDerivAt τ a 0) :
    ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < τ e := by
  have hslope : ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < slope τ 0 e :=
    (tendsto_const_nhds.eventually_lt
      (hτ.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)) ha)
  filter_upwards [hslope, self_mem_nhdsWithin] with e he hepos
  rw [slope_def_field, hτzero, sub_zero, sub_zero] at he
  exact (div_pos_iff_of_pos_right hepos).mp he

end

end ExactHoeffding
