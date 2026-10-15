import ExactHoeffding.ActualFourthCoordinateJets
import ExactHoeffding.AnalyticCurveThirdDerivative

/-! # Third inverse-population coefficient of the actual optimizing tilt

The critical branch is the actual unique global optimizer for every
sufficiently large admissible integer population with fixed sample size
and fixed success imbalance.
-/

namespace ExactHoeffding

noncomputable section

open Filter Asymptotics
open scoped Topology

theorem rescaledProxyExtension_critical_branch_deriv3
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hz : τ 0 = 0)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) :
    iteratedDeriv 3 τ 0 = 8 * s * (6 * (m : ℝ) + s ^ 2 - 6) := by
  let Q : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
  let F := tiltPartial Q
  have hQ : AnalyticAt ℝ Q (0, 0) := rescaledProxyExtension_joint_analytic m s
  have hF : AnalyticAt ℝ F (0, 0) := analyticAt_tiltPartial Q _ hQ
  obtain ⟨_, h31, h22, h13, h04⟩ := rescaledProxyExtension_coordinate_jet4 m hm s
  have h12 : populationPartial (tiltPartial (tiltPartial Q)) (0, 0) =
      (m : ℝ) * ((m : ℝ) - 1) / 12 := by
    change ((populationPartial^[1]) ((tiltPartial^[2]) Q)) (0, 0) = _
    rw [analytic_mixed_coordinate_jets 1 2 Q hQ, iteratedDeriv_one]
    exact (rescaledProxyExtension_tilt_deriv2_zero_hasDerivAt m s).deriv
  have h03 : tiltPartial (tiltPartial (tiltPartial Q)) (0, 0) = 0 := by
    change ((tiltPartial^[3]) Q) (0, 0) = _
    rw [iterate_tiltPartial_eq_iteratedDeriv 3 Q _ hQ]
    exact rescaledProxyExtension_limit_deriv3 m s
  have h02 : tiltPartial (tiltPartial Q) (0, 0) = -(m : ℝ) / 48 := by
    rw [tiltPartial2_eq_iteratedDeriv2 Q _ hQ]
    exact rescaledProxyExtension_limit_deriv2 m s
  have hpath : Tendsto (fun e : ℝ => (e, τ e)) (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [ContinuousAt, hz, id_eq] using (continuousAt_id.prodMk hτ.continuousAt)
  have hzero : (fun e => F (e, τ e)) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [hpath.eventually heq, hpath.eventually hQ.eventually_analyticAt]
      with e he ha
    change tiltPartial Q (e, τ e) = _
    rw [tiltPartial_eq_deriv Q (e, τ e) ha]
    exact he.mpr rfl
  have h3 := analytic_curve_deriv3_partials F τ hF hτ hz
  rw [hzero.iteratedDeriv_eq, iteratedDeriv_const] at h3
  norm_num only [show (3 : ℕ) ≠ 0 by omega, if_false] at h3
  change 0 = _ at h3
  dsimp only [F] at h3
  rw [h31, h22, h13, h04, h12, h03, h02,
    (rescaledProxyExtension_critical_branch_hasDerivAt m hm s τ hτ hz heq).deriv,
    rescaledProxyExtension_critical_branch_deriv2 m hm s τ hτ hz heq] at h3
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hx : (m : ℝ) * (iteratedDeriv 3 τ 0 -
      8 * s * (6 * (m : ℝ) + s ^ 2 - 6)) = 0 := by nlinarith [h3]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hmR)

theorem actualHypergeomProxy_tilt_third_analytic_expansion
    (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ τ T : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ AnalyticAt ℝ T 0 ∧
      τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ e, τ e = 4 * s * e + 4 * s * ((m : ℝ) - 1) * e ^ 2 +
        4 * s * (6 * (m : ℝ) + s ^ 2 - 6) / 3 * e ^ 3 + e ^ 4 * T e) ∧
      (fun e => τ e - 4 * s * e - 4 * s * ((m : ℝ) - 1) * e ^ 2 -
        4 * s * (6 * (m : ℝ) + s ^ 2 - 6) / 3 * e ^ 3)
        =O[𝓝 0] (fun e => e ^ 4) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
        2 * (k : ℝ) + s = (N : ℝ) → ∀ t : ℝ,
        (∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) ↔
          t = τ e) := by
  obtain ⟨τ, hτ, hz, hd, heq⟩ :=
    rescaledProxyExtension_analytic_critical_branch_leading m hm s
  have h2 : iteratedDeriv 2 τ 0 / 2 = 4 * s * ((m : ℝ) - 1) := by
    rw [rescaledProxyExtension_critical_branch_deriv2 m hm s τ hτ hz heq]
    ring
  have h3 : iteratedDeriv 3 τ 0 / 6 = 4 * s * (6 * (m : ℝ) + s ^ 2 - 6) / 3 := by
    rw [rescaledProxyExtension_critical_branch_deriv3 m hm s τ hτ hz heq]
    ring
  obtain ⟨T, hT, hTeq, hTO⟩ := analytic_cubic_remainder τ hτ
  refine ⟨τ, T, hτ, hT, hz, hd, ?_, ?_,
    actualHypergeomProxy_critical_branch_is_global m hm s τ heq⟩
  · simpa only [hz, hd.deriv, h2, h3, zero_add] using hTeq
  · simpa only [hz, hd.deriv, h2, h3, sub_zero] using hTO

end

end ExactHoeffding
