import ExactHoeffding.RescaledThirdMixedDerivative

/-! # The actual global optimizing tilt through second inverse-population order -/

namespace ExactHoeffding

noncomputable section

open Filter Asymptotics
open scoped Topology

theorem analytic_curve_iteratedDeriv2_full (Q : ℝ × ℝ → ℝ) (τ : ℝ → ℝ)
    (hQ : AnalyticAt ℝ Q (0, 0)) (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0) :
    iteratedDeriv 2 (fun e => Q (e, τ e)) 0 =
      fderiv ℝ (fderiv ℝ Q) (0, 0) (1, deriv τ 0) (1, deriv τ 0) +
        fderiv ℝ Q (0, 0) (0, iteratedDeriv 2 τ 0) := by
  let c : ℝ → ℝ × ℝ := fun e => (e, τ e)
  let v : ℝ → ℝ × ℝ := fun e => (1, deriv τ e)
  have hc : HasDerivAt c (1, deriv τ 0) 0 :=
    (hasDerivAt_id 0).prodMk hτ.differentiableAt.hasDerivAt
  have hc0 : c 0 = (0, 0) := by simp [c, hτzero]
  have hderiv : deriv (fun e => Q (c e)) =ᶠ[𝓝 0]
      (fun e => fderiv ℝ Q (c e) (v e)) := by
    have hct : Tendsto c (𝓝 0) (𝓝 (0, 0)) := hc0 ▸ hc.continuousAt
    filter_upwards [hct.eventually hQ.eventually_analyticAt,
      hτ.eventually_analyticAt] with e he heτ
    have hce : HasDerivAt c (v e) e :=
      (hasDerivAt_id e).prodMk heτ.differentiableAt.hasDerivAt
    exact (he.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq e hce rfl).deriv
  have hDQ := hQ.fderiv.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc hc0.symm
  have hv : HasDerivAt v (0, deriv (deriv τ) 0) 0 :=
    (hasDerivAt_const 0 1).prodMk hτ.deriv.differentiableAt.hasDerivAt
  have hsecond := hDQ.clm_apply hv
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
    hderiv.deriv_eq]
  simpa only [Function.comp_apply, hc0, v, iteratedDeriv_succ, iteratedDeriv_one,
    iteratedDeriv_zero]
    using hsecond.deriv

theorem rescaledProxyExtension_critical_branch_deriv2
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) :
    iteratedDeriv 2 τ 0 = 8 * s * ((m : ℝ) - 1) := by
  let Q : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
  let F := tiltPartial Q
  let D := fderiv ℝ (fderiv ℝ F) (0, 0)
  have hQ : AnalyticAt ℝ Q (0, 0) := rescaledProxyExtension_joint_analytic m s
  have hF : AnalyticAt ℝ F (0, 0) := analyticAt_tiltPartial Q _ hQ
  have hdτ : deriv τ 0 = 4 * s :=
    (rescaledProxyExtension_critical_branch_hasDerivAt m hm s τ hτ hτzero heq).deriv
  have hins : HasDerivAt (fun e : ℝ => (e, (0 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have hslice : (fun e => F (e, 0)) =ᶠ[𝓝 0]
      (fun e => deriv (rescaledProxyExtension m s e) 0) := by
    filter_upwards [hins.continuousAt.eventually hQ.eventually_analyticAt] with e he
    exact tiltPartial_eq_deriv Q (e, 0) he
  have hxx : D (1, 0) (1, 0) = (m : ℝ) * s * (1 - (m : ℝ)) / 2 := by
    have h := analytic_curve_iteratedDeriv2_full F (fun _ => 0) hF analyticAt_const rfl
    simp only [deriv_const, iteratedDeriv_const, show (2 : ℕ) ≠ 0 by omega,
      if_false, map_zero, add_zero] at h
    rw [show ((0, 0) : ℝ × ℝ) = 0 by rfl, map_zero, add_zero] at h
    exact h.symm.trans ((hslice.iteratedDeriv_eq 2).trans
      (rescaledProxyExtension_tilt_deriv_zero_deriv2 m s))
  have hyx : D (1, 0) (0, 1) = (m : ℝ) * ((m : ℝ) - 1) / 12 := by
    have hfirst := (analyticAt_tiltPartial F _ hF).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt_of_eq 0 hins rfl
    have hslice2 : (fun e => tiltPartial F (e, 0)) =ᶠ[𝓝 0]
        (fun e => iteratedDeriv 2 (rescaledProxyExtension m s e) 0) := by
      filter_upwards [hins.continuousAt.eventually hQ.eventually_analyticAt] with e he
      exact tiltPartial2_eq_iteratedDeriv2 Q (e, 0) he
    rw [← analytic_directional_fderiv F (0, 0) (1, 0) (0, 1) hF]
    exact hfirst.deriv.symm.trans (hslice2.deriv_eq.trans
      (rescaledProxyExtension_tilt_deriv2_zero_hasDerivAt m s).deriv)
  have hxy : D (0, 1) (1, 0) = (m : ℝ) * ((m : ℝ) - 1) / 12 := by
    have hsymm := (hF.contDiffAt : ContDiffAt ℝ ⊤ F (0, 0)).isSymmSndFDerivAt (by simp)
    exact (hsymm (0, 1) (1, 0)).trans hyx
  have hyy : D (0, 1) (0, 1) = 0 := by
    rw [← analytic_directional_fderiv F (0, 0) (0, 1) (0, 1) hF]
    change tiltPartial (tiltPartial F) (0, 0) = _
    rw [tiltPartial2_eq_iteratedDeriv2 F (0, 0) hF]
    have hslice3 : (fun t => F (0, t)) =ᶠ[𝓝 0]
        deriv (rescaledProxyExtension m s 0) := by
      have hc : ContinuousAt (fun t : ℝ => ((0 : ℝ), t)) 0 :=
        continuousAt_const.prodMk continuousAt_id
      filter_upwards [hc.eventually hQ.eventually_analyticAt] with t ht
      exact tiltPartial_eq_deriv Q (0, t) ht
    rw [hslice3.iteratedDeriv_eq]
    exact (congrFun (iteratedDeriv_succ' (n := 2)
      (f := rescaledProxyExtension m s 0)) 0).symm.trans
        (rescaledProxyExtension_limit_deriv3 m s)
  have hy : fderiv ℝ F (0, 0) (0, 1) = -(m : ℝ) / 48 := by
    change tiltPartial (tiltPartial Q) (0, 0) = _
    rw [tiltPartial2_eq_iteratedDeriv2 Q (0, 0) hQ]
    exact rescaledProxyExtension_limit_deriv2 m s
  have hpath : Tendsto (fun e : ℝ => (e, τ e)) (𝓝 0) (𝓝 (0, 0)) := by
    have h := continuousAt_id.prodMk hτ.continuousAt
    rwa [ContinuousAt, hτzero] at h
  have hzero : (fun e => F (e, τ e)) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [hpath.eventually heq, hpath.eventually hQ.eventually_analyticAt]
      with e he ha
    rw [show F (e, τ e) = deriv (rescaledProxyExtension m s e) (τ e) from
      tiltPartial_eq_deriv Q (e, τ e) ha]
    exact he.mpr rfl
  have hsecond := analytic_curve_iteratedDeriv2_full F τ hF hτ hτzero
  rw [hzero.iteratedDeriv_eq, iteratedDeriv_const] at hsecond
  norm_num only [show (2 : ℕ) ≠ 0 by omega, if_false] at hsecond
  rw [hdτ] at hsecond
  change 0 = D (1, 4 * s) (1, 4 * s) +
    fderiv ℝ F (0, 0) (0, iteratedDeriv 2 τ 0) at hsecond
  rw [show ((1, 4 * s) : ℝ × ℝ) = (1, 0) + (4 * s) • ((0, 1) : ℝ × ℝ) by
    ext <;> simp,
    show ((0, iteratedDeriv 2 τ 0) : ℝ × ℝ) =
      iteratedDeriv 2 τ 0 • ((0, 1) : ℝ × ℝ) by ext <;> simp] at hsecond
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
    hxx, hyx, hxy, hyy, hy] at hsecond
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  nlinarith

/-- The branch is the actual unique global optimizer for every sufficiently
large valid population. The displayed remainder is in inverse population. -/
theorem actualHypergeomProxy_tilt_second_analytic_expansion
    (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ τ T : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ AnalyticAt ℝ T 0 ∧
      τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ e, τ e = 4 * s * e + 4 * s * ((m : ℝ) - 1) * e ^ 2 + e ^ 3 * T e) ∧
      (fun e => τ e - 4 * s * e - 4 * s * ((m : ℝ) - 1) * e ^ 2)
        =O[𝓝 0] (fun e => e ^ 3) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
        2 * (k : ℝ) + s = (N : ℝ) → ∀ t : ℝ,
        (∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) ↔
          t = τ e) := by
  obtain ⟨τ, hτ, hz, hd, heq⟩ :=
    rescaledProxyExtension_analytic_critical_branch_leading m hm s
  have hdd : iteratedDeriv 2 τ 0 / 2 = 4 * s * ((m : ℝ) - 1) := by
    rw [rescaledProxyExtension_critical_branch_deriv2 m hm s τ hτ hz heq]
    ring
  obtain ⟨T, hT, hTeq, hTO⟩ := analytic_quadratic_remainder τ hτ
  refine ⟨τ, T, hτ, hT, hz, hd, ?_, ?_,
    actualHypergeomProxy_critical_branch_is_global m hm s τ heq⟩
  · simpa only [hz, hd.deriv, hdd, zero_add] using hTeq
  · simpa only [hz, hd.deriv, hdd, sub_zero] using hTO

end

end ExactHoeffding
