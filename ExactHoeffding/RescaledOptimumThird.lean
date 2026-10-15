import ExactHoeffding.ActualTiltSecondCoefficient

/-! # Actual optimized proxy: the third inverse-population derivative

The stationary branch is the previously constructed actual global optimizer.
The envelope chain rule below is proved from its critical-point germ.
-/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

def populationPartial (Q : ℝ × ℝ → ℝ) (u : ℝ × ℝ) : ℝ :=
  fderiv ℝ Q u (1, 0)

theorem analyticAt_populationPartial (Q : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (hQ : AnalyticAt ℝ Q u) : AnalyticAt ℝ (populationPartial Q) u := by
  exact (ContinuousLinearMap.apply ℝ ℝ (1, 0)).analyticAt _ |>.comp_of_eq hQ.fderiv rfl

theorem populationPartial_eq_deriv (Q : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (hQ : AnalyticAt ℝ Q u) :
    populationPartial Q u = deriv (fun e => Q (e, u.2)) u.1 := by
  have hins : HasDerivAt (fun e : ℝ => (e, u.2)) (1, 0) u.1 :=
    (hasDerivAt_id u.1).prodMk (hasDerivAt_const u.1 u.2)
  exact (hQ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq u.1 hins rfl).deriv.symm

theorem analytic_partials_commute (Q : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (hQ : AnalyticAt ℝ Q u) :
    tiltPartial (populationPartial Q) u = populationPartial (tiltPartial Q) u := by
  change fderiv ℝ (fun z => fderiv ℝ Q z (1, 0)) u (0, 1) =
    fderiv ℝ (fun z => fderiv ℝ Q z (0, 1)) u (1, 0)
  rw [analytic_directional_fderiv Q u (0, 1) (1, 0) hQ]
  change fderiv ℝ (fderiv ℝ Q) u (0, 1) (1, 0) =
    fderiv ℝ (tiltPartial Q) u (1, 0)
  rw [show tiltPartial Q = (fun z => fderiv ℝ Q z (0, 1)) from rfl,
    analytic_directional_fderiv Q u (1, 0) (0, 1) hQ]
  exact (hQ.contDiffAt : ContDiffAt ℝ ⊤ Q u).isSymmSndFDerivAt (by simp) _ _

theorem rescaledProxyExtension_optimized_value_deriv3
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) :
    iteratedDeriv 3 (fun e => rescaledProxyExtension m s e (τ e)) 0 =
      (m : ℝ) * (1 - (m : ℝ)) * (3 + s ^ 2) / 2 := by
  let Q : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
  let F := tiltPartial Q
  let G := populationPartial Q
  let D := fderiv ℝ (fderiv ℝ G) (0, 0)
  have hQ : AnalyticAt ℝ Q (0, 0) := rescaledProxyExtension_joint_analytic m s
  have hF : AnalyticAt ℝ F (0, 0) := analyticAt_tiltPartial Q _ hQ
  have hG : AnalyticAt ℝ G (0, 0) := analyticAt_populationPartial Q _ hQ
  have hins : HasDerivAt (fun e : ℝ => (e, (0 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have hpop : (fun e => G (e, 0)) =ᶠ[𝓝 0]
      deriv (fun e => rescaledProxyExtension m s e 0) := by
    filter_upwards [hins.continuousAt.eventually hQ.eventually_analyticAt] with e he
    exact populationPartial_eq_deriv Q (e, 0) he
  have htilt : (fun e => F (e, 0)) =ᶠ[𝓝 0]
      (fun e => deriv (rescaledProxyExtension m s e) 0) := by
    filter_upwards [hins.continuousAt.eventually hQ.eventually_analyticAt] with e he
    exact tiltPartial_eq_deriv Q (e, 0) he
  have hcomm : tiltPartial G =ᶠ[𝓝 (0, 0)] populationPartial F := by
    filter_upwards [hQ.eventually_analyticAt] with u hu
    exact analytic_partials_commute Q u hu
  have hxx : D (1, 0) (1, 0) =
      3 * (m : ℝ) * (1 - (m : ℝ)) * (1 - s ^ 2) / 2 := by
    have h := analytic_curve_iteratedDeriv2_full G (fun _ => 0) hG analyticAt_const rfl
    simp only [deriv_const, iteratedDeriv_const, show (2 : ℕ) ≠ 0 by omega, if_false] at h
    rw [show ((0, 0) : ℝ × ℝ) = 0 by rfl, map_zero, add_zero] at h
    rw [hpop.iteratedDeriv_eq] at h
    rw [← iteratedDeriv_succ' (n := 2)] at h
    exact h.symm.trans (rescaledProxyExtension_zero_tilt_deriv3 m s)
  have hFxx : fderiv ℝ (fderiv ℝ F) (0, 0) (1, 0) (1, 0) =
      (m : ℝ) * s * (1 - (m : ℝ)) / 2 := by
    have h := analytic_curve_iteratedDeriv2_full F (fun _ => 0) hF analyticAt_const rfl
    simp only [deriv_const, iteratedDeriv_const, show (2 : ℕ) ≠ 0 by omega, if_false] at h
    rw [show ((0, 0) : ℝ × ℝ) = 0 by rfl, map_zero, add_zero] at h
    exact h.symm.trans ((htilt.iteratedDeriv_eq 2).trans
      (rescaledProxyExtension_tilt_deriv_zero_deriv2 m s))
  have hFxy : fderiv ℝ (fderiv ℝ F) (0, 0) (1, 0) (0, 1) =
      (m : ℝ) * ((m : ℝ) - 1) / 12 := by
    have hfirst := (analyticAt_tiltPartial F _ hF).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt_of_eq 0 hins rfl
    have hslice : (fun e => tiltPartial F (e, 0)) =ᶠ[𝓝 0]
        (fun e => iteratedDeriv 2 (rescaledProxyExtension m s e) 0) := by
      filter_upwards [hins.continuousAt.eventually hQ.eventually_analyticAt] with e he
      exact tiltPartial2_eq_iteratedDeriv2 Q (e, 0) he
    rw [← analytic_directional_fderiv F (0, 0) (1, 0) (0, 1) hF]
    exact hfirst.deriv.symm.trans (hslice.deriv_eq.trans
      (rescaledProxyExtension_tilt_deriv2_zero_hasDerivAt m s).deriv)
  have hyx : D (1, 0) (0, 1) = (m : ℝ) * s * (1 - (m : ℝ)) / 2 := by
    rw [← analytic_directional_fderiv G (0, 0) (1, 0) (0, 1) hG]
    change fderiv ℝ (tiltPartial G) (0, 0) (1, 0) = _
    rw [hcomm.fderiv_eq]
    exact (analytic_directional_fderiv F (0, 0) (1, 0) (1, 0) hF).trans hFxx
  have hxy : D (0, 1) (1, 0) = (m : ℝ) * s * (1 - (m : ℝ)) / 2 := by
    have hsymm := (hG.contDiffAt : ContDiffAt ℝ ⊤ G (0, 0)).isSymmSndFDerivAt (by simp)
    exact (hsymm (0, 1) (1, 0)).trans hyx
  have hyy : D (0, 1) (0, 1) = (m : ℝ) * ((m : ℝ) - 1) / 12 := by
    rw [← analytic_directional_fderiv G (0, 0) (0, 1) (0, 1) hG]
    change fderiv ℝ (tiltPartial G) (0, 0) (0, 1) = _
    rw [hcomm.fderiv_eq]
    rw [show populationPartial F = (fun u => fderiv ℝ F u (1, 0)) from rfl,
      analytic_directional_fderiv F (0, 0) (0, 1) (1, 0) hF]
    have hsymm := (hF.contDiffAt : ContDiffAt ℝ ⊤ F (0, 0)).isSymmSndFDerivAt (by simp)
    exact (hsymm (0, 1) (1, 0)).trans hFxy
  have hy : fderiv ℝ G (0, 0) (0, 1) = (m : ℝ) * s / 12 := by
    change tiltPartial G (0, 0) = _
    rw [hcomm.eq_of_nhds]
    have hfirst := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hins rfl
    exact hfirst.deriv.symm.trans (htilt.deriv_eq.trans
      (rescaledProxyExtension_mixed_hasDerivAt m s).deriv)
  have hpath : Tendsto (fun e : ℝ => (e, τ e)) (𝓝 0) (𝓝 (0, 0)) := by
    have h := continuousAt_id.prodMk hτ.continuousAt
    rwa [ContinuousAt, hτzero] at h
  have henv : deriv (fun e => Q (e, τ e)) =ᶠ[𝓝 0] (fun e => G (e, τ e)) := by
    filter_upwards [hpath.eventually heq, hpath.eventually hQ.eventually_analyticAt,
      hτ.eventually_analyticAt] with e he ha heτ
    have hcritical : fderiv ℝ Q (e, τ e) (0, 1) = 0 := by
      change tiltPartial Q (e, τ e) = _
      rw [tiltPartial_eq_deriv Q (e, τ e) ha]
      exact he.mpr rfl
    have hc : HasDerivAt (fun e : ℝ => (e, τ e)) (1, deriv τ e) e :=
      (hasDerivAt_id e).prodMk heτ.differentiableAt.hasDerivAt
    have hd := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq e hc rfl
    change HasDerivAt (fun e => Q (e, τ e)) _ e at hd
    rw [hd.deriv]
    rw [show ((1, deriv τ e) : ℝ × ℝ) =
      (1, 0) + deriv τ e • ((0, 1) : ℝ × ℝ) by ext <;> simp,
      map_add, map_smul, hcritical, smul_zero, add_zero]
    rfl
  have hdτ : deriv τ 0 = 4 * s :=
    (rescaledProxyExtension_critical_branch_hasDerivAt m hm s τ hτ hτzero heq).deriv
  have hddτ := rescaledProxyExtension_critical_branch_deriv2 m hm s τ hτ hτzero heq
  rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ', henv.iteratedDeriv_eq,
    analytic_curve_iteratedDeriv2_full G τ hG hτ hτzero, hdτ, hddτ]
  change D (1, 4 * s) (1, 4 * s) +
    fderiv ℝ G (0, 0) (0, 8 * s * ((m : ℝ) - 1)) = _
  rw [show ((1, 4 * s) : ℝ × ℝ) =
    (1, 0) + (4 * s) • ((0, 1) : ℝ × ℝ) by ext <;> simp,
    show ((0, 8 * s * ((m : ℝ) - 1)) : ℝ × ℝ) =
      (8 * s * ((m : ℝ) - 1)) • ((0, 1) : ℝ × ℝ) by ext <;> simp]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul,
    hxx, hyx, hxy, hyy, hy]
  ring

end

end ExactHoeffding
