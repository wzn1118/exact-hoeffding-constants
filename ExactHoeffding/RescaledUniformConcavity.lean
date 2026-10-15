import ExactHoeffding.LimitProxyCurvature
import ExactHoeffding.AnalyticTiltPartial
import Mathlib.Analysis.Convex.Deriv

/-! # Uniform strict concavity near inverse population and tilt zero -/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

theorem rescaledProxyExtension_uniform_strictConcave (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ e in 𝓝 (0 : ℝ),
      StrictConcaveOn ℝ (Icc (-δ) δ) (rescaledProxyExtension m s e) := by
  let F : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
  have hF : AnalyticAt ℝ F (0, 0) := rescaledProxyExtension_joint_analytic m s
  have h2 : AnalyticAt ℝ (tiltPartial (tiltPartial F)) (0, 0) :=
    analyticAt_tiltPartial _ _ (analyticAt_tiltPartial F _ hF)
  have hneg : tiltPartial (tiltPartial F) (0, 0) < 0 := by
    rw [tiltPartial2_eq_iteratedDeriv2 F (0, 0) hF]
    exact rescaledProxyExtension_limit_deriv2_neg m hm s
  have hevent : ∀ᶠ u in 𝓝 ((0 : ℝ), (0 : ℝ)),
      AnalyticAt ℝ F u ∧ tiltPartial (tiltPartial F) u < 0 :=
    hF.eventually_analyticAt.and (h2.continuousAt.eventually_lt continuousAt_const hneg)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r / 2, by linarith, ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-r / 2) (r / 2) by
    constructor <;> linarith)] with e he
  have hall (t : ℝ) (ht : t ∈ Icc (-(r / 2)) (r / 2)) :
      AnalyticAt ℝ F (e, t) ∧ tiltPartial (tiltPartial F) (e, t) < 0 := by
    apply hball
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, max_lt_iff]
    constructor
    · exact abs_lt.mpr ⟨by linarith [he.1], by linarith [he.2]⟩
    · exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcont : ContinuousOn (rescaledProxyExtension m s e) (Icc (-(r / 2)) (r / 2)) := by
    intro t ht
    have ha := (hall t ht).1
    have hins : AnalyticAt ℝ (fun u : ℝ => (e, u)) t :=
      analyticAt_const.prod analyticAt_id
    exact (ha.comp_of_eq hins rfl).continuousAt.continuousWithinAt
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hcont
  intro t ht
  have ht' := interior_subset ht
  rw [← iteratedDeriv_eq_iterate]
  change iteratedDeriv 2 (fun u => F (e, u)) t < 0
  rw [← tiltPartial2_eq_iteratedDeriv2 F (e, t) (hall t ht').1]
  exact (hall t ht').2

end

end ExactHoeffding
