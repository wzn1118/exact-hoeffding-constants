import ExactHoeffding.RealMarginProxyDerivatives
import Mathlib.Analysis.Convex.Deriv

/-! # A genuine analytic optimizing critical branch at fixed finite population -/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

/-- The actual objective has strictly negative tilt Hessian at a balanced
finite population. No optimizer is a hypothesis of this theorem. -/
theorem realMarginProxy_balanced_deriv2_neg (N m : ℕ) (hN : 5 ≤ N)
    (hm : 1 ≤ m) (hNm : 2*m ≤ N) :
    iteratedDeriv 2 (realMarginProxy N m 0) 0 < 0 := by
  rw [(realMarginProxy_tilt_derivatives N m hN hNm).2,
    margin_cumulant4_zero N m hN]
  have hNr : (5:ℝ) ≤ N := by exact_mod_cast hN
  have hmr : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hNmR : 2*(m:ℝ) ≤ N := by exact_mod_cast hNm
  have hD : 0 < imbalanceD N m := by
    unfold imbalanceD
    have hprod : (m:ℝ)*((N:ℝ)-m) ≤ (N:ℝ)^2/4 := by
      nlinarith [sq_nonneg ((N:ℝ)-2*m)]
    nlinarith
  have hnum : 0 < (m:ℝ)*((N:ℝ)-m)*imbalanceD N m := by
    exact mul_pos (mul_pos (by linarith) (by linarith)) hD
  have hden : 0 < (8:ℝ)*((N:ℝ)-3)*((N:ℝ)-1)^2 := by
    have h3 : 0 < (N:ℝ)-3 := by linarith
    have h1 : 0 < (N:ℝ)-1 := by linarith
    positivity
  have hneg : -(m:ℝ)*((N:ℝ)-m)*imbalanceD N m /
      (8*((N:ℝ)-3)*((N:ℝ)-1)^2) < 0 := div_neg_of_neg_of_pos (by nlinarith) hden
  exact div_neg_of_neg_of_pos hneg (by norm_num)

/-- For every fixed `N≥5`, including odd `N`, the actual positive real-margin
law has a unique local analytic stationary branch near `(d,t)=(0,0)`. -/
theorem realMarginProxy_analytic_critical_branch (N m : ℕ) (hN : 5 ≤ N)
    (hm : 1 ≤ m) (hNm : 2*m ≤ N) :
    ∃ τ : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ τ 0 = 0 ∧
      (∀ᶠ u : ℝ × ℝ in 𝓝 (0,0),
        deriv (realMarginProxy N m u.1) u.2 = 0 ↔ τ u.1 = u.2) := by
  let F : ℝ × ℝ → ℝ := fun u => realMarginProxy N m u.1 u.2
  have hF : AnalyticAt ℝ F (0,0) := realMarginProxy_joint_analytic N m
    (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have hz : tiltPartial F (0,0) = 0 := by
    rw [tiltPartial_eq_deriv F (0,0) hF]
    exact (realMarginProxy_tilt_derivatives N m hN hNm).1
  have hneg : tiltPartial (tiltPartial F) (0,0) < 0 := by
    rw [tiltPartial2_eq_iteratedDeriv2 F (0,0) hF]
    exact realMarginProxy_balanced_deriv2_neg N m hN hm hNm
  obtain ⟨τ,hτ,hτ0,heq⟩ := analytic_implicit_tilt (tiltPartial F)
    (analyticAt_tiltPartial F (0,0) hF) hz (ne_of_lt hneg)
  refine ⟨τ,hτ,hτ0,?_⟩
  filter_upwards [heq,hF.eventually_analyticAt] with u hu hFu
  simpa only [tiltPartial_eq_deriv F u hFu] using hu

/-- The actual finite-population objective is uniformly strictly concave
on a fixed neighborhood of its balanced maximizing tilt. -/
theorem realMarginProxy_uniform_strictConcave (N m : ℕ) (hN : 5 ≤ N)
    (hm : 1 ≤ m) (hNm : 2*m ≤ N) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ d in 𝓝 (0 : ℝ),
      StrictConcaveOn ℝ (Set.Icc (-δ) δ) (realMarginProxy N m d) := by
  let F : ℝ × ℝ → ℝ := fun u => realMarginProxy N m u.1 u.2
  have hF : AnalyticAt ℝ F (0, 0) := realMarginProxy_joint_analytic N m
    (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have h2 : AnalyticAt ℝ (tiltPartial (tiltPartial F)) (0, 0) :=
    analyticAt_tiltPartial _ _ (analyticAt_tiltPartial F _ hF)
  have hneg : tiltPartial (tiltPartial F) (0, 0) < 0 := by
    rw [tiltPartial2_eq_iteratedDeriv2 F (0, 0) hF]
    exact realMarginProxy_balanced_deriv2_neg N m hN hm hNm
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
  have hcont : ContinuousOn (realMarginProxy N m e) (Icc (-(r / 2)) (r / 2)) := by
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
