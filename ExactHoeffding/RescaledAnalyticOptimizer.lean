import ExactHoeffding.AnalyticImplicitTilt
import ExactHoeffding.ActualUniqueOptimizer
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # The analytic branch is the actual unique global optimizing tilt

The implicit equation is the derivative of the actual removable proxy.
Localization and existence of actual global maxima identify the branch;
neither an optimizing selection nor its analyticity is an assumption.
-/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

theorem rescaledProxyExtension_limit_deriv_zero (m : ℕ) (hm : 0 < m) (s : ℝ) :
    deriv (rescaledProxyExtension m s 0) 0 = 0 := by
  have hmax : IsLocalMax (rescaledProxyExtension m s 0) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t = 0
    · simp only [ht, le_refl]
    · exact (rescaledProxyExtension_limit_strict m hm s t ht).le
  exact hmax.deriv_eq_zero

theorem rescaledProxyExtension_analytic_critical_branch
    (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ τ : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ τ 0 = 0 ∧
      (∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
        deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) := by
  let F : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
  have hF : AnalyticAt ℝ F (0, 0) := rescaledProxyExtension_joint_analytic m s
  have hzero : tiltPartial F (0, 0) = 0 := by
    rw [tiltPartial_eq_deriv F (0, 0) hF]
    exact rescaledProxyExtension_limit_deriv_zero m hm s
  have hnonzero : tiltPartial (tiltPartial F) (0, 0) ≠ 0 := by
    rw [tiltPartial2_eq_iteratedDeriv2 F (0, 0) hF]
    exact ne_of_lt (rescaledProxyExtension_limit_deriv2_neg m hm s)
  obtain ⟨τ, hτ, hτzero, heq⟩ := analytic_implicit_tilt (tiltPartial F)
    (analyticAt_tiltPartial F (0, 0) hF) hzero hnonzero
  refine ⟨τ, hτ, hτzero, ?_⟩
  filter_upwards [heq, hF.eventually_analyticAt] with u hu hFu
  simpa only [tiltPartial_eq_deriv F u hFu] using hu

/-- A single analytic branch describes all sufficiently large admissible
integer populations, not just a preselected sequence of optimizers. -/
theorem actualHypergeomProxy_analytic_global_optimizer
    (m : ℕ) (hmpos : 0 < m) (s : ℝ) :
    ∃ τ : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ τ 0 = 0 ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
        2 * (k : ℝ) + s = (N : ℝ) → ∀ t : ℝ,
        (∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) ↔
          t = τ e) := by
  obtain ⟨τ, hτ, hτzero, heq⟩ :=
    rescaledProxyExtension_analytic_critical_branch m hmpos s
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp heq
  refine ⟨τ, hτ, hτzero, ?_⟩
  filter_upwards [actualHypergeomProxy_eventually_exists_unique_global_max m hmpos s,
    actualHypergeomProxy_eventually_outside_lt_zero m hmpos s (r / 2) (by linarith),
    isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-r / 2) (r / 2) by
      constructor <;> linarith)] with e hexists hloc he
  intro N k hN hk hm heN hbalance
  have hbridge (t : ℝ) : rescaledProxyExtension m s e t =
      actualHypergeomProxy N k m t := by
    rw [heN]
    exact rescaledProxyExtension_hypergeom N k m s t hN hk hm hmpos hbalance
  have hforward (t : ℝ)
      (hmax : ∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) :
      t = τ e := by
    have ht : |t| < r / 2 := by
      by_contra hn
      exact (not_lt_of_ge (hmax 0))
        (hloc N k hN hk hm heN hbalance t (le_of_not_gt hn))
    have hdist : dist (e, t) ((0 : ℝ), (0 : ℝ)) < r := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, max_lt_iff]
      constructor
      · exact abs_lt.mpr ⟨by linarith [he.1], by linarith [he.2]⟩
      · linarith
    have hmaxQ : IsLocalMax (rescaledProxyExtension m s e) t := by
      apply Filter.Eventually.of_forall
      intro u
      simpa only [hbridge] using hmax u
    exact ((hball hdist).mp hmaxQ.deriv_eq_zero).symm
  intro t
  refine ⟨hforward t, ?_⟩
  intro ht
  obtain ⟨v, hv, _⟩ := hexists N k hN hk hm heN hbalance
  have hvτ := hforward v hv
  simpa only [ht, hvτ] using hv

/-- The optimized value itself is analytic in inverse population, once the
actual global optimizer is identified with the analytic branch. -/
theorem rescaledProxyExtension_optimized_value_analytic
    (m : ℕ) (s : ℝ) (τ : ℝ → ℝ) (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0) :
    AnalyticAt ℝ (fun e => rescaledProxyExtension m s e (τ e)) 0 := by
  exact (rescaledProxyExtension_joint_analytic m s).comp_of_eq
    (f := fun e : ℝ => (e, τ e)) (analyticAt_id.prod hτ) (by simp only [hτzero])

theorem rescaledProxyExtension_normalized_optimum_analytic
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0) :
    AnalyticAt ℝ (fun e =>
      4 * rescaledProxyExtension m s e (τ e) / ((m : ℝ) * (1 - (m : ℝ) * e))) 0 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  exact (analyticAt_const.mul
    (rescaledProxyExtension_optimized_value_analytic m s τ hτ hτzero)).div
    (analyticAt_const.mul (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)))
    (by simpa only [mul_zero, sub_zero, mul_one] using hmR)

theorem rescaledProxyExtension_normalized_optimum_zero
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ) (hτzero : τ 0 = 0) :
    4 * rescaledProxyExtension m s 0 (τ 0) / ((m : ℝ) * (1 - (m : ℝ) * 0)) = 1 := by
  rw [hτzero, rescaledProxyExtension_at_zero]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [mul_zero, sub_zero, mul_one]
  field_simp

end

end ExactHoeffding
