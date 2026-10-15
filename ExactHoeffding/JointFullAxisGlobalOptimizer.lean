import ExactHoeffding.AnalyticGlobalMaximum
import ExactHoeffding.JointFullAxisLocalization
import ExactHoeffding.JointBinomialOptimizer

/-! # Analytic global optimization at every interior binomial parameter -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

/-- The actual real-margin proxy has a jointly analytic and uniquely global
maximizing branch around each interior point of the limiting binomial axis. -/
theorem jointProxyExtension_full_axis_analytic_global_optimizer
    (m : ℕ) (hm : 0 < m) (d₀ : ℝ) (hd₀ : d₀ ∈ Ioo (-1 : ℝ) 1) :
    ∃ τ : ℝ × ℝ → ℝ, AnalyticAt ℝ τ (0,d₀) ∧ τ (0,d₀)=jointBinomialTilt d₀ ∧
      (∀ᶠ p in 𝓝 ((0 : ℝ),d₀), ∀ t : ℝ,
        (∀ u : ℝ, jointProxyExtension m p.1 p.2 u ≤ jointProxyExtension m p.1 p.2 t) ↔
          t=τ p) := by
  apply analytic_family_analytic_global_optimizer (jointProxyObjective m)
    (0,d₀) (jointBinomialTilt d₀) (2*(m : ℝ))
  · exact fun t => jointProxyObjective_analytic_full_axis m d₀ t hd₀
  · exact fun t ht => jointProxyExtension_binomial_strict m hm d₀ t hd₀ ht
  · have hmR : (0 : ℝ)<m := by exact_mod_cast hm
    have hvar : 0 < jointProxyExtension m 0 d₀ 0 := by
      rw [jointProxyExtension_zero_tilt_formula m 0 d₀ (by norm_num)]
      have hsq : 0 < 1-d₀^2 := by nlinarith [hd₀.1,hd₀.2]
      simpa only [mul_zero, sub_zero, mul_one] using
        (div_pos (mul_pos hmR hsq) (by norm_num : (0 : ℝ)<4))
    have hmax := (jointProxyExtension_binomial_unique_max m hm d₀ (jointBinomialTilt d₀) hd₀).mpr rfl
    exact lt_of_lt_of_le hvar (hmax (mem_univ 0))
  · positivity
  · exact jointProxyExtension_eventually_tail_bound_free_axis m hm d₀ hd₀
  · rw [jointTiltPartial2_eq_iteratedDeriv2 _ _
      (jointProxyObjective_analytic_full_axis m d₀ (jointBinomialTilt d₀) hd₀)]
    exact jointProxyExtension_binomial_deriv2_neg m hm d₀ hd₀

end
end ExactHoeffding
