import ExactHoeffding.JointOptimizedValue

/-! # Exact axis cancellations of the actual jointly optimized gap -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

/-- At zero inverse population the entire removable proxy is precisely the
binomial multiple of its one-draw counterpart, including zero tilt. -/
theorem jointProxyExtension_binomial_scaling (m : ℕ) (hm : 1 ≤ m) (d t : ℝ) :
    jointProxyExtension m 0 d t = (m : ℝ)*jointProxyExtension 1 0 d t := by
  by_cases ht : t=0
  · subst t
    rw [jointProxyExtension_zero_tilt_formula m 0 d (by norm_num),
      jointProxyExtension_zero_tilt_formula 1 0 d (by norm_num)]
    ring
  · rw [jointProxyExtension_eq_quotient m hm 0 d t ht,
      jointProxyExtension_eq_quotient 1 (by omega) 0 d t ht,
      jointMGF_at_zero, jointMGF_at_zero, Real.log_pow]
    norm_num only [Nat.cast_one, pow_one]
    unfold jointMean
    norm_num only [Nat.cast_one, one_mul]
    ring

/-- The actual optimized gap, in the manuscript's normalization. -/
def jointOptimizedGap (m : ℕ) (τ₁ τm : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  jointNormalizedValue 1 τ₁ p - jointNormalizedValue m τm p

theorem jointOptimizedGap_analytic (m : ℕ) (hm : 0 < m)
    (τ₁ τm : ℝ × ℝ → ℝ) (h₁ : AnalyticAt ℝ τ₁ (0, 0))
    (hmτ : AnalyticAt ℝ τm (0, 0)) (hz₁ : τ₁ (0, 0)=0) (hzm : τm (0, 0)=0) :
    AnalyticAt ℝ (jointOptimizedGap m τ₁ τm) (0, 0) :=
  (jointNormalizedValue_analytic 1 (by omega) τ₁ h₁ hz₁).sub
    (jointNormalizedValue_analytic m hm τm hmτ hzm)

/-- Equality on the zero-population-correction axis is proved from the
actual global maxima of the two binomial objectives. -/
theorem jointOptimizedGap_population_axis_zero (m : ℕ) (hm : 0 < m)
    (τ₁ τm : ℝ × ℝ → ℝ)
    (hmax₁ : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), ∀ t : ℝ,
      (∀ u : ℝ, jointProxyExtension 1 p.1 p.2 u ≤ jointProxyExtension 1 p.1 p.2 t) ↔ t=τ₁ p)
    (hmaxm : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), ∀ t : ℝ,
      (∀ u : ℝ, jointProxyExtension m p.1 p.2 u ≤ jointProxyExtension m p.1 p.2 t) ↔ t=τm p) :
    ∀ᶠ d in 𝓝 (0 : ℝ), jointOptimizedGap m τ₁ τm (0, d)=0 := by
  have hc : Tendsto (fun d : ℝ => ((0 : ℝ), d)) (𝓝 0) (𝓝 (0, 0)) :=
    continuousAt_const.prodMk continuousAt_id
  filter_upwards [hc.eventually hmax₁, hc.eventually hmaxm] with d h₁ hm'
  have hone := ((h₁ (τ₁ (0, d))).mpr rfl) (τm (0, d))
  have hmany := ((hm' (τm (0, d))).mpr rfl) (τ₁ (0, d))
  rw [jointProxyExtension_binomial_scaling m hm d,
    jointProxyExtension_binomial_scaling m hm d] at hmany
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heq : jointProxyExtension 1 0 d (τ₁ (0, d)) =
      jointProxyExtension 1 0 d (τm (0, d)) := by nlinarith
  unfold jointOptimizedGap jointNormalizedValue
  simp only [mul_zero, sub_zero, mul_one, Nat.cast_one]
  rw [jointProxyExtension_binomial_scaling m hm d, heq]
  field_simp
  ring

/-- The optimized gap has both exact vanishing axes and is even in the
independent imbalance variable; these identities hold for constructed,
globally optimizing analytic branches. -/
theorem jointOptimizedGap_constructed (m : ℕ) (hm : 0 < m) :
    ∃ τ₁ τm : ℝ × ℝ → ℝ,
      AnalyticAt ℝ τ₁ (0, 0) ∧ AnalyticAt ℝ τm (0, 0) ∧
      τ₁ (0, 0)=0 ∧ τm (0, 0)=0 ∧
      AnalyticAt ℝ (jointOptimizedGap m τ₁ τm) (0, 0) ∧
      (∀ᶠ d in 𝓝 (0 : ℝ), jointOptimizedGap m τ₁ τm (0, d)=0) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), jointOptimizedGap m τ₁ τm (e, 0)=0) ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
        jointOptimizedGap m τ₁ τm (p.1, -p.2)=jointOptimizedGap m τ₁ τm p) := by
  obtain ⟨τ₁, h₁, hz₁, hmax₁, hbal₁, href₁⟩ :=
    jointProxyExtension_analytic_global_optimizer 1 (by omega)
  obtain ⟨τm, hmτ, hzm, hmaxm, hbalm, hrefm⟩ :=
    jointProxyExtension_analytic_global_optimizer m hm
  refine ⟨τ₁, τm, h₁, hmτ, hz₁, hzm,
    jointOptimizedGap_analytic m hm τ₁ τm h₁ hmτ hz₁ hzm,
    jointOptimizedGap_population_axis_zero m hm τ₁ τm hmax₁ hmaxm, ?_, ?_⟩
  · filter_upwards [jointNormalizedValue_balanced 1 (by omega) τ₁ hbal₁,
      jointNormalizedValue_balanced m hm τm hbalm] with e he₁ hem
    simp only [jointOptimizedGap, he₁, hem, sub_self]
  · filter_upwards [jointNormalizedValue_reflection 1 (by omega) τ₁ h₁ hz₁ href₁,
      jointNormalizedValue_reflection m hm τm hmτ hzm hrefm] with p hp₁ hpm
    simp only [jointOptimizedGap, hp₁, hpm]

end

end ExactHoeffding
