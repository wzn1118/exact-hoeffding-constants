import ExactHoeffding.ActualCompactFirstCorrection

/-! # The compact first population correction for every positive sample size -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

/-- The singleton closed formula supplies the remaining positive sample size
in the explicit first derivative of the actual optimized supremum. -/
theorem actualCompactFirstCorrection_eq_parameterPartial_pos
    (m : ℕ) (hm : 0 < m) (d : ℝ) (hd₀ : 0 ≤ d) (hd₁ : d < 1) :
    actualCompactFirstCorrection m d =
      parameterPartial (jointOptimalValue m) (1,0) (0,d) := by
  by_cases hm₁ : m = 1
  · subst m
    have hd : d ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hd₁⟩
    rw [parameterPartial_fst_eq_deriv (jointOptimalValue 1) (0,d)
      (jointOptimalValue_analytic_full_axis 1 (by omega) d hd).differentiableAt]
    by_cases hz : d = 0
    · subst d
      simpa only [actualCompactFirstCorrection_zero] using
        (jointOptimalValue_balanced_hasDerivAt_population_zero 1 (by omega)).deriv.symm
    · simpa [actualCompactFirstCorrection,hz] using
        (jointOptimalValue_singleton_hasDerivAt_population_zero d
          (lt_of_le_of_ne hd₀ (Ne.symm hz)) hd₁).deriv.symm
  · exact actualCompactFirstCorrection_eq_parameterPartial m (by omega) d hd₀ hd₁

/-- Continuity through balance includes the exact singleton coefficient. -/
theorem actualCompactFirstCorrection_continuousOn_pos
    (m : ℕ) (hm : 0 < m) (d₀ : ℝ) (hd₁ : d₀ < 1) :
    ContinuousOn (actualCompactFirstCorrection m) (Icc 0 d₀) := by
  have hEq : EqOn (actualCompactFirstCorrection m)
      (fun d => parameterPartial (jointOptimalValue m) (1,0) (0,d)) (Icc 0 d₀) := by
    intro d hd
    exact actualCompactFirstCorrection_eq_parameterPartial_pos m hm d hd.1
      (lt_of_le_of_lt hd.2 hd₁)
  apply ContinuousOn.congr _ hEq
  intro d hd
  have hdi : d ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hd.1],lt_of_le_of_lt hd.2 hd₁⟩
  exact ((parameterPartial_analytic (jointOptimalValue m) (1,0) (0,d)
    (jointOptimalValue_analytic_full_axis m hm d hdi)).continuousAt.comp_of_eq
      (continuousAt_const.prodMk continuousAt_id) rfl).continuousWithinAt

/-- A single quadratic error bound on a compact success-proportion interval,
with the displayed closed coefficient and its balanced value, for all `m ≥ 1`. -/
theorem jointOptimalValue_uniform_explicit_first_correction_pos
    (m : ℕ) (hm : 0 < m) (d₀ : ℝ) (hd₀ : 0 ≤ d₀) (hd₁ : d₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ e in 𝓝 (0:ℝ), ∀ d ∈ Icc 0 d₀,
      |jointOptimalValue m (e,d) - 4*bernoulliSharpBeta (jointSuccessFraction d) -
        e*actualCompactFirstCorrection m d| ≤ C*e^2 := by
  obtain ⟨C,hC,hrem⟩ := jointOptimalValue_uniform_population_remainder m hm d₀ hd₀ hd₁
  refine ⟨C,hC,?_⟩
  filter_upwards [hrem] with e he
  intro d hd
  rw [actualCompactFirstCorrection_eq_parameterPartial_pos m hm d hd.1
    (lt_of_le_of_lt hd.2 hd₁)]
  exact he d hd

end
end ExactHoeffding
