import ExactHoeffding.ExactParityConstants
import ExactHoeffding.GeneralWeightedTail

open MeasureTheory

namespace ExactHoeffding

theorem paritySharpConstant_pos (N : ℕ) (hN : 2 ≤ N) :
    0 < paritySharpConstant N := by
  rw [← exact_finite_exchangeability_constants N hN,
    exactExchangeableConstant_eq_variational N hN]
  exact hypergeomVariationalConstant_pos N hN

/-- The parity-exact coefficient applies directly to the weighted,
population-centered contrast under every exchangeable law on the cube. -/
theorem sharp_weighted_exp_bound (N : ℕ) (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hex : FiniteExchangeableMeasure μ) (hcube : ∀ᵐ x ∂μ, x ∈ realCube N)
    (w : Fin N → ℝ) (t : ℝ) :
    (∫ x, Real.exp (t * ∑ i, w i * (x i - (∑ j, x j) / (N : ℝ))) ∂μ) ≤
      Real.exp (paritySharpConstant N * t ^ 2 * projectedWeightVariance w / 2) := by
  have h := paritySharpConstant_is_valid N hN μ inferInstance hex hcube
    (centerContrast w) (centerContrast_sum_zero N (by omega) w) t
  simpa only [expContrast, centerContrast_linear_contrast,
    centerContrast_sq_norm N (by omega) w] using h

/-- The optimal finite-exchangeability coefficient in the weighted tail bound. -/
theorem sharp_weighted_tail_bound (N : ℕ) (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hex : FiniteExchangeableMeasure μ) (hcube : ∀ᵐ x ∂μ, x ∈ realCube N)
    (w : Fin N → ℝ) (hw : 0 < projectedWeightVariance w)
    (s : ℝ) (hs : 0 < s) :
    μ.real {x | s ≤ ∑ i, w i * (x i - (∑ j, x j) / (N : ℝ))} ≤
      Real.exp (-s ^ 2 / (2 * paritySharpConstant N * projectedWeightVariance w)) :=
  exchangeable_weighted_tail_bound N (by omega) (paritySharpConstant N)
    (paritySharpConstant_is_valid N hN) μ hex hcube w
    (mul_pos (paritySharpConstant_pos N hN) hw) s hs

/-- Constant weights give the zero contrast at every point, including laws
without exchangeability or a support assumption. -/
theorem weighted_tail_zero_of_projectedVariance_zero (N : ℕ) (hN : 0 < N)
    (μ : Measure (Fin N → ℝ)) (w : Fin N → ℝ)
    (hw : projectedWeightVariance w = 0) (s : ℝ) (hs : 0 < s) :
    μ.real {x | s ≤ ∑ i, w i * (x i - (∑ j, x j) / (N : ℝ))} = 0 := by
  have hwc := (projectedWeightVariance_eq_zero_iff N hN w).1 hw
  have hz (x : Fin N → ℝ) :
      (∑ i, w i * (x i - (∑ j, x j) / (N : ℝ))) = 0 := by
    rw [← centerContrast_linear_contrast]
    apply Finset.sum_eq_zero
    intro i _
    simp [centerContrast, hwc i]
  have he : {x : Fin N → ℝ | s ≤ ∑ i, w i * (x i - (∑ j, x j) / (N : ℝ))} =
      ∅ := by
    ext x
    simp [hz x, not_le.mpr hs]
  rw [he]
  simp

/-- The tail bound on the entire weight space, with the zero denominator
handled by its exact deterministic value. -/
theorem sharp_weighted_tail_bound_all (N : ℕ) (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hex : FiniteExchangeableMeasure μ) (hcube : ∀ᵐ x ∂μ, x ∈ realCube N)
    (w : Fin N → ℝ) (s : ℝ) (hs : 0 < s) :
    μ.real {x | s ≤ ∑ i, w i * (x i - (∑ j, x j) / (N : ℝ))} ≤
      if projectedWeightVariance w = 0 then 0 else
        Real.exp (-s ^ 2 / (2 * paritySharpConstant N * projectedWeightVariance w)) := by
  by_cases hw : projectedWeightVariance w = 0
  · rw [if_pos hw, weighted_tail_zero_of_projectedVariance_zero N (by omega) μ w hw s hs]
  · rw [if_neg hw]
    exact sharp_weighted_tail_bound N hN μ hex hcube w
      (lt_of_le_of_ne (projectedWeightVariance_nonnegative N (by omega) w) (Ne.symm hw)) s hs

theorem sharp_weighted_confidence_bound (N : ℕ) (hN : 2 ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hex : FiniteExchangeableMeasure μ) (hcube : ∀ᵐ x ∂μ, x ∈ realCube N)
    (w : Fin N → ℝ) (hw : 0 < projectedWeightVariance w)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ.real {x | Real.sqrt (2 * paritySharpConstant N * projectedWeightVariance w *
        Real.log (1 / δ)) ≤ ∑ i, w i * (x i - (∑ j, x j) / (N : ℝ))} ≤ δ :=
  exchangeable_weighted_confidence_bound N (by omega) (paritySharpConstant N)
    (paritySharpConstant_is_valid N hN) μ hex hcube w
    (mul_pos (paritySharpConstant_pos N hN) hw) δ hδ hδ1

end ExactHoeffding
