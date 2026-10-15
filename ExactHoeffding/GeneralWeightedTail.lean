import ExactHoeffding.ExchangeableConstants
import ExactHoeffding.ProjectedWeights
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MeasureTheory

namespace ExactHoeffding

/-- Exponential Markov optimization for an actual exchangeable probability
measure supported on the cube. -/
theorem exchangeable_coefficient_tail_bound (N : ℕ) (C : ℝ)
    (hC : IsExchangeableCoefficient N C)
    (μ : Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex : FiniteExchangeableMeasure μ) (hcube : ∀ᵐx ∂μ,x∈realCube N)
    (a : Fin N→ℝ) (ha : ∑i,a i=0) (hV : 0<C*(∑i,(a i)^2))
    (s : ℝ) (hs : 0<s) :
    μ.real {x | s≤∑i,a i*x i}≤Real.exp (-s^2/(2*C*(∑i,(a i)^2))) := by
  let V := C*(∑i,(a i)^2)
  let t := s/V
  have ht : 0<t := div_pos hs hV
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (MeasureTheory.ae_of_all μ (fun x => (Real.exp_pos (t*∑i,a i*x i)).le))
    (expContrast_integrable μ hcube a t) (Real.exp (t*s))
  have hevent : {x : Fin N→ℝ | Real.exp (t*s)≤Real.exp (t*∑i,a i*x i)}=
      {x | s≤∑i,a i*x i} := by
    ext x
    simp only [Set.mem_ofPred_eq,Real.exp_le_exp]
    exact mul_le_mul_iff_right₀ ht
  rw [hevent] at hmark
  have hmgf := hC μ inferInstance hex hcube a ha t
  have h := hmark.trans hmgf
  have hdiv : μ.real {x : Fin N→ℝ | s≤∑i,a i*x i}≤
      Real.exp (C*t^2*(∑i,(a i)^2)/2)/Real.exp (t*s) := by
    apply (le_div_iff₀ (Real.exp_pos (t*s))).mpr
    simpa only [mul_comm] using h
  apply hdiv.trans_eq
  rw [←Real.exp_sub]
  congr 1
  have hCV : C≠0 := left_ne_zero_of_mul hV.ne'
  have hnorm : (∑i,(a i)^2)≠0 := right_ne_zero_of_mul hV.ne'
  dsimp [t,V]
  field_simp [hCV,hnorm]
  ring

/-- The manuscript's weighted contrast is normalized by the squared norm
after projection onto the zero-sum subspace. -/
theorem exchangeable_weighted_tail_bound (N : ℕ) (hN : 0<N) (C : ℝ)
    (hC : IsExchangeableCoefficient N C)
    (μ : Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex : FiniteExchangeableMeasure μ) (hcube : ∀ᵐx ∂μ,x∈realCube N)
    (w : Fin N→ℝ) (hV : 0<C*projectedWeightVariance w) (s : ℝ) (hs : 0<s) :
    μ.real {x | s≤∑i,w i*(x i-(∑j,x j)/(N:ℝ))}≤
      Real.exp (-s^2/(2*C*projectedWeightVariance w)) := by
  have h := exchangeable_coefficient_tail_bound N C hC μ hex hcube
    (centerContrast w) (centerContrast_sum_zero N hN w)
    (by rw [centerContrast_sq_norm N hN w]; exact hV) s hs
  simp_rw [centerContrast_linear_contrast N w,centerContrast_sq_norm N hN w] at h
  exact h

/-- Exact exponent at the standard confidence threshold. -/
theorem gaussian_threshold_exponent (V δ : ℝ) (hV : 0<V) (hδ : 0<δ) (hδ1 : δ<1) :
    Real.exp (-(Real.sqrt (2*V*Real.log (1/δ)))^2/(2*V))=δ := by
  have hlog : 0<Real.log (1/δ) := Real.log_pos ((one_lt_div hδ).mpr hδ1)
  have hr : 0≤2*V*Real.log (1/δ) := by positivity
  rw [Real.sq_sqrt hr]
  have he : -(2*V*Real.log (1/δ))/(2*V)= -Real.log (1/δ) := by
    field_simp [hV.ne']
  rw [he,one_div,Real.log_inv,neg_neg,Real.exp_log hδ]

theorem exchangeable_weighted_confidence_bound (N : ℕ) (hN : 0<N) (C : ℝ)
    (hC : IsExchangeableCoefficient N C)
    (μ : Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex : FiniteExchangeableMeasure μ) (hcube : ∀ᵐx ∂μ,x∈realCube N)
    (w : Fin N→ℝ) (hV : 0<C*projectedWeightVariance w)
    (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1) :
    μ.real {x | Real.sqrt (2*C*projectedWeightVariance w*Real.log (1/δ))≤
      ∑i,w i*(x i-(∑j,x j)/(N:ℝ))}≤δ := by
  have hlog : 0<Real.log (1/δ) := Real.log_pos ((one_lt_div hδ).mpr hδ1)
  have hs : 0<Real.sqrt (2*C*projectedWeightVariance w*Real.log (1/δ)) :=
    Real.sqrt_pos.mpr (by nlinarith)
  have h := exchangeable_weighted_tail_bound N hN C hC μ hex hcube w hV
    (Real.sqrt (2*C*projectedWeightVariance w*Real.log (1/δ))) hs
  apply h.trans_eq
  simpa only [mul_assoc] using
    gaussian_threshold_exponent (C*projectedWeightVariance w) δ hV hδ hδ1

end ExactHoeffding
