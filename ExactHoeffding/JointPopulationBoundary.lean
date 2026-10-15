import ExactHoeffding.JointPopulationEnvelope
import ExactHoeffding.JointContactFirstCorrection

/-! # Exact boundary coefficient of the actual optimized population gap -/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

theorem jointBernoulliSharpBeta_artanh (d : ℝ) (hd : d ∈ Ioo (-1 : ℝ) 1)
    (hd0 : d ≠ 0) :
    4*bernoulliSharpBeta (jointSuccessFraction d)=d/Real.artanh d := by
  have hpne : jointSuccessFraction d ≠ 1/2 := by
    unfold jointSuccessFraction
    intro h
    apply hd0
    linarith
  have ht := jointBinomialTilt_eq_log d hd
  unfold jointBinomialTilt at ht
  have hl : Real.log ((1-jointSuccessFraction d)/jointSuccessFraction d)=2*Real.artanh d := by
    linarith
  rw [bernoulliSharpBeta_eq_formula _ hpne,hl]
  unfold jointSuccessFraction
  field_simp
  <;> ring

theorem jointBinomial_population_correction_contact (d : ℝ)
    (hd : d ∈ Ioo (-1 : ℝ) 1) :
    1-(jointSuccessFraction d*Real.exp (2*jointBinomialTilt d)+(1-jointSuccessFraction d))/
        (1-jointSuccessFraction d+jointSuccessFraction d*Real.exp (jointBinomialTilt d))^2 =
      -4*d^2/(1-d^2) := by
  rw [jointBinomial_contact_population_factor d hd]
  unfold jointSuccessFraction
  have hden : (1-d)/2*(1-(1-d)/2)=(1-d^2)/4 := by ring
  rw [hden]
  rw [div_div_eq_mul_div]
  ring

/-- The actual envelope correction has the manuscript's closed artanh form. -/
theorem jointPopulationEnvelopeCoefficient_formula (m : ℕ) (d : ℝ)
    (hd : d ∈ Ioo (-1 : ℝ) 1) (hd0 : d ≠ 0) :
    jointPopulationEnvelopeCoefficient m d =
      (m:ℝ)*(d/Real.artanh d)-((m:ℝ)-1)*d^2/((1-d^2)*(Real.artanh d)^2) := by
  have hA : Real.artanh d ≠ 0 := by
    have h := jointBinomialTilt_ne_zero d hd hd0
    unfold jointBinomialTilt at h
    exact fun hz => h (by rw [hz,mul_zero])
  have hs : 1-d^2 ≠ 0 := by nlinarith [hd.1,hd.2]
  unfold jointPopulationEnvelopeCoefficient
  rw [show (m:ℝ)*4*bernoulliSharpBeta (jointSuccessFraction d)=
      (m:ℝ)*(4*bernoulliSharpBeta (jointSuccessFraction d)) by ring,
    jointBernoulliSharpBeta_artanh d hd hd0,
    jointBinomial_population_correction_contact d hd]
  unfold jointBinomialTilt
  field_simp [hA,hs]
  <;> ring

/-- The boundary coefficient is identified algebraically from the actual
singleton and fixed-sample envelope derivatives. -/
theorem jointPopulationEnvelope_gap_coefficient (m : ℕ) (d : ℝ)
    (hd : d ∈ Ioo (-1 : ℝ) 1) (hd0 : d ≠ 0) :
    4*bernoulliSharpBeta (jointSuccessFraction d)-jointPopulationEnvelopeCoefficient m d =
      d^2*compactContractionBoundary m d := by
  have hA : Real.artanh d ≠ 0 := by
    have h := jointBinomialTilt_ne_zero d hd hd0
    unfold jointBinomialTilt at h
    exact fun hz => h (by rw [hz,mul_zero])
  have hs : 1-d^2 ≠ 0 := by nlinarith [hd.1,hd.2]
  rw [jointBernoulliSharpBeta_artanh d hd hd0,
    jointPopulationEnvelopeCoefficient_formula m d hd hd0]
  simp only [compactContractionBoundary,if_neg hd0,artanhContractionFactor]
  field_simp [hA,hs,hd0]
  <;> ring

end
end ExactHoeffding
