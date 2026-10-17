import ExactHoeffding.FiniteSupportLawEnvelope
import ExactHoeffding.FiniteSupportLawIntegration

/-! # Finite-limit endpoint continuation of the actual-law envelope theorem

The limits below are the finite one-sided limits of the displayed envelope
integrals. No continuity of the envelope at a support endpoint, and no
one-sided limit of the Legendre rate, is supplied as a hypothesis.
-/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

/-- Upper-endpoint rate comparison in the original support coordinates. -/
theorem FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeRight_endpoint
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in L.mean0..v, (v-u)/Q u)
      (𝓝[<] (L.value L.hiIndex)) (𝓝 Jlim)) :
    Jlim ≤ L.rawLegendreRate (L.value L.hiIndex) := by
  have hμhi : L.mean0 < L.value L.hiIndex := by
    have h := (L.toTiltCurve L.variance_pos).hmuhi
    change 0 < L.value L.hiIndex - L.mean0 at h
    linarith
  have hinner : ∀ᶠ v in 𝓝[<] (L.value L.hiIndex),
      (∫ u : ℝ in L.mean0..v, (v-u)/Q u) ≤
        L.rawLegendreRate (L.value L.hiIndex) := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Ioi_mem_nhds hμhi] with v hv
    intro hvhi
    change L.mean0 < v at hv
    change v < L.value L.hiIndex at hvhi
    have hpoint := L.rawLegendreRate_ge_meanEnvelopeRight Q hQ hQpos hV hv.le hvhi
    have hend := finiteSupportLawData_legendreRate_le_hi L
      (show 0 ≤ v - L.mean0 by linarith)
      (show v - L.mean0 < L.value L.hiIndex - L.mean0 by linarith)
    rw [← L.rawLegendreRate_eq_centered v,
      ← L.rawLegendreRate_eq_centered (L.value L.hiIndex)] at hend
    exact hpoint.trans hend
  exact le_of_tendsto hJ hinner

/-- Lower-endpoint rate comparison in the original support coordinates. -/
theorem FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeLeft_endpoint
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in v..L.mean0, (u-v)/Q u)
      (𝓝[>] (L.value L.loIndex)) (𝓝 Jlim)) :
    Jlim ≤ L.rawLegendreRate (L.value L.loIndex) := by
  have hloμ : L.value L.loIndex < L.mean0 := by
    have h := (L.toTiltCurve L.variance_pos).hlomu
    change L.value L.loIndex - L.mean0 < 0 at h
    linarith
  have hinner : ∀ᶠ v in 𝓝[>] (L.value L.loIndex),
      (∫ u : ℝ in v..L.mean0, (u-v)/Q u) ≤
        L.rawLegendreRate (L.value L.loIndex) := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Iio_mem_nhds hloμ] with v hv
    intro hvlo
    change v < L.mean0 at hv
    change L.value L.loIndex < v at hvlo
    have hpoint := L.rawLegendreRate_ge_meanEnvelopeLeft Q hQ hQpos hV hvlo hv.le
    have hend := finiteSupportLawData_legendreRate_le_lo L
      (show L.value L.loIndex - L.mean0 < v - L.mean0 by linarith)
      (show v - L.mean0 ≤ 0 by linarith)
    rw [← L.rawLegendreRate_eq_centered v,
      ← L.rawLegendreRate_eq_centered (L.value L.loIndex)] at hend
    exact hpoint.trans hend
  exact le_of_tendsto hJ hinner

/-- The actual endpoint upper-tail event obeys the finite-limit envelope. -/
theorem FiniteSupportLawData.rawUpperTail_le_meanEnvelope_endpoint
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in L.mean0..v, (v-u)/Q u)
      (𝓝[<] (L.value L.hiIndex)) (𝓝 Jlim)) :
    L.rawUpperTail (L.value L.hiIndex) ≤ Real.exp (-Jlim) := by
  have hrate := L.rawLegendreRate_ge_meanEnvelopeRight_endpoint Q hQ hQpos hV Jlim hJ
  have htail := L.upperTail_le_exp_neg_rate_endpoint
  change L.rawUpperTail (L.value L.hiIndex) ≤
    Real.exp (-finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
      (L.value L.hiIndex - L.mean0)) at htail
  rw [← L.rawLegendreRate_eq_centered (L.value L.hiIndex)] at htail
  exact htail.trans (Real.exp_le_exp.mpr (neg_le_neg hrate))

/-- The actual endpoint lower-tail event obeys the finite-limit envelope. -/
theorem FiniteSupportLawData.rawLowerTail_le_meanEnvelope_endpoint
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in v..L.mean0, (u-v)/Q u)
      (𝓝[>] (L.value L.loIndex)) (𝓝 Jlim)) :
    L.rawLowerTail (L.value L.loIndex) ≤ Real.exp (-Jlim) := by
  have hrate := L.rawLegendreRate_ge_meanEnvelopeLeft_endpoint Q hQ hQpos hV Jlim hJ
  have htail := L.lowerTail_le_exp_neg_rate_endpoint
  change L.rawLowerTail (L.value L.loIndex) ≤
    Real.exp (-finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
      (L.value L.loIndex - L.mean0)) at htail
  rw [← L.rawLegendreRate_eq_centered (L.value L.loIndex)] at htail
  exact htail.trans (Real.exp_le_exp.mpr (neg_le_neg hrate))

end
end ExactHoeffding
