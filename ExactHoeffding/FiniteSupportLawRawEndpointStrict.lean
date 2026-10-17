import ExactHoeffding.FiniteSupportLawEndpointStrict
import ExactHoeffding.FiniteSupportLawIntegration

/-! # Strict finite-limit endpoints in the original support coordinates

A strict variance-envelope gap at one tilt on the relevant side of zero
persists to the support endpoint. The assumptions concern the open support
and the finite one-sided limit of the displayed integral.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

private theorem translatedEnvelope_continuousOn
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex))) :
    ContinuousOn (fun u : ℝ => Q (u + L.mean0))
      (Ioo (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0)) := by
  apply hQ.comp (continuous_id.add continuous_const).continuousOn
  intro u hu
  change L.value L.loIndex < u + L.mean0 ∧ u + L.mean0 < L.value L.hiIndex
  constructor <;> linarith [hu.1, hu.2]

private theorem translatedEnvelope_pos
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u) :
    ∀ u ∈ Ioo (L.value L.loIndex - L.mean0)
      (L.value L.hiIndex - L.mean0), 0 < Q (u + L.mean0) := by
  intro u hu
  apply hQpos
  constructor <;> linarith [hu.1, hu.2]

/-- Strict upper-endpoint rate comparison in the original coordinates. -/
theorem FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight_endpoint
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (hstrict : ∃ c : ℝ, 0 < c ∧ L.variance c < Q (L.mean c + L.mean0))
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in L.mean0..v, (v-u)/Q u)
      (𝓝[<] (L.value L.hiIndex)) (𝓝 Jlim)) :
    Jlim < L.rawLegendreRate (L.value L.hiIndex) := by
  have hshift : Tendsto (fun u : ℝ => u + L.mean0)
      (𝓝[<] (L.value L.hiIndex - L.mean0))
      (𝓝[<] (L.value L.hiIndex)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : Continuous (fun u : ℝ => u + L.mean0) :=
        continuous_id.add continuous_const
      have h : Tendsto (fun u : ℝ => u + L.mean0)
          (𝓝[<] (L.value L.hiIndex - L.mean0))
          (𝓝 (L.value L.hiIndex - L.mean0 + L.mean0)) :=
        (hcont.tendsto _).mono_left nhdsWithin_le_nhds
      simpa only [sub_add_cancel] using h
    · apply eventually_nhdsWithin_of_forall
      intro u hu
      change u + L.mean0 < L.value L.hiIndex
      change u < L.value L.hiIndex - L.mean0 at hu
      linarith
  have hJc : Tendsto (fun v : ℝ => finiteSupportMeanEnvelopeRateRight
      (L.toTiltCurve L.variance_pos) (fun u : ℝ => Q (u + L.mean0)) v)
      (𝓝[<] (L.value L.hiIndex - L.mean0)) (𝓝 Jlim) := by
    have hfun : (fun v : ℝ => finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) (fun u : ℝ => Q (u + L.mean0)) v) =
        (fun v : ℝ => ∫ u : ℝ in L.mean0..(v + L.mean0),
          (v + L.mean0 - u) / Q u) := by
      funext v
      have h := L.meanEnvelopeIntegralRight_shift Q (v + L.mean0)
      change (∫ u : ℝ in 0..v, (v - u) / Q (u + L.mean0)) = _
      simpa only [add_sub_cancel_right] using h
    rw [hfun]
    exact hJ.comp hshift
  rw [L.rawLegendreRate_eq_centered]
  exact finiteSupportLawData_rate_gt_meanEnvelopeRateRight_endpoint_of_limit_open
    L (fun u : ℝ => Q (u + L.mean0))
    (translatedEnvelope_continuousOn L Q hQ) (translatedEnvelope_pos L Q hQpos)
    hV hstrict Jlim hJc

/-- Strict lower-endpoint rate comparison in the original coordinates. -/
theorem FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft_endpoint
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (hstrict : ∃ c : ℝ, c < 0 ∧ L.variance c < Q (L.mean c + L.mean0))
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in v..L.mean0, (u-v)/Q u)
      (𝓝[>] (L.value L.loIndex)) (𝓝 Jlim)) :
    Jlim < L.rawLegendreRate (L.value L.loIndex) := by
  have hshift : Tendsto (fun u : ℝ => u + L.mean0)
      (𝓝[>] (L.value L.loIndex - L.mean0))
      (𝓝[>] (L.value L.loIndex)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : Continuous (fun u : ℝ => u + L.mean0) :=
        continuous_id.add continuous_const
      have h : Tendsto (fun u : ℝ => u + L.mean0)
          (𝓝[>] (L.value L.loIndex - L.mean0))
          (𝓝 (L.value L.loIndex - L.mean0 + L.mean0)) :=
        (hcont.tendsto _).mono_left nhdsWithin_le_nhds
      simpa only [sub_add_cancel] using h
    · apply eventually_nhdsWithin_of_forall
      intro u hu
      change L.value L.loIndex < u + L.mean0
      change L.value L.loIndex - L.mean0 < u at hu
      linarith
  have hJc : Tendsto (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft
      (L.toTiltCurve L.variance_pos) (fun u : ℝ => Q (u + L.mean0)) v)
      (𝓝[>] (L.value L.loIndex - L.mean0)) (𝓝 Jlim) := by
    have hfun : (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) (fun u : ℝ => Q (u + L.mean0)) v) =
        (fun v : ℝ => ∫ u : ℝ in (v + L.mean0)..L.mean0,
          (u - (v + L.mean0)) / Q u) := by
      funext v
      have h := L.meanEnvelopeIntegralLeft_shift Q (v + L.mean0)
      change (∫ u : ℝ in v..0, (u - v) / Q (u + L.mean0)) = _
      simpa only [add_sub_cancel_right] using h
    rw [hfun]
    exact hJ.comp hshift
  rw [L.rawLegendreRate_eq_centered]
  exact finiteSupportLawData_rate_gt_meanEnvelopeRateLeft_endpoint_of_limit_open
    L (fun u : ℝ => Q (u + L.mean0))
    (translatedEnvelope_continuousOn L Q hQ) (translatedEnvelope_pos L Q hQpos)
    hV hstrict Jlim hJc

/-- Strict bound for the actual upper-tail probability at its support endpoint. -/
theorem FiniteSupportLawData.rawUpperTail_lt_meanEnvelope_endpoint
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (hstrict : ∃ c : ℝ, 0 < c ∧ L.variance c < Q (L.mean c + L.mean0))
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in L.mean0..v, (v-u)/Q u)
      (𝓝[<] (L.value L.hiIndex)) (𝓝 Jlim)) :
    L.rawUpperTail (L.value L.hiIndex) < Real.exp (-Jlim) := by
  have hrate := L.rawLegendreRate_gt_meanEnvelopeRight_endpoint Q hQ hQpos hV
    hstrict Jlim hJ
  have htail := L.upperTail_le_exp_neg_rate_endpoint
  change L.rawUpperTail (L.value L.hiIndex) ≤
    Real.exp (-finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
      (L.value L.hiIndex - L.mean0)) at htail
  rw [← L.rawLegendreRate_eq_centered (L.value L.hiIndex)] at htail
  exact htail.trans_lt (Real.exp_lt_exp.mpr (neg_lt_neg hrate))

/-- Strict bound for the actual lower-tail probability at its support endpoint. -/
theorem FiniteSupportLawData.rawLowerTail_lt_meanEnvelope_endpoint
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (hstrict : ∃ c : ℝ, c < 0 ∧ L.variance c < Q (L.mean c + L.mean0))
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in v..L.mean0, (u-v)/Q u)
      (𝓝[>] (L.value L.loIndex)) (𝓝 Jlim)) :
    L.rawLowerTail (L.value L.loIndex) < Real.exp (-Jlim) := by
  have hrate := L.rawLegendreRate_gt_meanEnvelopeLeft_endpoint Q hQ hQpos hV
    hstrict Jlim hJ
  have htail := L.lowerTail_le_exp_neg_rate_endpoint
  change L.rawLowerTail (L.value L.loIndex) ≤
    Real.exp (-finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
      (L.value L.loIndex - L.mean0)) at htail
  rw [← L.rawLegendreRate_eq_centered (L.value L.loIndex)] at htail
  exact htail.trans_lt (Real.exp_lt_exp.mpr (neg_lt_neg hrate))

/-- A positive-length strict mean interval yields a positive strict tilt. -/
private theorem rawEndpoint_positive_tilt_of_interval
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (Q : ℝ → ℝ)
    (hgap : ∃ a b : ℝ, L.mean0 ≤ a ∧ a < b ∧ b ≤ L.value L.hiIndex ∧
      ∀ u ∈ Ioo a b, L.variance (finiteSupportMeanInverse
        (L.toTiltCurve L.variance_pos) (u - L.mean0)) < Q u) :
    ∃ c : ℝ, 0 < c ∧ L.variance c < Q (L.mean c + L.mean0) := by
  let D := L.toTiltCurve L.variance_pos
  have hmono : StrictMono D.mean :=
    strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
  obtain ⟨a, b, hμa, hab, hbhi, hstrict⟩ := hgap
  let u : ℝ := (a + b) / 2
  have hμu : L.mean0 < u := by dsimp [u]; linarith
  have huhi : u < L.value L.hiIndex := by dsimp [u]; linarith
  have hulo : D.lo < u - L.mean0 := by
    have h := D.hlomu
    change L.value L.loIndex - L.mean0 < 0 at h
    change L.value L.loIndex - L.mean0 < u - L.mean0
    linarith
  have huhi' : u - L.mean0 < D.hi := by
    change u - L.mean0 < L.value L.hiIndex - L.mean0
    linarith
  let c := finiteSupportMeanInverse D (u - L.mean0)
  have hcspec : D.mean c = u - L.mean0 :=
    finiteSupportMeanInverse_spec D hulo huhi'
  have hcpos : 0 < c := hmono.lt_iff_lt.mp (by
    rw [D.mean_zero, hcspec]
    change (0 : ℝ) < u - L.mean0
    linarith)
  refine ⟨c, hcpos, ?_⟩
  change L.variance c < Q (D.mean c + L.mean0)
  rw [hcspec, sub_add_cancel]
  apply hstrict u
  constructor <;> dsimp [u] <;> linarith

/-- A lower strict mean interval yields a negative strict tilt. -/
private theorem rawEndpoint_negative_tilt_of_interval
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (Q : ℝ → ℝ)
    (hgap : ∃ a b : ℝ, L.value L.loIndex ≤ a ∧ a < b ∧ b ≤ L.mean0 ∧
      ∀ u ∈ Ioo a b, L.variance (finiteSupportMeanInverse
        (L.toTiltCurve L.variance_pos) (u - L.mean0)) < Q u) :
    ∃ c : ℝ, c < 0 ∧ L.variance c < Q (L.mean c + L.mean0) := by
  let D := L.toTiltCurve L.variance_pos
  have hmono : StrictMono D.mean :=
    strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
  obtain ⟨a, b, hloa, hab, hbμ, hstrict⟩ := hgap
  let u : ℝ := (a + b) / 2
  have hlou : L.value L.loIndex < u := by dsimp [u]; linarith
  have huμ : u < L.mean0 := by dsimp [u]; linarith
  have hulo : D.lo < u - L.mean0 := by
    change L.value L.loIndex - L.mean0 < u - L.mean0
    linarith
  have huhi : u - L.mean0 < D.hi := by
    have h := D.hmuhi
    change 0 < L.value L.hiIndex - L.mean0 at h
    change u - L.mean0 < L.value L.hiIndex - L.mean0
    linarith
  let c := finiteSupportMeanInverse D (u - L.mean0)
  have hcspec : D.mean c = u - L.mean0 :=
    finiteSupportMeanInverse_spec D hulo huhi
  have hcneg : c < 0 := hmono.lt_iff_lt.mp (by
    rw [hcspec, D.mean_zero]
    change u - L.mean0 < (0 : ℝ)
    linarith)
  refine ⟨c, hcneg, ?_⟩
  change L.variance c < Q (D.mean c + L.mean0)
  rw [hcspec, sub_add_cancel]
  apply hstrict u
  constructor <;> dsimp [u] <;> linarith

/-- The manuscript's strict mean-interval condition at the upper endpoint. -/
theorem FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight_endpoint_of_interval
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (hgap : ∃ a b : ℝ, L.mean0 ≤ a ∧ a < b ∧ b ≤ L.value L.hiIndex ∧
      ∀ u ∈ Ioo a b, L.variance (finiteSupportMeanInverse
        (L.toTiltCurve L.variance_pos) (u - L.mean0)) < Q u)
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in L.mean0..v, (v-u)/Q u)
      (𝓝[<] (L.value L.hiIndex)) (𝓝 Jlim)) :
    Jlim < L.rawLegendreRate (L.value L.hiIndex) := by
  exact L.rawLegendreRate_gt_meanEnvelopeRight_endpoint Q hQ hQpos hV
    (rawEndpoint_positive_tilt_of_interval L Q hgap) Jlim hJ

/-- The manuscript's strict mean-interval condition at the lower endpoint. -/
theorem FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft_endpoint_of_interval
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (hgap : ∃ a b : ℝ, L.value L.loIndex ≤ a ∧ a < b ∧ b ≤ L.mean0 ∧
      ∀ u ∈ Ioo a b, L.variance (finiteSupportMeanInverse
        (L.toTiltCurve L.variance_pos) (u - L.mean0)) < Q u)
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in v..L.mean0, (u-v)/Q u)
      (𝓝[>] (L.value L.loIndex)) (𝓝 Jlim)) :
    Jlim < L.rawLegendreRate (L.value L.loIndex) := by
  exact L.rawLegendreRate_gt_meanEnvelopeLeft_endpoint Q hQ hQpos hV
    (rawEndpoint_negative_tilt_of_interval L Q hgap) Jlim hJ

/-- Actual upper-endpoint tail under a positive-length strict mean interval. -/
theorem FiniteSupportLawData.rawUpperTail_lt_meanEnvelope_endpoint_of_interval
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (hgap : ∃ a b : ℝ, L.mean0 ≤ a ∧ a < b ∧ b ≤ L.value L.hiIndex ∧
      ∀ u ∈ Ioo a b, L.variance (finiteSupportMeanInverse
        (L.toTiltCurve L.variance_pos) (u - L.mean0)) < Q u)
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in L.mean0..v, (v-u)/Q u)
      (𝓝[<] (L.value L.hiIndex)) (𝓝 Jlim)) :
    L.rawUpperTail (L.value L.hiIndex) < Real.exp (-Jlim) := by
  exact L.rawUpperTail_lt_meanEnvelope_endpoint Q hQ hQpos hV
    (rawEndpoint_positive_tilt_of_interval L Q hgap) Jlim hJ

/-- Actual lower-endpoint tail under a positive-length strict mean interval. -/
theorem FiniteSupportLawData.rawLowerTail_lt_meanEnvelope_endpoint_of_interval
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    (hgap : ∃ a b : ℝ, L.value L.loIndex ≤ a ∧ a < b ∧ b ≤ L.mean0 ∧
      ∀ u ∈ Ioo a b, L.variance (finiteSupportMeanInverse
        (L.toTiltCurve L.variance_pos) (u - L.mean0)) < Q u)
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => ∫ u : ℝ in v..L.mean0, (u-v)/Q u)
      (𝓝[>] (L.value L.loIndex)) (𝓝 Jlim)) :
    L.rawLowerTail (L.value L.loIndex) < Real.exp (-Jlim) := by
  exact L.rawLowerTail_lt_meanEnvelope_endpoint Q hQ hQpos hV
    (rawEndpoint_negative_tilt_of_interval L Q hgap) Jlim hJ

end
end ExactHoeffding
