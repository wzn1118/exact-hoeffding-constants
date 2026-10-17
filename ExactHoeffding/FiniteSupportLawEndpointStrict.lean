import ExactHoeffding.FiniteSupportEndpointStrict

/-! # Strict endpoint envelope bounds for actual finite laws

The strictness witness is an actual positive or negative tilt at which the
variance is smaller than the open-support envelope. A fixed positive gap is
retained at all farther targets before taking the finite integral limit.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- Strict right-endpoint comparison under the manuscript's open-support
hypotheses and the finite one-sided limit of the displayed integral. -/
theorem finiteSupportLawData_rate_gt_meanEnvelopeRateRight_endpoint_of_limit_open
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex - L.mean0)
      (L.value L.hiIndex - L.mean0)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex - L.mean0)
      (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    (hstrict : ∃ c : ℝ, 0 < c ∧ L.variance c < Q (L.mean c))
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => finiteSupportMeanEnvelopeRateRight
      (L.toTiltCurve L.variance_pos) Q v)
      (𝓝[<] (L.value L.hiIndex - L.mean0)) (𝓝 Jlim)) :
    Jlim < finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
      (L.value L.hiIndex - L.mean0) := by
  let D := L.toTiltCurve L.variance_pos
  obtain ⟨c, hc, hgap⟩ := hstrict
  let v₀ := D.mean (c + 1)
  have hmono : StrictMono D.mean := strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
  have hμv₀ : D.mu < v₀ := by
    have hm := hmono (show (0 : ℝ) < c + 1 by linarith)
    simpa [D.mean_zero, v₀] using hm
  have hv₀lo : D.lo < v₀ := (D.mean_range (c + 1)).1
  have hv₀hi : v₀ < D.hi := (D.mean_range (c + 1)).2
  have hinv : finiteSupportMeanInverse D v₀ = c + 1 :=
    ((finiteSupportMeanInverse_unique D hv₀lo hv₀hi).mp rfl).symm
  have hstrict₀ : finiteSupportMeanEnvelopeRateRight D Q v₀ <
      finiteSupportLegendreRate D v₀ := by
    apply finiteSupportLegendreRate_gt_meanEnvelopeRateRight_of_strict_open
      D Q hQ hQpos hV hμv₀ hv₀hi
    refine ⟨c, ?_, hgap⟩
    rw [hinv]
    exact ⟨hc, by linarith⟩
  let δ := finiteSupportLegendreRate D v₀ - finiteSupportMeanEnvelopeRateRight D Q v₀
  have hδ : 0 < δ := sub_pos.mpr hstrict₀
  have hinner : ∀ᶠ v in 𝓝[<] D.hi,
      finiteSupportMeanEnvelopeRateRight D Q v ≤ finiteSupportLegendreRate D D.hi - δ := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Ioi_mem_nhds hv₀hi] with v hv
    intro hvhi
    change v₀ < v at hv
    change v < D.hi at hvhi
    have hmon := finiteSupportLegendreRate_sub_meanEnvelopeRateRight_mono_open
      D Q hQ hQpos hV hμv₀ hv.le hvhi
    have hv0 : 0 ≤ v := by
      have hmu0 : D.mu = 0 := rfl
      linarith
    have hend := finiteSupportLawData_legendreRate_le_hi L hv0 hvhi
    change finiteSupportLegendreRate D v ≤ finiteSupportLegendreRate D D.hi at hend
    change δ ≤ finiteSupportLegendreRate D v -
      finiteSupportMeanEnvelopeRateRight D Q v at hmon
    linarith
  have hlim : Jlim ≤ finiteSupportLegendreRate D D.hi - δ := le_of_tendsto hJ hinner
  change Jlim < finiteSupportLegendreRate D D.hi
  linarith

/-- Strict left-endpoint comparison under the manuscript's open-support
hypotheses and the finite one-sided limit of the displayed integral. -/
theorem finiteSupportLawData_rate_gt_meanEnvelopeRateLeft_endpoint_of_limit_open
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex - L.mean0)
      (L.value L.hiIndex - L.mean0)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex - L.mean0)
      (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    (hstrict : ∃ c : ℝ, c < 0 ∧ L.variance c < Q (L.mean c))
    (Jlim : ℝ)
    (hJ : Tendsto (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft
      (L.toTiltCurve L.variance_pos) Q v)
      (𝓝[>] (L.value L.loIndex - L.mean0)) (𝓝 Jlim)) :
    Jlim < finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
      (L.value L.loIndex - L.mean0) := by
  let D := L.toTiltCurve L.variance_pos
  obtain ⟨c, hc, hgap⟩ := hstrict
  let v₀ := D.mean (c - 1)
  have hmono : StrictMono D.mean := strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
  have hv₀μ : v₀ < D.mu := by
    have hm := hmono (show c - 1 < (0 : ℝ) by linarith)
    simpa [D.mean_zero, v₀] using hm
  have hv₀lo : D.lo < v₀ := (D.mean_range (c - 1)).1
  have hv₀hi : v₀ < D.hi := (D.mean_range (c - 1)).2
  have hinv : finiteSupportMeanInverse D v₀ = c - 1 :=
    ((finiteSupportMeanInverse_unique D hv₀lo hv₀hi).mp rfl).symm
  have hstrict₀ : finiteSupportMeanEnvelopeRateLeft D Q v₀ <
      finiteSupportLegendreRate D v₀ := by
    apply finiteSupportLegendreRate_gt_meanEnvelopeRateLeft_of_strict_open
      D Q hQ hQpos hV hv₀lo hv₀μ
    refine ⟨c, ?_, hgap⟩
    rw [hinv]
    exact ⟨by linarith, hc⟩
  let δ := finiteSupportLegendreRate D v₀ - finiteSupportMeanEnvelopeRateLeft D Q v₀
  have hδ : 0 < δ := sub_pos.mpr hstrict₀
  have hinner : ∀ᶠ v in 𝓝[>] D.lo,
      finiteSupportMeanEnvelopeRateLeft D Q v ≤ finiteSupportLegendreRate D D.lo - δ := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Iio_mem_nhds hv₀lo] with v hv
    intro hvlo
    change v < v₀ at hv
    change D.lo < v at hvlo
    have hmon := finiteSupportLegendreRate_sub_meanEnvelopeRateLeft_mono_open
      D Q hQ hQpos hV hvlo hv.le hv₀μ
    have hv0 : v ≤ 0 := by
      have hmu0 : D.mu = 0 := rfl
      linarith
    have hend := finiteSupportLawData_legendreRate_le_lo L hvlo hv0
    change finiteSupportLegendreRate D v ≤ finiteSupportLegendreRate D D.lo at hend
    change δ ≤ finiteSupportLegendreRate D v -
      finiteSupportMeanEnvelopeRateLeft D Q v at hmon
    linarith
  have hlim : Jlim ≤ finiteSupportLegendreRate D D.lo - δ := le_of_tendsto hJ hinner
  change Jlim < finiteSupportLegendreRate D D.lo
  linarith

end
end ExactHoeffding
