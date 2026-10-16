import ExactHoeffding.FiniteSupportMeanEnvelopeStrict

/-!
# Endpoint continuation for the finite-support mean-envelope comparison

The interior comparison is combined with the one-sided endpoint limits that
are finite for a finite support exponential sum.  The limit hypotheses are
explicit so that endpoint identities are never hidden in a continuity claim.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- Right endpoint continuation of the variance-envelope comparison. -/
theorem finiteSupportLegendreRate_ge_meanEnvelopeRateRight_endpoint
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Set.Icc D.lo D.hi, 0 < Q u)
    (hV : ∀ t : ℝ, D.variance t ≤ Q (D.mean t))
    (hRate : Tendsto (fun v : ℝ => finiteSupportLegendreRate D v)
      (𝓝[<] D.hi) (𝓝 (finiteSupportLegendreRate D D.hi)))
    (hJ : Tendsto (fun v : ℝ => finiteSupportMeanEnvelopeRateRight D Q v)
      (𝓝[<] D.hi)
        (𝓝 (finiteSupportMeanEnvelopeRateRight D Q D.hi))) :
    finiteSupportMeanEnvelopeRateRight D Q D.hi ≤
      finiteSupportLegendreRate D D.hi := by
  have hinner : ∀ᶠ v in 𝓝[<] D.hi,
      finiteSupportMeanEnvelopeRateRight D Q v ≤
        finiteSupportLegendreRate D v := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Ioi_mem_nhds D.hmuhi] with v hv
    intro hlt
    exact finiteSupportLegendreRate_ge_meanEnvelopeRateRight D Q hQ hQpos hV
      hv.le hlt
  have hdiff : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateRight D Q v -
        finiteSupportLegendreRate D v) (𝓝[<] D.hi)
      (𝓝 (finiteSupportMeanEnvelopeRateRight D Q D.hi -
        finiteSupportLegendreRate D D.hi)) := by
    exact hJ.sub hRate
  have hnonpos : ∀ᶠ v in 𝓝[<] D.hi,
      finiteSupportMeanEnvelopeRateRight D Q v -
        finiteSupportLegendreRate D v ≤ 0 := hinner.mono (fun v hv => sub_nonpos.mpr hv)
  have hlim := le_of_tendsto hdiff hnonpos
  linarith

/-- Left endpoint continuation of the variance-envelope comparison. -/
theorem finiteSupportLegendreRate_ge_meanEnvelopeRateLeft_endpoint
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Set.Icc D.lo D.hi, 0 < Q u)
    (hV : ∀ t : ℝ, D.variance t ≤ Q (D.mean t))
    (hRate : Tendsto (fun v : ℝ => finiteSupportLegendreRate D v)
      (𝓝[>] D.lo) (𝓝 (finiteSupportLegendreRate D D.lo)))
    (hJ : Tendsto (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft D Q v)
      (𝓝[>] D.lo)
        (𝓝 (finiteSupportMeanEnvelopeRateLeft D Q D.lo))) :
    finiteSupportMeanEnvelopeRateLeft D Q D.lo ≤
      finiteSupportLegendreRate D D.lo := by
  have hinner : ∀ᶠ v in 𝓝[>] D.lo,
      finiteSupportMeanEnvelopeRateLeft D Q v ≤
        finiteSupportLegendreRate D v := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Iio_mem_nhds D.hlomu] with v hv
    intro hgt
    exact finiteSupportLegendreRate_ge_meanEnvelopeRateLeft D Q hQ hQpos hV
      hgt hv.le
  have hdiff : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft D Q v -
        finiteSupportLegendreRate D v) (𝓝[>] D.lo)
      (𝓝 (finiteSupportMeanEnvelopeRateLeft D Q D.lo -
        finiteSupportLegendreRate D D.lo)) := by
    exact hJ.sub hRate
  have hnonpos : ∀ᶠ v in 𝓝[>] D.lo,
      finiteSupportMeanEnvelopeRateLeft D Q v -
        finiteSupportLegendreRate D v ≤ 0 := hinner.mono (fun v hv => sub_nonpos.mpr hv)
  have hlim := le_of_tendsto hdiff hnonpos
  linarith

end
end ExactHoeffding
