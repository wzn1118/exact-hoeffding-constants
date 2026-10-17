import ExactHoeffding.FiniteSupportMeanEnvelopeStrict
import ExactHoeffding.FiniteSupportEndpointEnvelope
import ExactHoeffding.FiniteSupportTiltCurveOfLaw
import ExactHoeffding.FiniteSupportLawVariance

/-! # Direct finite-law interfaces for the mean-coordinate envelope theorem

The abstract change-of-variables proof is instantiated here at an actual
finite weighted probability law. Positive mass at two distinct endpoint atoms
proves strict positivity of every tilted variance; endpoint statements retain
the explicit one-sided limit hypotheses from the manuscript. -/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- Direct right-interior comparison for an actual finite weighted law. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateRight
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc (L.value L.loIndex - L.mean0)
        (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    {v : ℝ} (hv0 : 0 ≤ v) (hvhi : v < L.value L.hiIndex - L.mean0) :
    finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q v ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v := by
  exact finiteSupportLegendreRate_ge_meanEnvelopeRateRight
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hv0 hvhi

/-- Direct left-interior comparison for an actual finite weighted law. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateLeft
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc (L.value L.loIndex - L.mean0)
        (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    {v : ℝ} (hvlo : L.value L.loIndex - L.mean0 < v) (hv0 : v ≤ 0) :
    finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q v ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v := by
  exact finiteSupportLegendreRate_ge_meanEnvelopeRateLeft
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hvlo hv0

/-- Direct strict right comparison for an actual finite weighted law. -/
theorem finiteSupportLawData_rate_gt_meanEnvelopeRateRight
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc (L.value L.loIndex - L.mean0)
        (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    {v : ℝ} (hv0 : 0 < v) (hvhi : v < L.value L.hiIndex - L.mean0)
    (hstrict : ∃ c ∈ Ioo (0 : ℝ)
        (finiteSupportMeanInverse (L.toTiltCurve L.variance_pos) v),
      L.variance c < Q (L.mean c)) :
    finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q v <
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v := by
  exact finiteSupportLegendreRate_gt_meanEnvelopeRateRight_of_strict
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hv0 hvhi hstrict

/-- Direct strict left comparison for an actual finite weighted law. -/
theorem finiteSupportLawData_rate_gt_meanEnvelopeRateLeft
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc (L.value L.loIndex - L.mean0)
        (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    {v : ℝ} (hvlo : L.value L.loIndex - L.mean0 < v) (hv0 : v < 0)
    (hstrict : ∃ c ∈ Ioo (finiteSupportMeanInverse (L.toTiltCurve L.variance_pos) v) 0,
      L.variance c < Q (L.mean c)) :
    finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q v <
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v := by
  exact finiteSupportLegendreRate_gt_meanEnvelopeRateLeft_of_strict
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hvlo hv0 hstrict

/-- Right-endpoint continuation for a finite law, with the one-sided limits
required by the manuscript stated explicitly. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateRight_endpoint
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc
      (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    (hRate : Tendsto
      (fun v : ℝ => finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v)
      (𝓝[<] (L.value L.hiIndex - L.mean0))
      (𝓝 (finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.hiIndex - L.mean0))))
    (hJ : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) Q v)
      (𝓝[<] (L.value L.hiIndex - L.mean0))
      (𝓝 (finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) Q
        (L.value L.hiIndex - L.mean0)))) :
    finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q
        (L.value L.hiIndex - L.mean0) ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.hiIndex - L.mean0) := by
  exact finiteSupportLegendreRate_ge_meanEnvelopeRateRight_endpoint
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hRate hJ

/-- Left-endpoint continuation for a finite law, with the one-sided limits
required by the manuscript stated explicitly. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateLeft_endpoint
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc
      (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    (hRate : Tendsto
      (fun v : ℝ => finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v)
      (𝓝[>] (L.value L.loIndex - L.mean0))
      (𝓝 (finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.loIndex - L.mean0))))
    (hJ : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) Q v)
      (𝓝[>] (L.value L.loIndex - L.mean0))
      (𝓝 (finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) Q
        (L.value L.loIndex - L.mean0)))) :
    finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q
        (L.value L.loIndex - L.mean0) ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.loIndex - L.mean0) := by
  exact finiteSupportLegendreRate_ge_meanEnvelopeRateLeft_endpoint
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hRate hJ

end
end ExactHoeffding
