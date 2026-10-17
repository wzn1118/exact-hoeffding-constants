import ExactHoeffding.FiniteSupportLawIntegration
import ExactHoeffding.FiniteSupportLawEndpointIntegration
import ExactHoeffding.FiniteSupportLawMeanGap
import ExactHoeffding.FiniteSupportLawRawEndpointStrict

/-!
# Typed contract for manuscript result A:integration

This declaration is a direct Lean transcription of the finite-support
variance-envelope theorem: interior rate comparisons, actual finite weighted
tails, interval strictness, and finite one-sided endpoint limits are grouped
under the manuscript's endpoint-atom assumptions. In particular, positive
variance is derived from those assumptions and is not a caller premise.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

def manuscriptA1RightVarianceGap
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (v : ℝ) : Prop :=
  ∃ a b : ℝ, L.mean0 ≤ a ∧ a < b ∧ b ≤ v ∧
    ∀ u ∈ Ioo a b,
      L.variance (finiteSupportMeanInverse
        (L.toTiltCurve L.variance_pos) (u - L.mean0)) < Q u

def manuscriptA1LeftVarianceGap
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (v : ℝ) : Prop :=
  ∃ a b : ℝ, v ≤ a ∧ a < b ∧ b ≤ L.mean0 ∧
    ∀ u ∈ Ioo a b,
      L.variance (finiteSupportMeanInverse
        (L.toTiltCurve L.variance_pos) (u - L.mean0)) < Q u

/-- The full typed statement contract for the frozen manuscript theorem
`A:integration`, expressed for an actual finite weighted law. -/
theorem manuscript_A_integration_contract
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0)) :
    (∀ v, L.mean0 ≤ v → v < L.value L.hiIndex →
      (∫ u : ℝ in L.mean0..v, (v-u)/Q u) ≤ L.rawLegendreRate v) ∧
    (∀ v, L.value L.loIndex < v → v ≤ L.mean0 →
      (∫ u : ℝ in v..L.mean0, (u-v)/Q u) ≤ L.rawLegendreRate v) ∧
    (∀ v, L.mean0 ≤ v → v < L.value L.hiIndex →
      L.rawUpperTail v ≤ Real.exp (-(∫ u : ℝ in L.mean0..v, (v-u)/Q u))) ∧
    (∀ v, L.value L.loIndex < v → v ≤ L.mean0 →
      L.rawLowerTail v ≤ Real.exp (-(∫ u : ℝ in v..L.mean0, (u-v)/Q u))) ∧
    (∀ v, L.rawUpperTail v =
      ∑ i ∈ L.support, if v ≤ L.value i then L.weight i else 0) ∧
    (∀ v, L.rawLowerTail v =
      ∑ i ∈ L.support, if L.value i ≤ v then L.weight i else 0) ∧
    (∀ v, L.mean0 < v → v < L.value L.hiIndex →
      manuscriptA1RightVarianceGap L Q v →
      (∫ u : ℝ in L.mean0..v, (v-u)/Q u) < L.rawLegendreRate v) ∧
    (∀ v, L.value L.loIndex < v → v < L.mean0 →
      manuscriptA1LeftVarianceGap L Q v →
      (∫ u : ℝ in v..L.mean0, (u-v)/Q u) < L.rawLegendreRate v) ∧
    (∀ Jlim,
      Tendsto (fun v : ℝ => ∫ u : ℝ in L.mean0..v, (v-u)/Q u)
        (𝓝[<] (L.value L.hiIndex)) (𝓝 Jlim) →
      Jlim ≤ L.rawLegendreRate (L.value L.hiIndex)) ∧
    (∀ Jlim,
      Tendsto (fun v : ℝ => ∫ u : ℝ in v..L.mean0, (u-v)/Q u)
        (𝓝[>] (L.value L.loIndex)) (𝓝 Jlim) →
      Jlim ≤ L.rawLegendreRate (L.value L.loIndex)) ∧
    (∀ Jlim,
      Tendsto (fun v : ℝ => ∫ u : ℝ in L.mean0..v, (v-u)/Q u)
        (𝓝[<] (L.value L.hiIndex)) (𝓝 Jlim) →
      L.rawUpperTail (L.value L.hiIndex) ≤ Real.exp (-Jlim)) ∧
    (∀ Jlim,
      Tendsto (fun v : ℝ => ∫ u : ℝ in v..L.mean0, (u-v)/Q u)
        (𝓝[>] (L.value L.loIndex)) (𝓝 Jlim) →
      L.rawLowerTail (L.value L.loIndex) ≤ Real.exp (-Jlim)) ∧
    (∀ Jlim,
      Tendsto (fun v : ℝ => ∫ u : ℝ in L.mean0..v, (v-u)/Q u)
        (𝓝[<] (L.value L.hiIndex)) (𝓝 Jlim) →
      manuscriptA1RightVarianceGap L Q (L.value L.hiIndex) →
      Jlim < L.rawLegendreRate (L.value L.hiIndex)) ∧
    (∀ Jlim,
      Tendsto (fun v : ℝ => ∫ u : ℝ in v..L.mean0, (u-v)/Q u)
        (𝓝[>] (L.value L.loIndex)) (𝓝 Jlim) →
      manuscriptA1LeftVarianceGap L Q (L.value L.loIndex) →
      Jlim < L.rawLegendreRate (L.value L.loIndex)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hvmu hvhi
    exact L.rawLegendreRate_ge_meanEnvelopeRight Q hQ hQpos hV hvmu hvhi
  · intro v hvlo hvmu
    exact L.rawLegendreRate_ge_meanEnvelopeLeft Q hQ hQpos hV hvlo hvmu
  · intro v hvmu hvhi
    exact L.rawUpperTail_le_exp_neg_meanEnvelope Q hQ hQpos hV hvmu hvhi
  · intro v hvlo hvmu
    exact L.rawLowerTail_le_exp_neg_meanEnvelope Q hQ hQpos hV hvlo hvmu
  · intro v
    exact L.rawUpperTail_eq_sum v
  · intro v
    exact L.rawLowerTail_eq_sum v
  · intro v hvmu hvhi hgap
    exact L.rawLegendreRate_gt_meanEnvelopeRight_of_interval
      Q hQ hQpos hV hvmu hvhi hgap
  · intro v hvlo hvmu hgap
    exact L.rawLegendreRate_gt_meanEnvelopeLeft_of_interval
      Q hQ hQpos hV hvlo hvmu hgap
  · intro Jlim hJ
    exact L.rawLegendreRate_ge_meanEnvelopeRight_endpoint
      Q hQ hQpos hV Jlim hJ
  · intro Jlim hJ
    exact L.rawLegendreRate_ge_meanEnvelopeLeft_endpoint
      Q hQ hQpos hV Jlim hJ
  · intro Jlim hJ
    exact L.rawUpperTail_le_meanEnvelope_endpoint
      Q hQ hQpos hV Jlim hJ
  · intro Jlim hJ
    exact L.rawLowerTail_le_meanEnvelope_endpoint
      Q hQ hQpos hV Jlim hJ
  · intro Jlim hJ hgap
    exact L.rawLegendreRate_gt_meanEnvelopeRight_endpoint_of_interval
      Q hQ hQpos hV hgap Jlim hJ
  · intro Jlim hJ hgap
    exact L.rawLegendreRate_gt_meanEnvelopeLeft_endpoint_of_interval
      Q hQ hQpos hV hgap Jlim hJ

end
end ExactHoeffding
