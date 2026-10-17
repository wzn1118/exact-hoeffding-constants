import ExactHoeffding.FiniteSupportOpenEnvelope
import ExactHoeffding.FiniteSupportLawCentering
import ExactHoeffding.FiniteSupportLawTails

/-!
# Variance-envelope integration for an actual finite law

These statements use the uncentered support coordinates, the actual finite
weighted tail events, and the ordinary mean. The envelope is required to be
continuous and positive only between the support endpoints.
-/

namespace ExactHoeffding
noncomputable section

open Set

/-- Upper-tail probability in the original support coordinates. -/
def FiniteSupportLawData.rawUpperTail {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (v : ℝ) : ℝ :=
  L.upperTail (v - L.mean0)

/-- Lower-tail probability in the original support coordinates. -/
def FiniteSupportLawData.rawLowerTail {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (v : ℝ) : ℝ :=
  L.lowerTail (v - L.mean0)

/-- The translated upper event is the actual finite weighted event `X ≥ v`. -/
theorem FiniteSupportLawData.rawUpperTail_eq_sum
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (v : ℝ) :
    L.rawUpperTail v =
      ∑ i ∈ L.support, if v ≤ L.value i then L.weight i else 0 := by
  unfold FiniteSupportLawData.rawUpperTail FiniteSupportLawData.upperTail
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact propext (by simp [FiniteSupportLawData.centeredValue])

/-- The translated lower event is the actual finite weighted event `X ≤ v`. -/
theorem FiniteSupportLawData.rawLowerTail_eq_sum
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (v : ℝ) :
    L.rawLowerTail v =
      ∑ i ∈ L.support, if L.value i ≤ v then L.weight i else 0 := by
  unfold FiniteSupportLawData.rawLowerTail FiniteSupportLawData.lowerTail
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact propext (by simp [FiniteSupportLawData.centeredValue])

private theorem centeredEnvelope_continuousOn
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex))) :
    ContinuousOn (fun u : ℝ => Q (u + L.mean0))
      (Ioo (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0)) := by
  apply hQ.comp (continuous_id.add continuous_const).continuousOn
  intro u hu
  change L.value L.loIndex < u + L.mean0 ∧ u + L.mean0 < L.value L.hiIndex
  constructor <;> linarith [hu.1, hu.2]

private theorem centeredEnvelope_pos
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u) :
    ∀ u ∈ Ioo (L.value L.loIndex - L.mean0)
      (L.value L.hiIndex - L.mean0), 0 < Q (u + L.mean0) := by
  intro u hu
  apply hQpos
  constructor <;> linarith [hu.1, hu.2]

/-- The uncentered right envelope integral is bounded by the true Legendre
rate of the actual finite weighted law. -/
theorem FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeRight
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvmu : L.mean0 ≤ v) (hvhi : v < L.value L.hiIndex) :
    (∫ u : ℝ in L.mean0..v, (v - u) / Q u) ≤ L.rawLegendreRate v := by
  rw [L.rawLegendreRate_eq_centered]
  have h := finiteSupportLegendreRate_ge_meanEnvelopeRateRight_open
    (L.toTiltCurve L.variance_pos) (fun u : ℝ => Q (u + L.mean0))
    (centeredEnvelope_continuousOn L Q hQ) (centeredEnvelope_pos L Q hQpos)
    hV (show 0 ≤ v - L.mean0 by linarith)
    (show v - L.mean0 < L.value L.hiIndex - L.mean0 by linarith)
  change (∫ u : ℝ in 0..(v - L.mean0),
    ((v - L.mean0) - u) / Q (u + L.mean0)) ≤ _ at h
  rw [L.meanEnvelopeIntegralRight_shift Q v] at h
  exact h

/-- The uncentered left envelope integral is bounded by the true Legendre
rate of the actual finite weighted law. -/
theorem FiniteSupportLawData.rawLegendreRate_ge_meanEnvelopeLeft
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvlo : L.value L.loIndex < v) (hvmu : v ≤ L.mean0) :
    (∫ u : ℝ in v..L.mean0, (u - v) / Q u) ≤ L.rawLegendreRate v := by
  rw [L.rawLegendreRate_eq_centered]
  have h := finiteSupportLegendreRate_ge_meanEnvelopeRateLeft_open
    (L.toTiltCurve L.variance_pos) (fun u : ℝ => Q (u + L.mean0))
    (centeredEnvelope_continuousOn L Q hQ) (centeredEnvelope_pos L Q hQpos)
    hV (show L.value L.loIndex - L.mean0 < v - L.mean0 by linarith)
    (show v - L.mean0 ≤ 0 by linarith)
  change (∫ u : ℝ in (v - L.mean0)..0,
    (u - (v - L.mean0)) / Q (u + L.mean0)) ≤ _ at h
  rw [L.meanEnvelopeIntegralLeft_shift Q v] at h
  exact h

/-- A strict variance gap at one internal tilt yields strict domination of
the uncentered right envelope integral. -/
theorem FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvmu : L.mean0 < v) (hvhi : v < L.value L.hiIndex)
    (hstrict : ∃ c ∈ Ioo (0 : ℝ)
      (finiteSupportMeanInverse (L.toTiltCurve L.variance_pos) (v - L.mean0)),
      L.variance c < Q (L.mean c + L.mean0)) :
    (∫ u : ℝ in L.mean0..v, (v - u) / Q u) < L.rawLegendreRate v := by
  rw [L.rawLegendreRate_eq_centered]
  have h := finiteSupportLegendreRate_gt_meanEnvelopeRateRight_of_strict_open
    (L.toTiltCurve L.variance_pos) (fun u : ℝ => Q (u + L.mean0))
    (centeredEnvelope_continuousOn L Q hQ) (centeredEnvelope_pos L Q hQpos)
    hV (show 0 < v - L.mean0 by linarith)
    (show v - L.mean0 < L.value L.hiIndex - L.mean0 by linarith) hstrict
  change (∫ u : ℝ in 0..(v - L.mean0),
    ((v - L.mean0) - u) / Q (u + L.mean0)) < _ at h
  rw [L.meanEnvelopeIntegralRight_shift Q v] at h
  exact h

/-- A strict variance gap at one internal tilt yields strict domination of
the uncentered left envelope integral. -/
theorem FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvlo : L.value L.loIndex < v) (hvmu : v < L.mean0)
    (hstrict : ∃ c ∈ Ioo
      (finiteSupportMeanInverse (L.toTiltCurve L.variance_pos) (v - L.mean0)) 0,
      L.variance c < Q (L.mean c + L.mean0)) :
    (∫ u : ℝ in v..L.mean0, (u - v) / Q u) < L.rawLegendreRate v := by
  rw [L.rawLegendreRate_eq_centered]
  have h := finiteSupportLegendreRate_gt_meanEnvelopeRateLeft_of_strict_open
    (L.toTiltCurve L.variance_pos) (fun u : ℝ => Q (u + L.mean0))
    (centeredEnvelope_continuousOn L Q hQ) (centeredEnvelope_pos L Q hQpos)
    hV (show L.value L.loIndex - L.mean0 < v - L.mean0 by linarith)
    (show v - L.mean0 < 0 by linarith) hstrict
  change (∫ u : ℝ in (v - L.mean0)..0,
    (u - (v - L.mean0)) / Q (u + L.mean0)) < _ at h
  rw [L.meanEnvelopeIntegralLeft_shift Q v] at h
  exact h

/-- Optimized Chernoff inequality for the actual raw upper event. -/
theorem FiniteSupportLawData.rawUpperTail_le_exp_neg_rate_interior
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hvmu : L.mean0 ≤ v) (hvhi : v < L.value L.hiIndex) :
    L.rawUpperTail v ≤ Real.exp (-L.rawLegendreRate v) := by
  rw [L.rawLegendreRate_eq_centered]
  exact L.upperTail_le_exp_neg_rate_interior
    (by linarith : 0 ≤ v - L.mean0)
    (by linarith : v - L.mean0 < L.value L.hiIndex - L.mean0)

/-- Optimized Chernoff inequality for the actual raw lower event. -/
theorem FiniteSupportLawData.rawLowerTail_le_exp_neg_rate_interior
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hvlo : L.value L.loIndex < v) (hvmu : v ≤ L.mean0) :
    L.rawLowerTail v ≤ Real.exp (-L.rawLegendreRate v) := by
  rw [L.rawLegendreRate_eq_centered]
  exact L.lowerTail_le_exp_neg_rate_interior
    (by linarith : L.value L.loIndex - L.mean0 < v - L.mean0)
    (by linarith : v - L.mean0 ≤ 0)

/-- Right-tail envelope bound for the actual finite weighted event. -/
theorem FiniteSupportLawData.rawUpperTail_le_exp_neg_meanEnvelope
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvmu : L.mean0 ≤ v) (hvhi : v < L.value L.hiIndex) :
    L.rawUpperTail v ≤ Real.exp (-(∫ u : ℝ in L.mean0..v, (v - u) / Q u)) := by
  exact (L.rawUpperTail_le_exp_neg_rate_interior hvmu hvhi).trans
    (Real.exp_le_exp.mpr (neg_le_neg
      (L.rawLegendreRate_ge_meanEnvelopeRight Q hQ hQpos hV hvmu hvhi)))

/-- Left-tail envelope bound for the actual finite weighted event. -/
theorem FiniteSupportLawData.rawLowerTail_le_exp_neg_meanEnvelope
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvlo : L.value L.loIndex < v) (hvmu : v ≤ L.mean0) :
    L.rawLowerTail v ≤ Real.exp (-(∫ u : ℝ in v..L.mean0, (u - v) / Q u)) := by
  exact (L.rawLowerTail_le_exp_neg_rate_interior hvlo hvmu).trans
    (Real.exp_le_exp.mpr (neg_le_neg
      (L.rawLegendreRate_ge_meanEnvelopeLeft Q hQ hQpos hV hvlo hvmu)))

/-- The right-tail envelope bound is strict if the variance is strictly
below the envelope at one internal tilt. -/
theorem FiniteSupportLawData.rawUpperTail_lt_exp_neg_meanEnvelope
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvmu : L.mean0 < v) (hvhi : v < L.value L.hiIndex)
    (hstrict : ∃ c ∈ Ioo (0 : ℝ)
      (finiteSupportMeanInverse (L.toTiltCurve L.variance_pos) (v - L.mean0)),
      L.variance c < Q (L.mean c + L.mean0)) :
    L.rawUpperTail v < Real.exp (-(∫ u : ℝ in L.mean0..v, (v - u) / Q u)) := by
  exact (L.rawUpperTail_le_exp_neg_rate_interior hvmu.le hvhi).trans_lt
    (Real.exp_lt_exp.mpr (neg_lt_neg
      (L.rawLegendreRate_gt_meanEnvelopeRight Q hQ hQpos hV hvmu hvhi hstrict)))

/-- The left-tail envelope bound is strict if the variance is strictly
below the envelope at one internal tilt. -/
theorem FiniteSupportLawData.rawLowerTail_lt_exp_neg_meanEnvelope
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvlo : L.value L.loIndex < v) (hvmu : v < L.mean0)
    (hstrict : ∃ c ∈ Ioo
      (finiteSupportMeanInverse (L.toTiltCurve L.variance_pos) (v - L.mean0)) 0,
      L.variance c < Q (L.mean c + L.mean0)) :
    L.rawLowerTail v < Real.exp (-(∫ u : ℝ in v..L.mean0, (u - v) / Q u)) := by
  exact (L.rawLowerTail_le_exp_neg_rate_interior hvlo hvmu.le).trans_lt
    (Real.exp_lt_exp.mpr (neg_lt_neg
      (L.rawLegendreRate_gt_meanEnvelopeLeft Q hQ hQpos hV hvlo hvmu hstrict)))

end
end ExactHoeffding
