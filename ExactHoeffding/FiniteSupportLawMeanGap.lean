import ExactHoeffding.FiniteSupportLawIntegration
import ExactHoeffding.FiniteSupportLawEndpointRates

/-! # Strict envelope comparison in the original mean coordinates

A strict gap on a positive-length mean interval supplies the interior tilt
witness required by the integration theorem. Endpoint rates are identified
with their actual endpoint atom costs.
-/

namespace ExactHoeffding
noncomputable section
open Set

/-- A strict gap at one mean between the ordinary mean and an upper target
implies strict comparison of the actual Legendre rate. -/
theorem FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight_of_mean_gap
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvmu : L.mean0 < v) (hvhi : v < L.value L.hiIndex)
    (hgap : ∃ u ∈ Ioo L.mean0 v,
      L.variance (finiteSupportMeanInverse (L.toTiltCurve L.variance_pos)
        (u - L.mean0)) < Q u) :
    (∫ u : ℝ in L.mean0..v, (v-u)/Q u) < L.rawLegendreRate v := by
  let D := L.toTiltCurve L.variance_pos
  have hmono : StrictMono D.mean :=
    strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
  obtain ⟨u, hu, hgu⟩ := hgap
  have hulo : D.lo < u - L.mean0 := by
    have h := D.hlomu
    change L.value L.loIndex - L.mean0 < 0 at h
    change L.value L.loIndex - L.mean0 < u - L.mean0
    linarith [hu.1]
  have huhi : u - L.mean0 < D.hi := by
    change u - L.mean0 < L.value L.hiIndex - L.mean0
    linarith [hu.2]
  have hvlo : D.lo < v - L.mean0 := by
    change L.value L.loIndex - L.mean0 < v - L.mean0
    have h := D.hlomu
    change L.value L.loIndex - L.mean0 < 0 at h
    linarith
  have hvhi' : v - L.mean0 < D.hi := by
    change v - L.mean0 < L.value L.hiIndex - L.mean0
    linarith
  let c := finiteSupportMeanInverse D (u - L.mean0)
  have hcspec : D.mean c = u - L.mean0 :=
    finiteSupportMeanInverse_spec D hulo huhi
  have hvspec := finiteSupportMeanInverse_spec D hvlo hvhi'
  have hcpos : 0 < c := hmono.lt_iff_lt.mp (by
    rw [D.mean_zero, hcspec]
    change (0 : ℝ) < u - L.mean0
    linarith [hu.1])
  have hcv : c < finiteSupportMeanInverse D (v - L.mean0) :=
    hmono.lt_iff_lt.mp (by rw [hcspec, hvspec]; linarith [hu.2])
  apply L.rawLegendreRate_gt_meanEnvelopeRight Q hQ hQpos hV hvmu hvhi
  refine ⟨c, ⟨hcpos, hcv⟩, ?_⟩
  change L.variance c < Q (D.mean c + L.mean0)
  rw [hcspec, sub_add_cancel]
  exact hgu

/-- The corresponding strict comparison for a lower target. -/
theorem FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft_of_mean_gap
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvlo : L.value L.loIndex < v) (hvmu : v < L.mean0)
    (hgap : ∃ u ∈ Ioo v L.mean0,
      L.variance (finiteSupportMeanInverse (L.toTiltCurve L.variance_pos)
        (u - L.mean0)) < Q u) :
    (∫ u : ℝ in v..L.mean0, (u-v)/Q u) < L.rawLegendreRate v := by
  let D := L.toTiltCurve L.variance_pos
  have hmono : StrictMono D.mean :=
    strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
  obtain ⟨u, hu, hgu⟩ := hgap
  have hulo : D.lo < u - L.mean0 := by
    change L.value L.loIndex - L.mean0 < u - L.mean0
    linarith [hu.1]
  have huhi : u - L.mean0 < D.hi := by
    have h := D.hmuhi
    change 0 < L.value L.hiIndex - L.mean0 at h
    change u - L.mean0 < L.value L.hiIndex - L.mean0
    linarith [hu.2]
  have hvlo' : D.lo < v - L.mean0 := by
    change L.value L.loIndex - L.mean0 < v - L.mean0
    linarith
  have hvhi : v - L.mean0 < D.hi := by
    change v - L.mean0 < L.value L.hiIndex - L.mean0
    have h := D.hmuhi
    change 0 < L.value L.hiIndex - L.mean0 at h
    linarith
  let c := finiteSupportMeanInverse D (u - L.mean0)
  have hcspec : D.mean c = u - L.mean0 :=
    finiteSupportMeanInverse_spec D hulo huhi
  have hvspec := finiteSupportMeanInverse_spec D hvlo' hvhi
  have hvc : finiteSupportMeanInverse D (v - L.mean0) < c :=
    hmono.lt_iff_lt.mp (by rw [hvspec, hcspec]; linarith [hu.1])
  have hcneg : c < 0 := hmono.lt_iff_lt.mp (by
    rw [hcspec, D.mean_zero]
    change u - L.mean0 < (0 : ℝ)
    linarith [hu.2])
  apply L.rawLegendreRate_gt_meanEnvelopeLeft Q hQ hQpos hV hvlo hvmu
  refine ⟨c, ⟨hvc, hcneg⟩, ?_⟩
  change L.variance c < Q (D.mean c + L.mean0)
  rw [hcspec, sub_add_cancel]
  exact hgu

/-- Strictness under the manuscript's positive-length interval condition. -/
theorem FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeRight_of_interval
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvmu : L.mean0 < v) (hvhi : v < L.value L.hiIndex)
    (hgap : ∃ a b : ℝ, L.mean0 ≤ a ∧ a < b ∧ b ≤ v ∧
      ∀ u ∈ Ioo a b, L.variance (finiteSupportMeanInverse
        (L.toTiltCurve L.variance_pos) (u - L.mean0)) < Q u) :
    (∫ u : ℝ in L.mean0..v, (v-u)/Q u) < L.rawLegendreRate v := by
  apply L.rawLegendreRate_gt_meanEnvelopeRight_of_mean_gap Q hQ hQpos hV hvmu hvhi
  obtain ⟨a, b, hμa, hab, hbv, hstrict⟩ := hgap
  refine ⟨(a+b)/2, ⟨by linarith, by linarith⟩, ?_⟩
  exact hstrict _ ⟨by linarith, by linarith⟩

/-- The lower-target positive-length interval condition. -/
theorem FiniteSupportLawData.rawLegendreRate_gt_meanEnvelopeLeft_of_interval
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo (L.value L.loIndex) (L.value L.hiIndex)))
    (hQpos : ∀ u ∈ Ioo (L.value L.loIndex) (L.value L.hiIndex), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t + L.mean0))
    {v : ℝ} (hvlo : L.value L.loIndex < v) (hvmu : v < L.mean0)
    (hgap : ∃ a b : ℝ, v ≤ a ∧ a < b ∧ b ≤ L.mean0 ∧
      ∀ u ∈ Ioo a b, L.variance (finiteSupportMeanInverse
        (L.toTiltCurve L.variance_pos) (u - L.mean0)) < Q u) :
    (∫ u : ℝ in v..L.mean0, (u-v)/Q u) < L.rawLegendreRate v := by
  apply L.rawLegendreRate_gt_meanEnvelopeLeft_of_mean_gap Q hQ hQpos hV hvlo hvmu
  obtain ⟨a, b, hva, hab, hbμ, hstrict⟩ := hgap
  refine ⟨(a+b)/2, ⟨by linarith, by linarith⟩, ?_⟩
  exact hstrict _ ⟨by linarith, by linarith⟩

/-- Exact upper endpoint rate of the original finite law. -/
theorem FiniteSupportLawData.rawLegendreRate_hi
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    L.rawLegendreRate (L.value L.hiIndex) = -Real.log (L.weight L.hiIndex) := by
  rw [L.rawLegendreRate_eq_centered]
  exact L.legendreRate_hi

/-- Exact lower endpoint rate of the original finite law. -/
theorem FiniteSupportLawData.rawLegendreRate_lo
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    L.rawLegendreRate (L.value L.loIndex) = -Real.log (L.weight L.loIndex) := by
  rw [L.rawLegendreRate_eq_centered]
  exact L.legendreRate_lo

end
end ExactHoeffding
