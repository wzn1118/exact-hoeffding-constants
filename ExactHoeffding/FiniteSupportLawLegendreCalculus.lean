import ExactHoeffding.FiniteSupportLegendreCalculus
import ExactHoeffding.FiniteSupportLawCentering

/-! # Legendre calculus for the actual uncentered finite law

The derivatives concern the rate defined from the original weighted MGF.
Every target lies in the actual open support; no derivative or inverse
regularity assumption is supplied by the caller.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- The actual tilt attaining an ordinary-coordinate interior mean. -/
def FiniteSupportLawData.rawMeanInverse
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (v : ℝ) : ℝ :=
  finiteSupportMeanInverse (L.toTiltCurve L.variance_pos) (v - L.mean0)

/-- The inverse returns a tilt with the requested actual mean. -/
theorem FiniteSupportLawData.rawMeanInverse_spec
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hvlo : L.value L.loIndex < v) (hvhi : v < L.value L.hiIndex) :
    L.mean (L.rawMeanInverse v) + L.mean0 = v := by
  have h := finiteSupportMeanInverse_spec (L.toTiltCurve L.variance_pos)
    (show L.value L.loIndex - L.mean0 < v - L.mean0 by linarith)
    (show v - L.mean0 < L.value L.hiIndex - L.mean0 by linarith)
  change L.mean (L.rawMeanInverse v) = v - L.mean0 at h
  linarith

/-- The actual inverse tilt has derivative reciprocal tilted variance. -/
theorem FiniteSupportLawData.rawMeanInverse_hasDerivAt
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hvlo : L.value L.loIndex < v) (hvhi : v < L.value L.hiIndex) :
    HasDerivAt L.rawMeanInverse (L.variance (L.rawMeanInverse v))⁻¹ v := by
  have h := (finiteSupportMeanInverse_hasDerivAt (L.toTiltCurve L.variance_pos)
    (show L.value L.loIndex - L.mean0 < v - L.mean0 by linarith)
    (show v - L.mean0 < L.value L.hiIndex - L.mean0 by linarith)).comp v
      ((hasDerivAt_id v).sub_const L.mean0)
  simpa only [mul_one] using! h

/-- First derivative of the actual raw Legendre transform. -/
theorem FiniteSupportLawData.rawLegendreRate_hasDerivAt
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hvlo : L.value L.loIndex < v) (hvhi : v < L.value L.hiIndex) :
    HasDerivAt L.rawLegendreRate (L.rawMeanInverse v) v := by
  have h := (finiteSupportLegendreRate_hasDerivAt (L.toTiltCurve L.variance_pos)
    (show L.value L.loIndex - L.mean0 < v - L.mean0 by linarith)
    (show v - L.mean0 < L.value L.hiIndex - L.mean0 by linarith)).comp v
      ((hasDerivAt_id v).sub_const L.mean0)
  have h' := h.congr_deriv (mul_one _)
  apply h'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun u => L.rawLegendreRate_eq_centered u)

/-- Exact first derivative in the manuscript's ordinary support coordinates. -/
theorem FiniteSupportLawData.rawLegendreRate_deriv
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hvlo : L.value L.loIndex < v) (hvhi : v < L.value L.hiIndex) :
    deriv L.rawLegendreRate v = L.rawMeanInverse v :=
  (L.rawLegendreRate_hasDerivAt hvlo hvhi).deriv

/-- Differentiability of the first actual Legendre derivative. -/
theorem FiniteSupportLawData.rawLegendreRate_deriv_hasDerivAt
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hvlo : L.value L.loIndex < v) (hvhi : v < L.value L.hiIndex) :
    HasDerivAt (deriv L.rawLegendreRate)
      (L.variance (L.rawMeanInverse v))⁻¹ v := by
  apply (L.rawMeanInverse_hasDerivAt hvlo hvhi).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hvlo hvhi] with u hu
  exact L.rawLegendreRate_deriv hu.1 hu.2

/-- Exact second derivative at every target of the actual open support. -/
theorem FiniteSupportLawData.rawLegendreRate_second_deriv
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hvlo : L.value L.loIndex < v) (hvhi : v < L.value L.hiIndex) :
    deriv (deriv L.rawLegendreRate) v =
      1 / L.variance (L.rawMeanInverse v) := by
  simpa only [one_div] using (L.rawLegendreRate_deriv_hasDerivAt hvlo hvhi).deriv

/-- The actual Legendre rate vanishes at the ordinary mean. -/
theorem FiniteSupportLawData.rawLegendreRate_at_mean0
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    L.rawLegendreRate L.mean0 = 0 := by
  rw [L.rawLegendreRate_eq_centered, sub_self]
  exact finiteSupportLegendreRate_at_mu (L.toTiltCurve L.variance_pos)

/-- Zero tilt is the inverse of the ordinary mean. -/
theorem FiniteSupportLawData.rawMeanInverse_mean0
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    L.rawMeanInverse L.mean0 = 0 := by
  let D := L.toTiltCurve L.variance_pos
  change finiteSupportMeanInverse D (L.mean0 - L.mean0) = 0
  rw [sub_self]
  exact ((finiteSupportMeanInverse_unique D D.hlomu D.hmuhi).mp D.mean_zero).symm

/-- The actual first Legendre derivative vanishes at the ordinary mean. -/
theorem FiniteSupportLawData.rawLegendreRate_deriv_at_mean0
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    deriv L.rawLegendreRate L.mean0 = 0 := by
  have hlo : L.value L.loIndex < L.mean0 := by
    have h := (L.toTiltCurve L.variance_pos).hlomu
    change L.value L.loIndex - L.mean0 < 0 at h
    linarith
  have hhi : L.mean0 < L.value L.hiIndex := by
    have h := (L.toTiltCurve L.variance_pos).hmuhi
    change 0 < L.value L.hiIndex - L.mean0 at h
    linarith
  rw [L.rawLegendreRate_deriv hlo hhi, L.rawMeanInverse_mean0]

end
end ExactHoeffding
