import ExactHoeffding.FiniteSupportMeanEnvelope
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-! # Interior derivatives of the finite-support Legendre transform

The inverse tilted mean is differentiable because the actual mean curve is
strictly increasing with positive variance. Interior attainment then gives
the first and second derivatives of the Legendre rate.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- The inverse tilted mean is continuous at every interior target. -/
theorem finiteSupportMeanInverse_continuousAt
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    ContinuousAt (finiteSupportMeanInverse D) v := by
  have hmono : StrictMono D.mean :=
    strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
  have hspec : D.mean (finiteSupportMeanInverse D v) = v :=
    finiteSupportMeanInverse_spec D hvlo hvhi
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hav : D.mean a < v := (hmono ha).trans_eq hspec
    filter_upwards [Ioo_mem_nhds hvlo hvhi, Ioi_mem_nhds hav] with u hu hau
    have huspec := finiteSupportMeanInverse_spec D hu.1 hu.2
    exact hmono.lt_iff_lt.mp (huspec.symm ▸ hau)
  · intro b hb
    have hvb : v < D.mean b := hspec ▸ hmono hb
    filter_upwards [Ioo_mem_nhds hvlo hvhi, Iio_mem_nhds hvb] with u hu hub
    have huspec := finiteSupportMeanInverse_spec D hu.1 hu.2
    exact hmono.lt_iff_lt.mp (huspec.symm ▸ hub)

/-- Derivative of the inverse tilted mean: reciprocal actual variance. -/
theorem finiteSupportMeanInverse_hasDerivAt
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    HasDerivAt (finiteSupportMeanInverse D)
      (D.variance (finiteSupportMeanInverse D v))⁻¹ v := by
  apply HasDerivAt.of_local_left_inverse
    (finiteSupportMeanInverse_continuousAt D hvlo hvhi)
    (D.mean_deriv _) (ne_of_gt (D.variance_pos _))
  filter_upwards [Ioo_mem_nhds hvlo hvhi] with u hu
  exact finiteSupportMeanInverse_spec D hu.1 hu.2

/-- First derivative of the actual finite-support Legendre rate. -/
theorem finiteSupportLegendreRate_hasDerivAt
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    HasDerivAt (finiteSupportLegendreRate D) (finiteSupportMeanInverse D v) v := by
  have ht := finiteSupportMeanInverse_hasDerivAt D hvlo hvhi
  have hψ := (D.logMGF_deriv (finiteSupportMeanInverse D v)).comp v ht
  have h := (ht.mul (hasDerivAt_id v)).sub hψ
  have hderiv :
      (D.variance (finiteSupportMeanInverse D v))⁻¹ * v +
        finiteSupportMeanInverse D v * 1 -
        D.mean (finiteSupportMeanInverse D v) *
          (D.variance (finiteSupportMeanInverse D v))⁻¹ =
        finiteSupportMeanInverse D v := by
    rw [finiteSupportMeanInverse_spec D hvlo hvhi]
    ring
  have h' := h.congr_deriv hderiv
  apply h'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hvlo hvhi] with u hu
  exact finiteSupportLegendreRate_at_mean D hu.1 hu.2

/-- Ordinary derivative form of the inverse-tilt identity. -/
theorem finiteSupportLegendreRate_deriv
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    deriv (finiteSupportLegendreRate D) v = finiteSupportMeanInverse D v :=
  (finiteSupportLegendreRate_hasDerivAt D hvlo hvhi).deriv

/-- The first Legendre derivative has derivative reciprocal variance. -/
theorem finiteSupportLegendreRate_deriv_hasDerivAt
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    HasDerivAt (deriv (finiteSupportLegendreRate D))
      (D.variance (finiteSupportMeanInverse D v))⁻¹ v := by
  apply (finiteSupportMeanInverse_hasDerivAt D hvlo hvhi).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hvlo hvhi] with u hu
  exact finiteSupportLegendreRate_deriv D hu.1 hu.2

/-- Second Legendre derivative on the entire open support. -/
theorem finiteSupportLegendreRate_second_deriv
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    deriv (deriv (finiteSupportLegendreRate D)) v =
      1 / D.variance (finiteSupportMeanInverse D v) := by
  simpa only [one_div] using
    (finiteSupportLegendreRate_deriv_hasDerivAt D hvlo hvhi).deriv

/-- The zero-tilt mean has Legendre value zero. -/
theorem finiteSupportLegendreRate_at_mu (D : FiniteSupportTiltCurve) :
    finiteSupportLegendreRate D D.mu = 0 := by
  have ht : finiteSupportMeanInverse D D.mu = 0 :=
    ((finiteSupportMeanInverse_unique D D.hlomu D.hmuhi).mp D.mean_zero).symm
  rw [finiteSupportLegendreRate_at_mean D D.hlomu D.hmuhi, ht, D.logMGF_zero]
  ring

/-- The first Legendre derivative vanishes at the ordinary mean. -/
theorem finiteSupportLegendreRate_deriv_at_mu (D : FiniteSupportTiltCurve) :
    deriv (finiteSupportLegendreRate D) D.mu = 0 := by
  rw [finiteSupportLegendreRate_deriv D D.hlomu D.hmuhi]
  exact ((finiteSupportMeanInverse_unique D D.hlomu D.hmuhi).mp D.mean_zero).symm

end
end ExactHoeffding
