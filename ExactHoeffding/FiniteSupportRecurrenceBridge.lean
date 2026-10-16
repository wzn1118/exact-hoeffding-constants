import ExactHoeffding.FiniteSupportChernoffEnvelope

/-!
# Finite-support instantiation of the mean-envelope interface

Positive recurrence laws are actual finite probability laws on the ordered
support `0,...,degree`.  This bridge supplies all fields of the general
finite-support tilt curve from the already proved finite-sum derivative and
endpoint theorems.
-/

namespace ExactHoeffding
noncomputable section

/-- The analytic finite-support curve carried by a positive recurrence law. -/
def RealRecurrenceLaw.toFiniteSupportTiltCurve
    (L : RealRecurrenceLaw) (hm : 0 < L.degree) : FiniteSupportTiltCurve where
  lo := 0
  hi := (L.degree : ℝ)
  mu := L.mean 0
  mean := L.mean
  variance := L.variance
  logMGF := fun t => Real.log (L.mgf t)
  hlomu := L.mean_pos hm 0
  hmuhi := L.mean_lt hm 0
  mean_zero := rfl
  mean_range := fun t => ⟨L.mean_pos hm t, L.mean_lt hm t⟩
  mean_deriv := L.mean_hasDerivAt
  variance_pos := L.variance_pos hm
  variance_continuous := continuous_iff_continuousAt.mpr (fun t =>
    (L.variance_differentiableAt t).continuousAt)
  mean_atBot := L.mean_tendsto_atBot hm
  mean_atTop := L.mean_tendsto_atTop hm
  logMGF_zero := by simp [L.mgf_zero]
  logMGF_deriv := by
    intro t
    simpa [RealRecurrenceLaw.mean, RealRecurrenceLaw.mgf] using
      (finiteLogMGF_hasDerivAt
        (Finset.range (L.degree + 1)) L.mass (fun i => (i : ℝ))
        L.mass_nonneg L.mass_total t)

/-- The generic rate is definitionally the recurrence-law rate. -/
theorem RealRecurrenceLaw.toFiniteSupportTiltCurve_rate_eq
    (L : RealRecurrenceLaw) (hm : 0 < L.degree) (v : ℝ) :
    finiteSupportLegendreRate (L.toFiniteSupportTiltCurve hm) v =
      recurrenceLegendreRate L v := by
  rfl

end
end ExactHoeffding
