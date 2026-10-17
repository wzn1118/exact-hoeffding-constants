import ExactHoeffding.FiniteSupportLawCentering

/-! # Actual uncentered logarithmic-MGF derivatives -/

namespace ExactHoeffding
noncomputable section

/-- The first derivative of the actual uncentered log-MGF is its tilted mean. -/
theorem FiniteSupportLawData.rawLogMGF_hasDerivAt
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) :
    HasDerivAt L.rawLogMGF (L.mean t + L.mean0) t := by
  have hcenter : HasDerivAt L.logMGF (L.mean t) t := by
    exact finiteLogMGF_hasDerivAt L.support L.weight L.centeredValue
      L.weight_nonneg L.weight_total t
  have h := hcenter.add ((hasDerivAt_id t).mul_const L.mean0)
  have heq : L.rawLogMGF = fun u => L.logMGF u + u * L.mean0 := by
    funext u
    exact L.rawLogMGF_eq_centered u
  rw [heq]
  simpa only [Pi.add_apply, id_eq, one_mul] using! h

/-- The ordinary-coordinate tilted mean has derivative equal to actual variance. -/
theorem FiniteSupportLawData.rawTiltMean_hasDerivAt
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) :
    HasDerivAt (fun u => L.mean u + L.mean0) (L.variance t) t := by
  exact ((L.toTiltCurve L.variance_pos).mean_deriv t).add_const L.mean0

/-- The actual raw log-MGF has the actual tilted variance as second derivative. -/
theorem FiniteSupportLawData.rawLogMGF_second_deriv
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) :
    deriv (deriv L.rawLogMGF) t = L.variance t := by
  have hfirst : deriv L.rawLogMGF = fun u => L.mean u + L.mean0 := by
    funext u
    exact (L.rawLogMGF_hasDerivAt u).deriv
  rw [hfirst]
  exact (L.rawTiltMean_hasDerivAt t).deriv

/-- Strict monotonicity holds for the actual tilted mean. -/
theorem FiniteSupportLawData.rawTiltMean_strictMono
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    StrictMono (fun t => L.mean t + L.mean0) :=
  strictMono_of_hasDerivAt_pos L.rawTiltMean_hasDerivAt L.variance_pos

end
end ExactHoeffding
