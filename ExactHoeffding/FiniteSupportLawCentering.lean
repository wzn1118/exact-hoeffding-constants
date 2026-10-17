import ExactHoeffding.FiniteSupportLawVariance

/-! # Centering identities for finite-support logarithmic MGFs and rates

The logarithmic MGF of the original finite law differs from its centered
logarithmic MGF by the linear mean term. Consequently its Legendre rate and
mean-coordinate envelope integrals are exactly translations of the centered
ones, throughout their real domains.
-/

namespace ExactHoeffding
noncomputable section

/-- The logarithmic MGF of the original, uncentered finite law. -/
def FiniteSupportLawData.rawLogMGF
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) : ℝ :=
  Real.log (finiteMGF L.support L.weight L.value t)

/-- The Legendre rate of the original, uncentered finite law. -/
def FiniteSupportLawData.rawLegendreRate
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (v : ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ => t * v - L.rawLogMGF t))

/-- Centering removes precisely the linear term given by the ordinary mean. -/
theorem FiniteSupportLawData.rawLogMGF_eq_centered
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) :
    L.rawLogMGF t = L.logMGF t + t * L.mean0 := by
  have hvalues : L.value = fun i => L.centeredValue i + L.mean0 := by
    funext i
    simp [FiniteSupportLawData.centeredValue]
  have hpos := finiteMGF_pos_of_normalized L.support L.weight L.centeredValue
    L.weight_nonneg L.weight_total t
  unfold FiniteSupportLawData.rawLogMGF
  rw [hvalues, finiteMGF_shift, Real.log_mul (ne_of_gt (Real.exp_pos _))
    (ne_of_gt hpos), Real.log_exp]
  change t * L.mean0 + L.logMGF t = L.logMGF t + t * L.mean0
  ring

/-- Translation of the actual Legendre rate, with any realization of the
centered tilt curve. No rate comparison is assumed. -/
theorem FiniteSupportLawData.rawLegendreRate_eq_centered_of_variance_pos
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (hvar : ∀ t : ℝ, 0 < L.variance t) (v : ℝ) :
    L.rawLegendreRate v =
      finiteSupportLegendreRate (L.toTiltCurve hvar) (v - L.mean0) := by
  unfold FiniteSupportLawData.rawLegendreRate finiteSupportLegendreRate
  congr 1
  apply congrArg Set.range
  funext t
  rw [L.rawLogMGF_eq_centered]
  change t * v - (L.logMGF t + t * L.mean0) =
    t * (v - L.mean0) - L.logMGF t
  ring

/-- The finite law itself supplies the positive-variance realization needed
for the centered rate identity. -/
theorem FiniteSupportLawData.rawLegendreRate_eq_centered
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (v : ℝ) :
    L.rawLegendreRate v =
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) (v - L.mean0) :=
  L.rawLegendreRate_eq_centered_of_variance_pos L.variance_pos v

/-- Translation of the right envelope integral, with no integrability
hypothesis needed for the change-of-variable identity. -/
theorem FiniteSupportLawData.meanEnvelopeIntegralRight_shift
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (v : ℝ) :
    (∫ u : ℝ in 0..(v - L.mean0),
      ((v - L.mean0) - u) / Q (u + L.mean0)) =
      ∫ u : ℝ in L.mean0..v, (v - u) / Q u := by
  have h := intervalIntegral.integral_comp_add_right
    (fun u : ℝ => (v - u) / Q u) (a := (0 : ℝ))
    (b := v - L.mean0) L.mean0
  have hfun : (fun u : ℝ => (v - (u + L.mean0)) / Q (u + L.mean0)) =
      (fun u : ℝ => ((v - L.mean0) - u) / Q (u + L.mean0)) := by
    funext u
    congr 1
    ring
  rw [hfun] at h
  simpa only [zero_add, sub_add_cancel] using h

/-- Translation of the left envelope integral. -/
theorem FiniteSupportLawData.meanEnvelopeIntegralLeft_shift
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (v : ℝ) :
    (∫ u : ℝ in (v - L.mean0)..0,
      (u - (v - L.mean0)) / Q (u + L.mean0)) =
      ∫ u : ℝ in v..L.mean0, (u - v) / Q u := by
  have h := intervalIntegral.integral_comp_add_right
    (fun u : ℝ => (u - v) / Q u) (a := v - L.mean0)
    (b := (0 : ℝ)) L.mean0
  have hfun : (fun u : ℝ => (u + L.mean0 - v) / Q (u + L.mean0)) =
      (fun u : ℝ => (u - (v - L.mean0)) / Q (u + L.mean0)) := by
    funext u
    congr 1
    ring
  rw [hfun] at h
  simpa only [zero_add, sub_add_cancel] using h

end
end ExactHoeffding
