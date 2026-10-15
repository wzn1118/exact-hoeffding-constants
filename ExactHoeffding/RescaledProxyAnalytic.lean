import ExactHoeffding.AnalyticQuotientKernels

/-!
# Actual jointly analytic rescaled proxy near inverse population zero

The auxiliary expression below removes the factor `t^2` explicitly from
`log M(e,t) - μ(e)t`. Its value at nonzero tilt is proved equal to that
quotient; no analyticity of the quotient is assumed.
-/

namespace ExactHoeffding

noncomputable section

open scoped Topology

def rescaledMean (m : ℕ) (s e : ℝ) : ℝ := (m : ℝ) * (1 - s * e) / 2

theorem rescaledFactorialMoment_degree_one (m : ℕ) (s e : ℝ) :
    rescaledFactorialMoment m s 1 e = rescaledMean m s e := by
  simp [rescaledFactorialMoment, rescaledMean, rescaledPopulationDenom,
    scaledFalling, mul_div_assoc]

theorem expQuadraticKernel_at_zero : expQuadraticKernel 0 = (1 / 2 : ℝ) := by
  have h := (analyticAt_rexp (x := (0 : ℝ))).hasFPowerSeriesAt
    |>.has_fpower_series_dslope_fslope |>.has_fpower_series_dslope_fslope
  have hz := h.coeff_zero 1
  simpa [expQuadraticKernel, expSlopeKernel, FormalMultilinearSeries.coeff_fslope,
    iteratedDeriv_eq_iterate] using hz.symm

def rescaledMGFQuadratic (m : ℕ) (s e t : ℝ) : ℝ :=
  rescaledMean m s e * expQuadraticKernel t +
    ∑ j ∈ Finset.range (m - 1),
      rescaledFactorialMoment m s (j + 2) e / (Nat.factorial (j + 2) : ℝ) *
        t ^ j * expSlopeKernel t ^ (j + 2)

theorem rescaledMGF_split (m : ℕ) (hm : 1 ≤ m) (s e t : ℝ) :
    rescaledMGF m s e t = 1 + rescaledMean m s e * (Real.exp t - 1) +
      ∑ j ∈ Finset.range (m - 1),
        rescaledFactorialMoment m s (j + 2) e / (Nat.factorial (j + 2) : ℝ) *
          (Real.exp t - 1) ^ (j + 2) := by
  unfold rescaledMGF
  rw [show m + 1 = 2 + (m - 1) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    rescaledFactorialMoment_degree_zero, rescaledFactorialMoment_degree_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, pow_zero,
    pow_one, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_comm 2 j]

theorem rescaledMGF_quadratic_factor (m : ℕ) (hm : 1 ≤ m) (s e t : ℝ) :
    rescaledMGF m s e t =
      1 + rescaledMean m s e * t + t ^ 2 * rescaledMGFQuadratic m s e t := by
  rw [rescaledMGF_split m hm, rescaledMGFQuadratic, mul_add, Finset.mul_sum]
  have htail :
      (∑ j ∈ Finset.range (m - 1),
        rescaledFactorialMoment m s (j + 2) e / (Nat.factorial (j + 2) : ℝ) *
          (Real.exp t - 1) ^ (j + 2)) =
      ∑ j ∈ Finset.range (m - 1),
        t ^ 2 * (rescaledFactorialMoment m s (j + 2) e /
          (Nat.factorial (j + 2) : ℝ) * t ^ j * expSlopeKernel t ^ (j + 2)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [exp_sub_one_factor, mul_pow, pow_add]
    ring
  rw [htail, exp_sub_one_factor]
  have h := expSlopeKernel_factor t
  nlinarith [congrArg (fun r : ℝ => rescaledMean m s e * t * r) h]

theorem rescaledMGFQuadratic_joint_analytic (m : ℕ) (s : ℝ) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => rescaledMGFQuadratic m s u.1 u.2) (0, 0) := by
  unfold rescaledMGFQuadratic
  apply AnalyticAt.add
  · apply AnalyticAt.mul
    · unfold rescaledMean
      exact (analyticAt_const.mul
        (analyticAt_const.sub (analyticAt_const.mul analyticAt_fst))).div_const
    · exact expQuadraticKernel_analytic.comp_of_eq
        (analyticAt_snd : AnalyticAt ℝ (fun u : ℝ × ℝ => u.2) (0, 0)) rfl
  · apply Finset.analyticAt_fun_sum
    intro j hj
    exact (((rescaledFactorialMoment_joint_analytic m (j + 2) s (0, 0)
      (by simp)).div_const).mul (analyticAt_snd.pow j)).mul
        ((expSlopeKernel_analytic.comp_of_eq
          (analyticAt_snd : AnalyticAt ℝ (fun u : ℝ × ℝ => u.2) (0, 0)) rfl).pow (j + 2))

def rescaledMGFSlope (m : ℕ) (s e t : ℝ) : ℝ :=
  rescaledMean m s e + t * rescaledMGFQuadratic m s e t

def rescaledProxyExtension (m : ℕ) (s e t : ℝ) : ℝ :=
  2 * (rescaledMGFQuadratic m s e t + rescaledMGFSlope m s e t ^ 2 *
    logQuadraticKernel (t * rescaledMGFSlope m s e t))

theorem rescaledMGFSlope_joint_analytic (m : ℕ) (s : ℝ) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => rescaledMGFSlope m s u.1 u.2) (0, 0) := by
  unfold rescaledMGFSlope rescaledMean
  exact ((analyticAt_const.mul
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_fst))).div_const).add
      (analyticAt_snd.mul (rescaledMGFQuadratic_joint_analytic m s))

theorem rescaledProxyExtension_joint_analytic (m : ℕ) (s : ℝ) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => rescaledProxyExtension m s u.1 u.2) (0, 0) := by
  unfold rescaledProxyExtension
  apply AnalyticAt.mul analyticAt_const
  apply (rescaledMGFQuadratic_joint_analytic m s).add
  apply ((rescaledMGFSlope_joint_analytic m s).pow 2).mul
  exact logQuadraticKernel_analytic.comp_of_eq
    (analyticAt_snd.mul (rescaledMGFSlope_joint_analytic m s)) (by simp)

theorem rescaled_logMGF_quadratic_factor (m : ℕ) (hm : 1 ≤ m) (s e t : ℝ) :
    Real.log (rescaledMGF m s e t) - rescaledMean m s e * t =
      t ^ 2 * rescaledProxyExtension m s e t / 2 := by
  have hM := rescaledMGF_quadratic_factor m hm s e t
  have hlog := logOnePlus_quadratic_factor (t * rescaledMGFSlope m s e t)
  have hbase : 1 + t * rescaledMGFSlope m s e t = rescaledMGF m s e t := by
    rw [hM, rescaledMGFSlope]
    ring
  rw [hbase] at hlog
  rw [hlog, rescaledProxyExtension, rescaledMGFSlope]
  ring

/-- Away from zero, the analytic extension is the actual centered quotient. -/
theorem rescaledProxyExtension_eq_quotient (m : ℕ) (hm : 1 ≤ m)
    (s e t : ℝ) (ht : t ≠ 0) :
    rescaledProxyExtension m s e t =
      2 * (Real.log (rescaledMGF m s e t) - rescaledMean m s e * t) / t ^ 2 := by
  rw [rescaled_logMGF_quadratic_factor m hm]
  field_simp

end

end ExactHoeffding
