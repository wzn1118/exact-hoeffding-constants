import ExactHoeffding.RescaledAnalyticOptimizer

/-! # The first tilt coefficient of the actual removable proxy -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem expSlopeKernel_hasDerivAt_zero :
    HasDerivAt expSlopeKernel (1 / 2 : ℝ) 0 := by
  have hd := expSlopeKernel_analytic.differentiableAt.hasDerivAt
  have heq : deriv expSlopeKernel 0 = (1 / 2 : ℝ) := by
    rw [← dslope_same]
    exact expQuadraticKernel_at_zero
  rwa [heq] at hd

theorem expQuadraticKernel_hasDerivAt_zero :
    HasDerivAt expQuadraticKernel (1 / 6 : ℝ) 0 := by
  have h := (analyticAt_rexp (x := (0 : ℝ))).hasFPowerSeriesAt
    |>.has_fpower_series_dslope_fslope |>.has_fpower_series_dslope_fslope
    |>.has_fpower_series_dslope_fslope
  have hz := h.coeff_zero 1
  have heq : deriv expQuadraticKernel 0 = (1 / 6 : ℝ) := by
    simpa [expQuadraticKernel, expSlopeKernel, dslope_same, Nat.factorial,
      FormalMultilinearSeries.coeff_fslope, iteratedDeriv_eq_iterate,
      Real.iter_deriv_exp] using hz.symm
  exact expQuadraticKernel_analytic.differentiableAt.hasDerivAt.congr_deriv heq

theorem logQuadraticKernel_hasDerivAt_zero :
    HasDerivAt logQuadraticKernel (1 / 3 : ℝ) 0 := by
  have h := hasFPowerSeriesAt_log_one_add.has_fpower_series_dslope_fslope
    |>.has_fpower_series_dslope_fslope |>.has_fpower_series_dslope_fslope
  have hz := h.coeff_zero 1
  have heq : deriv logQuadraticKernel 0 = (1 / 3 : ℝ) := by
    unfold logQuadraticKernel logSlopeKernel logOnePlus
    norm_num [FormalMultilinearSeries.coeff_fslope] at hz
    exact hz.symm
  exact logQuadraticKernel_analytic.differentiableAt.hasDerivAt.congr_deriv heq

private theorem slope_power_term_hasDerivAt_zero (j : ℕ) :
    HasDerivAt (fun t : ℝ => t ^ j * expSlopeKernel t ^ (j + 2))
      (if j = 0 then 1 else if j = 1 then 1 else 0) 0 := by
  have hd := ((hasDerivAt_id (0 : ℝ)).pow j).mul
    (expSlopeKernel_hasDerivAt_zero.pow (j + 2))
  apply hd.congr_deriv
  rcases j with _ | j
  · norm_num
  rcases j with _ | j
  · norm_num
  · simp

theorem rescaledMGFQuadratic_hasDerivAt_zero (m : ℕ) (s e : ℝ) :
    HasDerivAt (rescaledMGFQuadratic m s e)
      (rescaledMean m s e / 6 + rescaledFactorialMoment m s 2 e / 2 +
        rescaledFactorialMoment m s 3 e / 6) 0 := by
  have hsum := HasDerivAt.fun_sum (u := Finset.range (m - 1))
    (fun j _ => (slope_power_term_hasDerivAt_zero j).const_mul
      (rescaledFactorialMoment m s (j + 2) e / (Nat.factorial (j + 2) : ℝ)))
  have hd := (expQuadraticKernel_hasDerivAt_zero.const_mul (rescaledMean m s e)).add hsum
  simp only [← mul_assoc] at hd
  change HasDerivAt (rescaledMGFQuadratic m s e) _ 0 at hd
  apply hd.congr_deriv
  have hterm (j : ℕ) :
      rescaledFactorialMoment m s (j + 2) e / (Nat.factorial (j + 2) : ℝ) *
        (if j = 0 then 1 else if j = 1 then 1 else 0) =
      (if j = 0 then rescaledFactorialMoment m s 2 e / 2 else 0) +
        (if j = 1 then rescaledFactorialMoment m s 3 e / 6 else 0) := by
    by_cases hj0 : j = 0
    · subst j; norm_num
    by_cases hj1 : j = 1
    · subst j; norm_num
    simp [hj0, hj1]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  by_cases hm3 : 3 ≤ m
  · simp [Finset.sum_ite_eq', Finset.mem_range, show 0 < m - 1 by omega,
      show 1 < m - 1 by omega]
    ring
  · interval_cases m <;>
      norm_num [Finset.sum_range_succ, rescaledMean,
        rescaledFactorialMoment, Nat.descFactorial] <;> ring

theorem rescaledProxyExtension_hasDerivAt_tilt_zero (m : ℕ) (s e : ℝ) :
    HasDerivAt (rescaledProxyExtension m s e)
      ((rescaledMean m s e + 3 * rescaledFactorialMoment m s 2 e +
          rescaledFactorialMoment m s 3 e -
          3 * (rescaledMean m s e + rescaledFactorialMoment m s 2 e) *
            rescaledMean m s e + 2 * rescaledMean m s e ^ 3) / 3) 0 := by
  have hB := rescaledMGFQuadratic_hasDerivAt_zero m s e
  have hA := (hasDerivAt_const (0 : ℝ) (rescaledMean m s e)).add
    ((hasDerivAt_id (0 : ℝ)).mul hB)
  change HasDerivAt (rescaledMGFSlope m s e) _ 0 at hA
  have hz := (hasDerivAt_id (0 : ℝ)).mul hA
  have hlog := logQuadraticKernel_hasDerivAt_zero.comp_of_eq (0 : ℝ) hz (by simp)
  have hd := (hB.add ((hA.pow 2).mul hlog)).const_mul 2
  change HasDerivAt (rescaledProxyExtension m s e) _ 0 at hd
  apply hd.congr_deriv
  simp [rescaledMGFSlope, rescaledMGFQuadratic_tilt_zero]
  ring

end

end ExactHoeffding
