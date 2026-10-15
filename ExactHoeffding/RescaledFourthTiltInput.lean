import ExactHoeffding.RescaledThirdOrderInputs
import ExactHoeffding.ActualOptimumSecondExpansion

/-! # Fourth tilt coefficient of the actual rescaled proxy

The factorial-polynomial expression is derived from the analytic removable
proxy itself. It is not assumed to be a logarithmic derivative.
-/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

private theorem dslope_iteratedDeriv_zero (f : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) (n : ℕ) :
    iteratedDeriv n (dslope f 0) 0 / (n.factorial : ℝ) =
      iteratedDeriv (n + 1) f 0 / ((n + 1).factorial : ℝ) := by
  have h := hf.hasFPowerSeriesAt.has_fpower_series_dslope_fslope
    |>.eq_formalMultilinearSeries (analyticAt_dslope_zero hf).hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff n) h
  simpa only [FormalMultilinearSeries.coeff_fslope,
    FormalMultilinearSeries.coeff_ofScalars] using hc.symm

theorem expSlopeKernel_deriv2_zero :
    iteratedDeriv 2 expSlopeKernel 0 = (1 / 3 : ℝ) := by
  have h := dslope_iteratedDeriv_zero Real.exp analyticAt_rexp 2
  norm_num [expSlopeKernel, Nat.factorial, iteratedDeriv_eq_iterate,
    Real.iter_deriv_exp] at h ⊢
  linarith

theorem expQuadraticKernel_deriv2_zero :
    iteratedDeriv 2 expQuadraticKernel 0 = (1 / 12 : ℝ) := by
  have h := dslope_iteratedDeriv_zero expSlopeKernel expSlopeKernel_analytic 2
  have h' := dslope_iteratedDeriv_zero Real.exp analyticAt_rexp 3
  have hexp : iteratedDeriv 4 Real.exp 0 = 1 := by
    simp [iteratedDeriv_eq_iterate, Real.iter_deriv_exp]
  norm_num only [Nat.factorial, hexp, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at h'
  change iteratedDeriv 3 expSlopeKernel 0 / 6 = (1 / 24 : ℝ) at h'
  change iteratedDeriv 2 expQuadraticKernel 0 / 2 =
    iteratedDeriv 3 expSlopeKernel 0 / 6 at h
  linarith

theorem logQuadraticKernel_deriv2_zero :
    iteratedDeriv 2 logQuadraticKernel 0 = -(1 / 2 : ℝ) := by
  have hp := hasFPowerSeriesAt_log_one_add.has_fpower_series_dslope_fslope
    |>.has_fpower_series_dslope_fslope
  have h := hp.eq_formalMultilinearSeries logQuadraticKernel_analytic.hasFPowerSeriesAt
  have hc := congrArg (fun p : FormalMultilinearSeries ℝ ℝ ℝ => p.coeff 2) h
  norm_num [FormalMultilinearSeries.coeff_fslope, Nat.factorial] at hc
  linarith

theorem analytic_mul_iteratedDeriv2 (f g : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) :
    iteratedDeriv 2 (fun t => f t * g t) 0 =
      iteratedDeriv 2 f 0 * g 0 + 2 * deriv f 0 * deriv g 0 +
        f 0 * iteratedDeriv 2 g 0 := by
  rw [iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, Nat.choose]
  ring

theorem analytic_comp_iteratedDeriv2_zero (f g : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (hfzero : f 0 = 0) :
    iteratedDeriv 2 (fun t => g (f t)) 0 =
      iteratedDeriv 2 g 0 * (deriv f 0) ^ 2 + deriv g 0 * iteratedDeriv 2 f 0 := by
  have heq : deriv (fun t => g (f t)) =ᶠ[𝓝 0]
      (fun t => deriv g (f t) * deriv f t) := by
    have hc : Tendsto f (𝓝 0) (𝓝 0) := by
      have h := hf.continuousAt
      rwa [ContinuousAt, hfzero] at h
    filter_upwards [hf.eventually_analyticAt, hc.eventually hg.eventually_analyticAt]
      with t ht hgt
    exact (hgt.differentiableAt.hasDerivAt.comp t ht.differentiableAt.hasDerivAt).deriv
  have hg' := hg.deriv.differentiableAt.hasDerivAt.comp_of_eq 0
    hf.differentiableAt.hasDerivAt hfzero.symm
  have hd := hg'.mul hf.deriv.differentiableAt.hasDerivAt
  change HasDerivAt (fun t => deriv g (f t) * deriv f t) _ 0 at hd
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one,
    heq.deriv_eq, hd.deriv]
  simp only [Function.comp_apply, hfzero, show deriv (deriv g) 0 = iteratedDeriv 2 g 0 by
      rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one],
    show deriv (deriv f) 0 = iteratedDeriv 2 f 0 by
      rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]]
  ring

private theorem slope_power_term_deriv2_zero (j : ℕ) :
    iteratedDeriv 2 (fun t : ℝ => t ^ j * expSlopeKernel t ^ (j + 2)) 0 =
      if j = 0 then 7 / 6 else if j = 1 then 3 else if j = 2 then 2 else 0 := by
  have hs : AnalyticAt ℝ expSlopeKernel 0 := expSlopeKernel_analytic
  have hd (n : ℕ) : deriv (fun t => expSlopeKernel t ^ n) 0 = (n : ℝ) / 2 := by
    have h := expSlopeKernel_hasDerivAt_zero.pow n
    change HasDerivAt (fun t => expSlopeKernel t ^ n) _ 0 at h
    rw [h.deriv]
    simp
    ring
  rw [analytic_mul_iteratedDeriv2 (fun t : ℝ => t ^ j)
    (fun t => expSlopeKernel t ^ (j + 2)) (by fun_prop) (hs.pow _), hd]
  simp only [iteratedDeriv_fun_pow_zero, expSlopeKernel_zero, one_pow]
  rcases j with _ | j
  · norm_num
    have heq : (fun t => expSlopeKernel t ^ 2) =
        (fun t => expSlopeKernel t * expSlopeKernel t) := by funext t; ring
    rw [heq, analytic_mul_iteratedDeriv2 _ _ hs hs,
      expSlopeKernel_deriv2_zero, expSlopeKernel_hasDerivAt_zero.deriv]
    norm_num
  rcases j with _ | j
  · norm_num
  rcases j with _ | j
  · norm_num
  · norm_num
    omega

theorem rescaledMGFQuadratic_deriv2_zero (m : ℕ) (s e : ℝ) :
    iteratedDeriv 2 (rescaledMGFQuadratic m s e) 0 =
      rescaledMean m s e / 12 + 7 * rescaledFactorialMoment m s 2 e / 12 +
        rescaledFactorialMoment m s 3 e / 2 + rescaledFactorialMoment m s 4 e / 12 := by
  unfold rescaledMGFQuadratic
  have hE : ContDiffAt ℝ 2 expQuadraticKernel 0 := expQuadraticKernel_analytic.contDiffAt
  have hS : ContDiffAt ℝ 2 expSlopeKernel 0 := expSlopeKernel_analytic.contDiffAt
  rw [iteratedDeriv_fun_add (by fun_prop)
    (by apply ContDiffAt.sum; intro j hj; fun_prop),
    iteratedDeriv_const_mul_field, expQuadraticKernel_deriv2_zero,
    iteratedDeriv_fun_sum (by intro j hj; fun_prop)]
  simp only [mul_assoc]
  simp_rw [iteratedDeriv_const_mul_field, slope_power_term_deriv2_zero]
  have hterm (j : ℕ) :
      rescaledFactorialMoment m s (j + 2) e / (Nat.factorial (j + 2) : ℝ) *
        (if j = 0 then 7 / 6 else if j = 1 then 3 else if j = 2 then 2 else 0) =
      (if j = 0 then 7 * rescaledFactorialMoment m s 2 e / 12 else 0) +
      (if j = 1 then rescaledFactorialMoment m s 3 e / 2 else 0) +
      (if j = 2 then rescaledFactorialMoment m s 4 e / 12 else 0) := by
    by_cases h0 : j = 0
    · subst j; norm_num; ring
    by_cases h1 : j = 1
    · subst j; norm_num; ring
    by_cases h2 : j = 2
    · subst j; norm_num; ring
    simp [h0, h1, h2]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  by_cases hm4 : 4 ≤ m
  · simp [Finset.sum_ite_eq', Finset.mem_range, show 0 < m - 1 by omega,
      show 1 < m - 1 by omega, show 2 < m - 1 by omega]
    ring
  · interval_cases m <;>
      norm_num [Finset.sum_range_succ, rescaledMean,
        rescaledFactorialMoment, Nat.descFactorial] <;> ring

/-- Fourth ordinary cumulant polynomial in the actual factorial coefficients. -/
def rescaledFourthCumulantPolynomial (m : ℕ) (s e : ℝ) : ℝ :=
  let a := rescaledMean m s e
  let b := rescaledFactorialMoment m s 2 e
  let c := rescaledFactorialMoment m s 3 e
  let d := rescaledFactorialMoment m s 4 e
  a + 7 * b + 6 * c + d - 4 * a * (a + 3 * b + c) -
    3 * (a + b) ^ 2 + 12 * a ^ 2 * (a + b) - 6 * a ^ 4

/-- The fourth cumulant polynomial is derived from the actual removable
proxy's second tilt derivative, with no positivity hypothesis on real `e`. -/
theorem rescaledProxyExtension_deriv2_tilt_zero (m : ℕ) (s e : ℝ) :
    iteratedDeriv 2 (rescaledProxyExtension m s e) 0 =
      rescaledFourthCumulantPolynomial m s e / 6 := by
  let B := rescaledMGFQuadratic m s e
  let A := rescaledMGFSlope m s e
  let Z : ℝ → ℝ := fun t => t * A t
  let L : ℝ → ℝ := fun t => logQuadraticKernel (Z t)
  have hB : AnalyticAt ℝ B 0 := by
    dsimp [B, rescaledMGFQuadratic]
    apply AnalyticAt.add (analyticAt_const.mul expQuadraticKernel_analytic)
    apply Finset.analyticAt_fun_sum
    intro j hj
    exact (analyticAt_const.mul (analyticAt_id.pow j)).mul
      (expSlopeKernel_analytic.pow (j + 2))
  have hA : AnalyticAt ℝ A 0 :=
    analyticAt_const.add (analyticAt_id.mul hB)
  have hZ : AnalyticAt ℝ Z 0 := analyticAt_id.mul hA
  have hZ0 : Z 0 = 0 := by simp [Z]
  have hL : AnalyticAt ℝ L 0 := logQuadraticKernel_analytic.comp_of_eq hZ hZ0
  have hB0 : B 0 = (rescaledMean m s e + rescaledFactorialMoment m s 2 e) / 2 :=
    rescaledMGFQuadratic_tilt_zero m s e
  have hB1 : deriv B 0 = rescaledMean m s e / 6 +
      rescaledFactorialMoment m s 2 e / 2 + rescaledFactorialMoment m s 3 e / 6 :=
    (rescaledMGFQuadratic_hasDerivAt_zero m s e).deriv
  have hB2 := rescaledMGFQuadratic_deriv2_zero m s e
  have hA0 : A 0 = rescaledMean m s e := by simp [A, rescaledMGFSlope]
  have hA1 : deriv A 0 = B 0 := by
    have h := (hasDerivAt_const 0 (rescaledMean m s e)).add
      ((hasDerivAt_id 0).mul hB.differentiableAt.hasDerivAt)
    change HasDerivAt A _ 0 at h
    exact h.deriv.trans (by simp)
  have hA2 : iteratedDeriv 2 A 0 = 2 * deriv B 0 := by
    change iteratedDeriv 2 (fun t => rescaledMean m s e + t * B t) 0 = _
    rw [iteratedDeriv_fun_add (f := fun _ : ℝ => rescaledMean m s e)
      (g := fun t : ℝ => t * B t) (by fun_prop) (analyticAt_id.mul hB).contDiffAt,
      iteratedDeriv_const,
      analytic_mul_iteratedDeriv2 (fun t : ℝ => t) B analyticAt_id hB]
    simp [iteratedDeriv_fun_id]
  have hZ1 : deriv Z 0 = rescaledMean m s e := by
    have h := (hasDerivAt_id 0).mul hA.differentiableAt.hasDerivAt
    change HasDerivAt Z _ 0 at h
    rw [h.deriv]
    simp [hA0]
  have hZ2 : iteratedDeriv 2 Z 0 = 2 * B 0 := by
    rw [analytic_mul_iteratedDeriv2 (fun t : ℝ => t) A analyticAt_id hA]
    simp [hA1, iteratedDeriv_fun_id]
  have hL0 : L 0 = -(1 / 2 : ℝ) := by simp [L, hZ0]
  have hL1 : deriv L 0 = rescaledMean m s e / 3 := by
    have h := logQuadraticKernel_hasDerivAt_zero.comp_of_eq 0
      hZ.differentiableAt.hasDerivAt hZ0.symm
    change HasDerivAt L _ 0 at h
    rw [h.deriv, hZ1]
    ring
  have hL2 : iteratedDeriv 2 L 0 =
      -(rescaledMean m s e ^ 2) / 2 + 2 * B 0 / 3 := by
    rw [analytic_comp_iteratedDeriv2_zero Z logQuadraticKernel hZ
      logQuadraticKernel_analytic hZ0, logQuadraticKernel_deriv2_zero,
      logQuadraticKernel_hasDerivAt_zero.deriv, hZ1, hZ2]
    ring
  have hAA : AnalyticAt ℝ (fun t => A t * A t) 0 := hA.mul hA
  have hAA1 : deriv (fun t => A t * A t) 0 = 2 * A 0 * B 0 := by
    have h := hA.differentiableAt.hasDerivAt.mul hA.differentiableAt.hasDerivAt
    change HasDerivAt (fun t => A t * A t) _ 0 at h
    rw [h.deriv, hA1]
    ring
  have heq : rescaledProxyExtension m s e = (fun t => 2 * (B t + (A t * A t) * L t)) := by
    funext t
    dsimp [rescaledProxyExtension, B, A, L, Z]
    ring
  rw [heq, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add (f := B) (g := fun t => (A t * A t) * L t)
      hB.contDiffAt (hAA.mul hL).contDiffAt,
    analytic_mul_iteratedDeriv2 (fun t => A t * A t) L hAA hL,
    analytic_mul_iteratedDeriv2 A A hA hA, hAA1, hA0, hA1, hA2,
    hL0, hL1, hL2, hB0, hB1, hB2]
  dsimp [rescaledFourthCumulantPolynomial]
  ring

end

end ExactHoeffding
