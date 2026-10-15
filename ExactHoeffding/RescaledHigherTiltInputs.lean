import ExactHoeffding.FactorialMGFDerivatives

/-! # Higher tilt derivatives of the actual rescaled removable proxy

The fifth and sixth log-MGF derivatives are identified with the factorial
moment cumulant polynomials. Dividing out the removable quadratic factor
then gives the third and fourth tilt derivatives of the actual proxy.
-/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem analytic_log_deriv6_polynomial (f : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) (hf0 : f 0 = 1) :
    iteratedDeriv 6 (fun t => Real.log (f t)) 0 =
      cumulant6Polynomial (iteratedDeriv 1 f 0) (iteratedDeriv 2 f 0)
        (iteratedDeriv 3 f 0) (iteratedDeriv 4 f 0) (iteratedDeriv 5 f 0)
        (iteratedDeriv 6 f 0) := by
  let L : ℝ → ℝ := fun t => Real.log (f t)
  have h0 := analytic_log_derivative_recursion f hf hf0 0
  have h1 := analytic_log_derivative_recursion f hf hf0 1
  have h2 := analytic_log_derivative_recursion f hf hf0 2
  have h3 := analytic_log_derivative_recursion f hf hf0 3
  have h5 := analytic_log_derivative_recursion f hf hf0 5
  norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_zero, hf0]
    at h0 h1 h2 h3 h5
  have hk1 : deriv L 0 = deriv f 0 := h0.symm
  change iteratedDeriv 2 f 0 = iteratedDeriv 2 L 0 + deriv f 0 * deriv L 0 at h1
  change iteratedDeriv 3 f 0 = iteratedDeriv 3 L 0 +
    2 * deriv f 0 * iteratedDeriv 2 L 0 + iteratedDeriv 2 f 0 * deriv L 0 at h2
  change iteratedDeriv 4 f 0 = iteratedDeriv 4 L 0 +
    3 * deriv f 0 * iteratedDeriv 3 L 0 + 3 * iteratedDeriv 2 f 0 * iteratedDeriv 2 L 0 +
      iteratedDeriv 3 f 0 * deriv L 0 at h3
  change iteratedDeriv 6 f 0 = iteratedDeriv 6 L 0 +
    5 * deriv f 0 * iteratedDeriv 5 L 0 + 10 * iteratedDeriv 2 f 0 * iteratedDeriv 4 L 0 +
      10 * iteratedDeriv 3 f 0 * iteratedDeriv 3 L 0 +
      5 * iteratedDeriv 4 f 0 * iteratedDeriv 2 L 0 +
      iteratedDeriv 5 f 0 * deriv L 0 at h5
  rw [hk1] at h1 h2 h3 h5
  have hk2 : iteratedDeriv 2 L 0 = iteratedDeriv 2 f 0 - deriv f 0 ^ 2 := by
    nlinarith
  have hk3 : iteratedDeriv 3 L 0 = iteratedDeriv 3 f 0 -
      3 * iteratedDeriv 2 f 0 * deriv f 0 + 2 * deriv f 0 ^ 3 := by
    rw [hk2] at h2
    nlinarith [h2]
  have hk4 : iteratedDeriv 4 L 0 = iteratedDeriv 4 f 0 -
      4 * iteratedDeriv 3 f 0 * deriv f 0 - 3 * iteratedDeriv 2 f 0 ^ 2 +
      12 * iteratedDeriv 2 f 0 * deriv f 0 ^ 2 - 6 * deriv f 0 ^ 4 := by
    rw [hk2, hk3] at h3
    nlinarith [h3]
  have hk5 := analytic_log_deriv5_polynomial f hf hf0
  change iteratedDeriv 5 L 0 = _ at hk5
  rw [hk2, hk3, hk4, hk5] at h5
  simp only [iteratedDeriv_one] at h5 ⊢
  dsimp [cumulant5Polynomial, cumulant6Polynomial] at h5 ⊢
  nlinarith [h5]

theorem rescaledMGF_tilt_analytic (m : ℕ) (s e t : ℝ) :
    AnalyticAt ℝ (rescaledMGF m s e) t := by
  unfold rescaledMGF
  apply Finset.analyticAt_fun_sum
  intro q hq
  exact analyticAt_const.mul ((analyticAt_rexp.sub analyticAt_const).pow q)

theorem rescaledProxyExtension_tilt_analytic (m : ℕ) (s e : ℝ) :
    AnalyticAt ℝ (rescaledProxyExtension m s e) 0 := by
  have hB : AnalyticAt ℝ (rescaledMGFQuadratic m s e) 0 := by
    unfold rescaledMGFQuadratic
    apply AnalyticAt.add (analyticAt_const.mul expQuadraticKernel_analytic)
    apply Finset.analyticAt_fun_sum
    intro j hj
    exact (analyticAt_const.mul (analyticAt_id.pow j)).mul
      (expSlopeKernel_analytic.pow (j + 2))
  have hA : AnalyticAt ℝ (rescaledMGFSlope m s e) 0 :=
    analyticAt_const.add (analyticAt_id.mul hB)
  unfold rescaledProxyExtension
  apply AnalyticAt.mul analyticAt_const
  apply hB.add
  exact (hA.pow 2).mul (logQuadraticKernel_analytic.comp_of_eq
    (analyticAt_id.mul hA) (by simp))

theorem rescaledMGF_log_deriv5_zero (m : ℕ) (s e : ℝ) :
    iteratedDeriv 5 (fun t => Real.log (rescaledMGF m s e t)) 0 =
      hypergeomRescaledCumulant5 m s e := by
  rw [analytic_log_deriv5_polynomial _ (rescaledMGF_tilt_analytic m s e 0)
    (rescaledMGF_tilt_zero m s e)]
  simp only [rescaledMGF_iteratedDeriv_zero_through_six m 1 s e (by omega),
    rescaledMGF_iteratedDeriv_zero_through_six m 2 s e (by omega),
    rescaledMGF_iteratedDeriv_zero_through_six m 3 s e (by omega),
    rescaledMGF_iteratedDeriv_zero_through_six m 4 s e (by omega),
    rescaledMGF_iteratedDeriv_zero_through_six m 5 s e (by omega),
    hypergeomRescaledCumulant5]

theorem rescaledMGF_log_deriv6_zero (m : ℕ) (s e : ℝ) :
    iteratedDeriv 6 (fun t => Real.log (rescaledMGF m s e t)) 0 =
      hypergeomRescaledCumulant6 m s e := by
  rw [analytic_log_deriv6_polynomial _ (rescaledMGF_tilt_analytic m s e 0)
    (rescaledMGF_tilt_zero m s e)]
  simp only [rescaledMGF_iteratedDeriv_zero_through_six m 1 s e (by omega),
    rescaledMGF_iteratedDeriv_zero_through_six m 2 s e (by omega),
    rescaledMGF_iteratedDeriv_zero_through_six m 3 s e (by omega),
    rescaledMGF_iteratedDeriv_zero_through_six m 4 s e (by omega),
    rescaledMGF_iteratedDeriv_zero_through_six m 5 s e (by omega),
    rescaledMGF_iteratedDeriv_zero_through_six m 6 s e (by omega),
    hypergeomRescaledCumulant6]

private theorem rescaled_logMGF_factor_deriv (m : ℕ) (hm : 1 ≤ m)
    (s e : ℝ) (n : ℕ) (hn : n = 5 ∨ n = 6) :
    iteratedDeriv n (fun t => Real.log (rescaledMGF m s e t)) 0 =
      (Nat.choose n 2 : ℝ) * iteratedDeriv (n - 2) (rescaledProxyExtension m s e) 0 := by
  have hL : AnalyticAt ℝ (fun t => Real.log (rescaledMGF m s e t)) 0 :=
    (rescaledMGF_tilt_analytic m s e 0).log (by simp)
  have hQ := rescaledProxyExtension_tilt_analytic m s e
  have heq : (fun t => Real.log (rescaledMGF m s e t) - rescaledMean m s e * t) =
      (fun t => t ^ 2 * rescaledProxyExtension m s e t / 2) :=
    funext (rescaled_logMGF_quadratic_factor m hm s e)
  have h := congrArg (fun f : ℝ → ℝ => iteratedDeriv n f 0) heq
  rw [iteratedDeriv_fun_sub hL.contDiffAt (by fun_prop),
    iteratedDeriv_const_mul_field] at h
  have hrhs : (fun t => t ^ 2 * rescaledProxyExtension m s e t / 2) =
      (fun t => (1 / 2 : ℝ) * (t ^ 2 * rescaledProxyExtension m s e t)) := by
    funext t; ring
  rw [hrhs, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul (by fun_prop) hQ.contDiffAt] at h
  rcases hn with rfl | rfl <;>
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero,
      iteratedDeriv_fun_id, Nat.choose] at h ⊢ <;> linarith

theorem rescaledProxyExtension_deriv3_tilt_zero (m : ℕ) (hm : 1 ≤ m) (s e : ℝ) :
    iteratedDeriv 3 (rescaledProxyExtension m s e) 0 =
      hypergeomRescaledCumulant5 m s e / 10 := by
  have h := rescaled_logMGF_factor_deriv m hm s e 5 (Or.inl rfl)
  rw [rescaledMGF_log_deriv5_zero] at h
  norm_num [Nat.choose] at h
  linarith

theorem rescaledProxyExtension_deriv4_tilt_zero (m : ℕ) (hm : 1 ≤ m) (s e : ℝ) :
    iteratedDeriv 4 (rescaledProxyExtension m s e) 0 =
      hypergeomRescaledCumulant6 m s e / 15 := by
  have h := rescaled_logMGF_factor_deriv m hm s e 6 (Or.inr rfl)
  rw [rescaledMGF_log_deriv6_zero] at h
  norm_num [Nat.choose] at h
  linarith

theorem rescaledProxyExtension_tilt_deriv3_zero_hasDerivAt (m : ℕ) (hm : 1 ≤ m)
    (s : ℝ) :
    HasDerivAt (fun e => iteratedDeriv 3 (rescaledProxyExtension m s e) 0)
      (-(m : ℝ) * s / 20) 0 := by
  have heq : (fun e => iteratedDeriv 3 (rescaledProxyExtension m s e) 0) =
      (fun e => hypergeomRescaledCumulant5 m s e / 10) :=
    funext (rescaledProxyExtension_deriv3_tilt_zero m hm s)
  rw [heq]
  apply ((hypergeom_rescaled_cumulant5_hasDerivAt_zero m s).div_const 10).congr_deriv
  ring

theorem rescaledProxyExtension_limit_deriv4 (m : ℕ) (hm : 1 ≤ m) (s : ℝ) :
    iteratedDeriv 4 (rescaledProxyExtension m s 0) 0 = (m : ℝ) / 60 := by
  rw [rescaledProxyExtension_deriv4_tilt_zero m hm,
    hypergeom_rescaled_cumulant6_at_zero]
  ring

end

end ExactHoeffding
