import ExactHoeffding.RescaledVarianceSecond

/-!
# Actual derivative inputs for third-order inverse-population optimization

These are derivatives of the existing analytic hypergeometric continuation,
not postulated coefficients of an optimizer. They are intermediate inputs;
this module does not claim a third- or fourth-order optimized expansion.
-/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

/-- The two inverse-population derivatives of the actual first tilt
derivative. No integer-population limit is substituted for differentiation. -/
theorem rescaledProxyExtension_tilt_deriv_zero_deriv2 (m : ℕ) (s : ℝ) :
    iteratedDeriv 2 (fun e => deriv (rescaledProxyExtension m s e) 0) 0 =
      (m : ℝ) * s * (1 - (m : ℝ)) / 2 := by
  let H : ℝ → ℝ := fun e => (m : ℝ) * s *
    (3 - 3 * (m : ℝ) + (2 * (m : ℝ) ^ 2 - s ^ 2 - 2) * e +
      3 * (m : ℝ) * s ^ 2 * e ^ 2 - 2 * (m : ℝ) ^ 2 * s ^ 2 * e ^ 3) /
        (12 * (1 - e) * (1 - 2 * e))
  have hH : AnalyticAt ℝ H 0 := by dsimp [H]; fun_prop (disch := norm_num)
  have heq : (fun e => deriv (rescaledProxyExtension m s e) 0) =ᶠ[𝓝 0]
      (fun e => (m : ℝ) * s / 12 * e + e ^ 2 * H e) := by
    have h1 : ∀ᶠ e in 𝓝 (0 : ℝ), 1 - e ≠ 0 :=
      (continuous_const.sub continuous_id).continuousAt.eventually_ne (by norm_num)
    have h2 : ∀ᶠ e in 𝓝 (0 : ℝ), 1 - 2 * e ≠ 0 :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne
        (by norm_num)
    filter_upwards [h1, h2] with e he1 he2
    rw [rescaledProxyExtension_deriv_tilt_zero m s e he1 he2]
    dsimp [H]
    field_simp [he1, he2, show 1 - e * 2 ≠ 0 by simpa only [mul_comm] using he2]
    ring
  rw [heq.iteratedDeriv_eq]
  rw [iteratedDeriv_fun_add (f := fun e : ℝ => (m : ℝ) * s / 12 * e)
    (g := fun e : ℝ => e ^ 2 * H e) (by fun_prop)
    (by exact ((by fun_prop : AnalyticAt ℝ (fun e : ℝ => e ^ 2 * H e) 0)).contDiffAt),
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_id,
    iteratedDeriv2_quadratic_factor H hH]
  norm_num [H]
  ring

/-- The cubic coefficient of the actual variance slice before optimizing. -/
theorem rescaledProxyExtension_zero_tilt_deriv3 (m : ℕ) (s : ℝ) :
    iteratedDeriv 3 (fun e => rescaledProxyExtension m s e 0) 0 =
      3 * (m : ℝ) * (1 - (m : ℝ)) * (1 - s ^ 2) / 2 := by
  let H : ℝ → ℝ := fun e =>
    (m : ℝ) * (1 - (m : ℝ)) * (1 - s ^ 2) / (4 * (1 - e))
  have hH : AnalyticAt ℝ H 0 := by dsimp [H]; fun_prop (disch := norm_num)
  have heq : (fun e => rescaledProxyExtension m s e 0) =ᶠ[𝓝 0]
      (fun e => (m : ℝ) / 4 + (m : ℝ) * (1 - (m : ℝ)) / 4 * e +
        (m : ℝ) * (1 - (m : ℝ) - s ^ 2) / 4 * e ^ 2 + e ^ 3 * H e) := by
    filter_upwards [(continuous_const.sub continuous_id).continuousAt.eventually_ne
      (by norm_num : (1 : ℝ) - 0 ≠ 0)] with e he
    change 1 - e ≠ 0 at he
    rw [rescaledProxyExtension_zero_tilt_formula m s e he]
    dsimp [H]
    field_simp [he]
    ring
  have hfactor : iteratedDeriv 3 (fun e => e ^ 3 * H e) 0 = 6 * H 0 := by
    rw [iteratedDeriv_fun_mul (by fun_prop) hH.contDiffAt]
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, Nat.choose]
  rw [heq.iteratedDeriv_eq]
  rw [iteratedDeriv_fun_add
    (f := fun e : ℝ => (m : ℝ) / 4 + (m : ℝ) * (1 - (m : ℝ)) / 4 * e +
      (m : ℝ) * (1 - (m : ℝ) - s ^ 2) / 4 * e ^ 2)
    (g := fun e : ℝ => e ^ 3 * H e) (by fun_prop)
    (by exact ((by fun_prop : AnalyticAt ℝ (fun e : ℝ => e ^ 3 * H e) 0)).contDiffAt),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_const, iteratedDeriv_const_mul_field, iteratedDeriv_fun_id,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, hfactor]
  norm_num [H]
  ring

/-- The limiting proxy is genuinely even, including its removable value. -/
theorem rescaledProxyExtension_limit_even (m : ℕ) (s t : ℝ) :
    rescaledProxyExtension m s 0 (-t) = rescaledProxyExtension m s 0 t := by
  by_cases ht : t = 0
  · simp [ht]
  · rw [rescaledProxyExtension_limit_formula m s (-t) (neg_ne_zero.mpr ht),
      rescaledProxyExtension_limit_formula m s t ht]
    simp only [neg_div, Real.cosh_neg, neg_sq]

/-- In particular the third tilt derivative vanishes at the balanced limit. -/
theorem rescaledProxyExtension_limit_deriv3 (m : ℕ) (s : ℝ) :
    iteratedDeriv 3 (rescaledProxyExtension m s 0) 0 = 0 := by
  have heq : (fun t => rescaledProxyExtension m s 0 (-t)) =
      rescaledProxyExtension m s 0 := funext (rescaledProxyExtension_limit_even m s)
  have h := iteratedDeriv_comp_neg 3 (rescaledProxyExtension m s 0) 0
  rw [heq] at h
  norm_num at h
  linarith

end

end ExactHoeffding
