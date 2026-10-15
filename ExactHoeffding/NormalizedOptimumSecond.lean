import ExactHoeffding.RescaledOptimumSecond

/-! # The exact second coefficient of the actual normalized optimum -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

private theorem iteratedDeriv2_mul_affine (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0)
    (a b : ℝ) :
    iteratedDeriv 2 (fun e => f e * (a + b * e)) 0 =
      a * iteratedDeriv 2 f 0 + 2 * b * deriv f 0 := by
  have heq : (fun e => f e * (a + b * e)) =
      (fun e => a * f e + b * (e * f e)) := by funext e; ring
  rw [heq, iteratedDeriv_fun_add
    (f := fun e : ℝ => a * f e) (g := fun e : ℝ => b * (e * f e))
    (analyticAt_const.mul hf).contDiffAt
    ((analyticAt_const.mul (analyticAt_id.mul hf)).contDiffAt),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id, iteratedDeriv_one, Nat.choose]
  ring

theorem rescaledProxyExtension_normalized_optimum_deriv2
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0) (hdτ : deriv τ 0 = 4 * s) :
    iteratedDeriv 2 (fun e =>
      4 * rescaledProxyExtension m s e (τ e) / ((m : ℝ) * (1 - (m : ℝ) * e))) 0 =
      2 * (1 - s ^ 2 / 3) := by
  let V : ℝ → ℝ := fun e => rescaledProxyExtension m s e (τ e)
  let R : ℝ → ℝ := fun e => 4 * V e / ((m : ℝ) * (1 - (m : ℝ) * e))
  have hV : AnalyticAt ℝ V 0 :=
    rescaledProxyExtension_optimized_value_analytic m s τ hτ hτzero
  have hR : AnalyticAt ℝ R 0 :=
    rescaledProxyExtension_normalized_optimum_analytic m hm s τ hτ hτzero
  have hRd : deriv R 0 = 1 :=
    (rescaledProxyExtension_normalized_optimum_hasDerivAt m hm s τ hτ hτzero).deriv
  have hVdd : iteratedDeriv 2 V 0 = (m : ℝ) * (1 - (m : ℝ) - s ^ 2 / 3) / 2 :=
    rescaledProxyExtension_optimized_value_deriv2 m hm s τ hτ hτzero hdτ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heq : (fun e => R e * ((m : ℝ) + (-(m : ℝ) ^ 2) * e)) =ᶠ[𝓝 0]
      (fun e => 4 * V e) := by
    have hne : ∀ᶠ e in 𝓝 (0 : ℝ), (m : ℝ) * (1 - (m : ℝ) * e) ≠ 0 :=
      ((continuous_const.mul (continuous_const.sub
        (continuous_const.mul continuous_id))).continuousAt.eventually_ne (by simpa using hmR.ne'))
    filter_upwards [hne] with e he
    change (m : ℝ) * (1 - (m : ℝ) * e) ≠ 0 at he
    dsimp [R]
    rw [show (m : ℝ) + (-(m : ℝ) ^ 2) * e =
      (m : ℝ) * (1 - (m : ℝ) * e) by ring]
    exact div_mul_cancel₀ _ he
  have hdd := heq.iteratedDeriv_eq 2
  rw [iteratedDeriv2_mul_affine R hR, iteratedDeriv_const_mul_field,
    hRd, hVdd] at hdd
  change iteratedDeriv 2 R 0 = _
  nlinarith

end

end ExactHoeffding
