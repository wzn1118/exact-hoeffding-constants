import ExactHoeffding.RescaledOptimumLeading

/-! # The actual zero-tilt variance continuation through second order -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem iteratedDeriv2_quadratic_factor (g : ℝ → ℝ) (hg : AnalyticAt ℝ g 0) :
    iteratedDeriv 2 (fun e => e ^ 2 * g e) 0 = 2 * g 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hg.contDiffAt]
  norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, Nat.choose]

theorem rescaledProxyExtension_zero_tilt_deriv2 (m : ℕ) (s : ℝ) :
    iteratedDeriv 2 (fun e => rescaledProxyExtension m s e 0) 0 =
      (m : ℝ) * (1 - (m : ℝ) - s ^ 2) / 2 := by
  let G : ℝ → ℝ := fun e =>
    (m : ℝ) * (1 - (m : ℝ) - s ^ 2 + (m : ℝ) * s ^ 2 * e) / (4 * (1 - e))
  have hG : AnalyticAt ℝ G 0 := by dsimp [G]; fun_prop (disch := norm_num)
  have heq : (fun e => rescaledProxyExtension m s e 0) =ᶠ[𝓝 0]
      (fun e => (m : ℝ) / 4 + (m : ℝ) * (1 - (m : ℝ)) / 4 * e + e ^ 2 * G e) := by
    filter_upwards [((continuous_const.sub continuous_id).continuousAt.eventually_ne
      (by norm_num : (1 : ℝ) - 0 ≠ 0))] with e he
    change 1 - e ≠ 0 at he
    rw [rescaledProxyExtension_zero_tilt_formula m s e he]
    dsimp [G]
    field_simp [he]
    ring
  rw [heq.iteratedDeriv_eq]
  rw [iteratedDeriv_fun_add (by fun_prop) ((by fun_prop :
    AnalyticAt ℝ (fun e : ℝ => e ^ 2 * G e) 0).contDiffAt)]
  rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_const, iteratedDeriv_const_mul_field, iteratedDeriv_fun_id,
    iteratedDeriv2_quadratic_factor G hG]
  norm_num [G]
  ring

end

end ExactHoeffding
