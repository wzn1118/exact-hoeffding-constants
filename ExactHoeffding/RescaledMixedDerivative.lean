import ExactHoeffding.RescaledTiltCoefficient

/-! # The actual inverse-population / tilt mixed derivative -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

private theorem cast_descFactorial_three_all (m : ℕ) :
    (Nat.descFactorial m 3 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
  rw [show 3 = 2 + 1 by rfl, Nat.descFactorial_succ, Nat.cast_mul,
    Nat.cast_descFactorial_two]
  by_cases hm : 2 ≤ m
  · rw [Nat.cast_sub hm]
    norm_num
    ring
  · interval_cases m <;> norm_num

/-- Exact rational formula for the actual removable proxy's first tilt
derivative, valid away from the factorial-family denominator poles. -/
theorem rescaledProxyExtension_deriv_tilt_zero (m : ℕ) (s e : ℝ)
    (h1 : 1 - e ≠ 0) (h2 : 1 - 2 * e ≠ 0) :
    deriv (rescaledProxyExtension m s e) 0 =
      (m : ℝ) * s * e * (1 - s ^ 2 * e ^ 2) * (1 - (m : ℝ) * e) *
        (1 - 2 * (m : ℝ) * e) / (12 * (1 - e) * (1 - 2 * e)) := by
  rw [(rescaledProxyExtension_hasDerivAt_tilt_zero m s e).deriv]
  simp only [rescaledMean, rescaledFactorialMoment, rescaledPopulationDenom,
    scaledFalling_succ, scaledFalling_zero, Nat.cast_descFactorial_two,
    cast_descFactorial_three_all]
  norm_num
  field_simp [h1, h2, show 1 - e * 2 ≠ 0 by simpa only [mul_comm] using h2]
  ring

theorem rescaledProxyExtension_mixed_hasDerivAt (m : ℕ) (s : ℝ) :
    HasDerivAt (fun e => deriv (rescaledProxyExtension m s e) 0)
      ((m : ℝ) * s / 12) 0 := by
  let G : ℝ → ℝ := fun e =>
    (m : ℝ) * s * (1 - s ^ 2 * e ^ 2) * (1 - (m : ℝ) * e) *
      (1 - 2 * (m : ℝ) * e) / (12 * (1 - e) * (1 - 2 * e))
  have hG : AnalyticAt ℝ G 0 := by
    dsimp [G]
    fun_prop (disch := norm_num)
  have hd := (hasDerivAt_id (0 : ℝ)).mul hG.differentiableAt.hasDerivAt
  have hd' : HasDerivAt (fun e => e * G e) ((m : ℝ) * s / 12) 0 := by
    apply hd.congr_deriv
    simp [G]
  apply hd'.congr_of_eventuallyEq
  have h1 : ∀ᶠ e in 𝓝 (0 : ℝ), 1 - e ≠ 0 := by
    exact ((continuous_const.sub continuous_id).continuousAt.eventually_ne
      (by norm_num : (1 : ℝ) - 0 ≠ 0))
  have h2 : ∀ᶠ e in 𝓝 (0 : ℝ), 1 - 2 * e ≠ 0 := by
    exact ((continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne
      (by norm_num : (1 : ℝ) - 2 * 0 ≠ 0))
  filter_upwards [h1, h2] with e he1 he2
  rw [rescaledProxyExtension_deriv_tilt_zero m s e he1 he2]
  dsimp [G]
  ring

end

end ExactHoeffding
