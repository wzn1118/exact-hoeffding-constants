import ExactHoeffding.RescaledProxyAnalytic
import Mathlib.Data.Nat.Factorial.Cast
import Mathlib.Analysis.Complex.Trigonometric

/-! # The removable value and limiting proxy of the rescaled family -/

namespace ExactHoeffding

noncomputable section

open scoped Topology

private theorem rescaledMGFQuadratic_zero (m : ℕ) (s : ℝ) :
    rescaledMGFQuadratic m s 0 0 =
      (m : ℝ) * ((m : ℝ) + 1) / 8 := by
  unfold rescaledMGFQuadratic
  rw [expQuadraticKernel_at_zero, expSlopeKernel_zero]
  have htail :
      (∑ j ∈ Finset.range (m - 1),
        rescaledFactorialMoment m s (j + 2) 0 /
            (Nat.factorial (j + 2) : ℝ) * 0 ^ j *
          expSlopeKernel 0 ^ (j + 2)) =
        (Nat.descFactorial m 2 : ℝ) / 8 := by
    by_cases hm2 : 2 ≤ m
    · rw [Finset.sum_eq_single 0]
      · simp [rescaledFactorialMoment_at_zero]
        norm_num
        ring
      · intro j hj hj0
        simp [hj0]
      · intro hnot
        exfalso
        apply hnot
        have hpos : 0 < m - 1 := by omega
        exact Finset.mem_range.mpr hpos
    · have hm1 : m - 1 = 0 := by omega
      simp [hm1]
  have htail' :
      (∑ j ∈ Finset.range (m - 1),
        rescaledFactorialMoment m s (j + 2) 0 /
            (Nat.factorial (j + 2) : ℝ) * 0 ^ j * 1 ^ (j + 2)) =
        (Nat.descFactorial m 2 : ℝ) / 8 := by
    simpa only [expSlopeKernel_zero, one_pow] using htail
  rw [htail']
  simp [rescaledMean, Nat.cast_descFactorial_two]
  by_cases hm0 : m = 0
  · simp [hm0]
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    rw [Nat.cast_sub hm1]
    ring

theorem rescaledProxyExtension_at_zero (m : ℕ) (s : ℝ) :
    rescaledProxyExtension m s 0 0 = (m : ℝ) / 4 := by
  unfold rescaledProxyExtension rescaledMGFSlope
  rw [rescaledMGFQuadratic_zero]
  simp only [zero_mul, mul_zero, zero_add, add_zero]
  rw [logQuadraticKernel_zero]
  simp [rescaledMean]
  ring

private theorem rescaled_limit_log_identity (m : ℕ) (s : ℝ) (t : ℝ) :
    Real.log (rescaledMGF m s 0 t) - rescaledMean m s 0 * t =
      (m : ℝ) * Real.log (Real.cosh (t / 2)) := by
  rw [rescaledMGF_at_zero]
  have hbase : 0 < (1 + Real.exp t) / 2 := by positivity
  have hcosh : 0 < Real.cosh (t / 2) := Real.cosh_pos _
  have hfactor :
      (1 + Real.exp t) / 2 = Real.exp (t / 2) * Real.cosh (t / 2) := by
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp [ne_of_gt (Real.exp_pos (t / 2))]
    rw [pow_two, ← Real.exp_add]
    rw [show t / 2 + t / 2 = t by ring]
    ring
  rw [rescaledMean, Real.log_pow]
  rw [hfactor, Real.log_mul (ne_of_gt (Real.exp_pos _)) hcosh.ne',
    Real.log_exp]
  ring

theorem rescaledProxyExtension_limit_formula (m : ℕ) (s t : ℝ) (ht : t ≠ 0) :
    rescaledProxyExtension m s 0 t =
      2 * (m : ℝ) * Real.log (Real.cosh (t / 2)) / t ^ 2 := by
  by_cases hm0 : m = 0
  · subst m
    simp [rescaledProxyExtension, rescaledMGFQuadratic, rescaledMGFSlope,
      rescaledMean]
  · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    rw [rescaledProxyExtension_eq_quotient m hm s 0 t ht]
    rw [rescaled_limit_log_identity m s t]
    ring

end

end ExactHoeffding
