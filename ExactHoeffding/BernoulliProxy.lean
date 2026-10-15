import ExactHoeffding.BernoulliKL
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Bernoulli quadratic proxy: the balanced case

The general sharp coefficient requires the two-contact-point argument from
the manuscript.  This file first closes the balanced case without assuming
that argument: the centered Bernoulli log-MGF becomes `log (cosh (t/2))`, and
Mathlib's kernel-checked `cosh_le_exp_half_sq` supplies the global quadratic
bound.  The equality-at-zero statement is kept explicit.
-/

namespace ExactHoeffding

theorem bernoulli_half_mgf_factorization (t : ℝ) :
    bernoulliMGF (1 / 2 : ℝ) t =
      Real.exp (t / 2) * Real.cosh (t / 2) := by
  unfold bernoulliMGF
  rw [Real.cosh_eq]
  rw [Real.exp_neg]
  have ht : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [ht]
  field_simp [Real.exp_ne_zero]
  ring

theorem bernoulli_half_centered_log_mgf_eq_log_cosh (t : ℝ) :
    bernoulliCenteredLogMGF (1 / 2 : ℝ) t =
      Real.log (Real.cosh (t / 2)) := by
  rw [bernoulliCenteredLogMGF, bernoulli_half_mgf_factorization,
    Real.log_mul (Real.exp_pos (t / 2)).ne' (Real.cosh_pos _).ne',
    Real.log_exp]
  ring

/-- Balanced Bernoulli has the global Hoeffding quadratic bound with coefficient
`1/4`, proved through the exact centered `log cosh` representation. -/
theorem bernoulli_half_quadratic_bound (t : ℝ) :
    bernoulliCenteredLogMGF (1 / 2 : ℝ) t ≤ (1 / 4 : ℝ) * t ^ 2 / 2 := by
  rw [bernoulli_half_centered_log_mgf_eq_log_cosh]
  have hcosh := Real.cosh_le_exp_half_sq (t / 2)
  have hlog := Real.log_le_log (Real.cosh_pos (t / 2)) hcosh
  rw [Real.log_exp] at hlog
  nlinarith

theorem bernoulli_half_quadratic_bound_at_zero :
    bernoulliCenteredLogMGF (1 / 2 : ℝ) 0 =
      (1 / 4 : ℝ) * (0 : ℝ) ^ 2 / 2 := by
  simp [bernoulliCenteredLogMGF, bernoulliMGF]

end ExactHoeffding
