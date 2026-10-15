import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

/-!
# Basic algebra for finite-population concentration

The proven statements in this file correspond to the elementary quadratic
identities used in the variance and curvature portions of the manuscript.
All identities use real arithmetic; no probabilistic assumptions are hidden.
-/

namespace ExactHoeffding

/-- The elementary finite-population quadratic envelope. -/
theorem balance_product_bound (N x : ℝ) :
    x * (N - x) ≤ N ^ 2 / 4 := by
  nlinarith [sq_nonneg (x - N / 2)]

/-- A balanced population saturates the quadratic envelope. -/
theorem balance_product_eq (N : ℝ) :
    (N / 2) * (N - N / 2) = N ^ 2 / 4 := by
  ring

/-- The two margin products appearing in the curvature theorem both obey
    the same elementary upper bound. -/
theorem min_margin_product_bound (N k m : ℝ) :
    min (k * (N - k)) (m * (N - m)) ≤ N ^ 2 / 4 := by
  exact le_trans (min_le_left ..) (balance_product_bound N k)

/-- The Bernoulli variance is at most `1/4` for every real parameter. -/
theorem bernoulli_variance_bound (p : ℝ) : p * (1 - p) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (p - 1 / 2)]

/-- Bernoulli variance attains the envelope at a balanced parameter. -/
theorem bernoulli_variance_half :
    (1 / 2 : ℝ) * (1 - 1 / 2) = 1 / 4 := by
  norm_num

/-- An exact algebraic form of the centered variance identity. -/
theorem centered_quadratic_identity (x μ : ℝ) :
    (x - μ) ^ 2 = x ^ 2 - 2 * μ * x + μ ^ 2 := by
  ring

/-- Algebraic form of the finite-population correction in dimension `N`. -/
theorem centered_singleton_norm (N : ℝ) (hN : N ≠ 0) :
    (1 - 1 / N) ^ 2 + (N - 1) * (1 / N) ^ 2 = (N - 1) / N := by
  field_simp
  ring

end ExactHoeffding
