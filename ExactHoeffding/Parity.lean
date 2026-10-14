import ExactHoeffding.Basic

/-!
# Even and odd variance benchmarks

Exact algebraic identities for the parity dependence of
`4 floor(N²/4)/(N(N-1))`. The upper bound for the sharp Laplace proxy
is a separate analytic theorem, not claimed here.
-/

namespace ExactHoeffding

/-- At an even population size `N = 2j`, the balanced margin product
    is precisely `N²/4`. -/
theorem even_margin_identity (j : ℝ) :
    j * (2 * j - j) = (2 * j) ^ 2 / 4 := by
  ring

/-- For `N = 2j+1`, the nearest-balanced margin product is
    `(N²-1)/4`. -/
theorem odd_margin_identity (j : ℝ) :
    j * ((2 * j + 1) - j) = ((2 * j + 1) ^ 2 - 1) / 4 := by
  ring

/-- Exact even-population formula for the normalized variance. -/
theorem even_variance_formula (j : ℝ) (hj : 1 ≤ j) :
    4 * (j * j) / ((2 * j) * ((2 * j) - 1)) =
      (2 * j) / ((2 * j) - 1) := by
  have hj0 : j ≠ 0 := by linarith
  have hden : (2 * j - 1) ≠ 0 := by linarith
  field_simp
  ring

/-- Exact odd-population formula for the normalized variance. -/
theorem odd_variance_formula (j : ℝ) (hj : 1 ≤ j) :
    4 * (j * (j + 1)) / ((2 * j + 1) * (2 * j)) =
      ((2 * j + 1) + 1) / (2 * j + 1) := by
  have hj0 : j ≠ 0 := by linarith
  have hden : (2 * j + 1) ≠ 0 := by linarith
  field_simp
  ring

end ExactHoeffding
