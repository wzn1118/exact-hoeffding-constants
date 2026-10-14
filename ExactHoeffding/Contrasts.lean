import ExactHoeffding.Basic

/-!
# Zero-sum contrasts

These lemmas formalize the elementary linear-algebra identities used when
passing from arbitrary weights to centered contrasts. They do not assume
independence of the coordinates.
-/

namespace ExactHoeffding

/-- The centered version of a contrast vector. -/
def centerContrast {n : ℕ} (a : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a i - (∑ j : Fin n, a j) / n

/-- Centering does not alter pairwise differences of coefficients. -/
theorem centerContrast_difference {n : ℕ} (a : Fin n → ℝ) (i j : Fin n) :
    centerContrast a i - centerContrast a j = a i - a j := by
  unfold centerContrast
  ring

/-- If the original coefficients sum to zero, centering acts trivially. -/
theorem centerContrast_fixed {n : ℕ} (a : Fin n → ℝ)
    (ha : ∑ i : Fin n, a i = 0) : centerContrast a = a := by
  funext i
  simp [centerContrast, ha]

end ExactHoeffding
