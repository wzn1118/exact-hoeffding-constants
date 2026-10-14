import ExactHoeffding.Basic
import Mathlib.Data.Nat.Choose.Cast

/-!
# The hypergeometric weight model

These are the finite weights used in the paper (Equation (hypergeom)).
At this stage the model records the combinatorial coefficients and proves
some exact algebraic facts; its global normalization and variance theorem are
tracked as open formalization targets in `LEAN_PROOF_STATUS.md`.
-/

namespace ExactHoeffding

/-- Integer-valued, unnormalized hypergeometric mass. -/
def hypergeomCount (N k m i : ℕ) : ℕ :=
  Nat.choose k i * Nat.choose (N - k) (m - i)

/-- A real-valued hypergeometric mass with the usual combinatorial denominator.
    Correct normalization requires `k ≤ N` and `m ≤ N`. -/
noncomputable def hypergeomMass (N k m i : ℕ) : ℝ :=
  (hypergeomCount N k m i : ℝ) / (Nat.choose N m : ℝ)

/-- Every hypergeometric mass is nonnegative (also for degenerate parameters). -/
theorem hypergeomMass_nonneg (N k m i : ℕ) :
    0 ≤ hypergeomMass N k m i := by
  unfold hypergeomMass
  positivity

/-- The unnormalized mass at zero draws is `1`. -/
theorem hypergeomCount_no_draws (N k : ℕ) :
    hypergeomCount N k 0 0 = 1 := by
  simp [hypergeomCount]

/-- Sampling zero elements gives a unit probability mass at zero. -/
theorem hypergeomMass_no_draws (N k : ℕ) :
    hypergeomMass N k 0 0 = 1 := by
  simp [hypergeomMass, hypergeomCount]

/-- A coefficient formula for the hypergeometric probability generating
    polynomial (without its global normalization). -/
def hypergeomPolynomial (N k m : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (hypergeomCount N k m i : ℝ) * z ^ i

end ExactHoeffding
