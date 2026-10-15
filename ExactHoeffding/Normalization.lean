import ExactHoeffding.Hypergeometric
import ExactHoeffding.Laplace
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Algebra.BigOperators.Field

/-!
# Vandermonde normalization of the hypergeometric distribution

This module proves that the probability masses used in the manuscript really
sum to one, for all finite populations and valid sample parameters. The
argument is the finite Vandermonde identity, not numerical enumeration.
-/

namespace ExactHoeffding

/-- The total number of sample/marked-element configurations is `N.choose m`.
This is the exact Vandermonde identity underlying equation (hypergeom). -/
theorem hypergeomCount_total (N k m : ℕ) (hk : k ≤ N) :
    (∑ i ∈ Finset.range (m + 1), hypergeomCount N k m i) =
      Nat.choose N m := by
  have h₁ :=
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j : ℕ => Nat.choose k i * Nat.choose (N - k) j) m).symm
  have h₂ := (Nat.add_choose_eq k (N - k) m).symm
  simpa [hypergeomCount, Nat.add_sub_of_le hk] using h₁.trans h₂

/-- The hypergeometric mass has total probability one. -/
theorem hypergeomMass_total (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) :
    ∑ i ∈ Finset.range (m + 1), hypergeomMass N k m i = 1 := by
  have hchoose : (Nat.choose N m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hm
  have hcount :
      (∑ i ∈ Finset.range (m + 1), (hypergeomCount N k m i : ℝ)) =
        (Nat.choose N m : ℝ) := by
    exact_mod_cast hypergeomCount_total N k m hk
  simp only [hypergeomMass, ← Finset.sum_div, hcount, div_self hchoose]

/-- The normalized finite Laplace transform of the hypergeometric law. -/
noncomputable def hypergeomMGF (N k m : ℕ) (t : ℝ) : ℝ :=
  finiteMGF (Finset.range (m + 1)) (hypergeomMass N k m)
    (fun i => (i : ℝ)) t

/-- A hypergeometric exponential moment equals one at zero tilt. -/
theorem hypergeomMGF_zero (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomMGF N k m 0 = 1 := by
  exact finiteMGF_zero_of_normalized (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (hypergeomMass_total N k m hk hm)

/-- The (uncentered) hypergeometric exponential moment is nonnegative. -/
theorem hypergeomMGF_nonneg (N k m : ℕ) (t : ℝ) :
    0 ≤ hypergeomMGF N k m t := by
  exact finiteMGF_nonneg (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ)) t
    (fun i hi => hypergeomMass_nonneg N k m i)

/-- The exact one-draw success probability, as an identity of real masses. -/
theorem hypergeomMass_one_success (N k : ℕ) :
    hypergeomMass N k 1 1 = (k : ℝ) / N := by
  simp [hypergeomMass, hypergeomCount]

/-- The exact one-draw failure probability, retaining natural subtraction. -/
theorem hypergeomMass_one_failure (N k : ℕ) :
    hypergeomMass N k 1 0 = ((N - k : ℕ) : ℝ) / N := by
  simp [hypergeomMass, hypergeomCount]

/-- A one-draw hypergeometric law is a Bernoulli law. -/
theorem hypergeomMass_one_failure_complement (N k : ℕ)
    (hk : k ≤ N) (hN : 0 < N) :
    hypergeomMass N k 1 0 = 1 - (k : ℝ) / N := by
  rw [hypergeomMass_one_failure, Nat.cast_sub hk]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp <;> ring

end ExactHoeffding
