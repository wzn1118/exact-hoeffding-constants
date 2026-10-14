import ExactHoeffding.FactorialMoments

/-!
# Normalized hypergeometric first moment

Here a combinatorial factorial-moment identity is combined with binomial
recurrences to obtain an exact expectation formula for sampling without
replacement. No asymptotic approximation is used.
-/

namespace ExactHoeffding

/-- For any `k+1` marked and `h` unmarked elements, sampling `m+1`
elements has exact hypergeometric expectation `(m+1)*(k+1)/(k+h+1)`. -/
theorem hypergeom_mean_succ (k h m : ℕ)
    (hm : m + 1 ≤ k + h + 1) :
    (∑ i ∈ Finset.range (m + 2),
      (i : ℝ) * hypergeomMass (k + h + 1) (k + 1) (m + 1) i) =
      ((m + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) /
        ((k + h + 1 : ℕ) : ℝ) := by
  have hsub : k + h + 1 - (k + 1) = h := by omega
  have hcnt :
      (∑ i ∈ Finset.range (m + 2),
        (i : ℝ) * (hypergeomCount (k + h + 1) (k + 1) (m + 1) i : ℝ)) =
      ((k + 1 : ℕ) : ℝ) * (Nat.choose (k + h) m : ℝ) := by
    simp only [hypergeomCount, hsub, Nat.cast_mul]
    exact_mod_cast hypergeomCount_first_moment_succ k h m
  have hden : (Nat.choose (k + h + 1) (m + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero hm)
  have hN : ((k + h + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hrec :
      ((k + h + 1 : ℕ) : ℝ) * (Nat.choose (k + h) m : ℝ) =
        (Nat.choose (k + h + 1) (m + 1) : ℝ) *
          ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq (k + h) m)
  calc
    (∑ i ∈ Finset.range (m + 2),
      (i : ℝ) * hypergeomMass (k + h + 1) (k + 1) (m + 1) i) =
        (∑ i ∈ Finset.range (m + 2),
          (i : ℝ) * (hypergeomCount (k + h + 1) (k + 1) (m + 1) i : ℝ)) /
            (Nat.choose (k + h + 1) (m + 1) : ℝ) := by
      simp only [hypergeomMass]
      rw [← Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ((k + 1 : ℕ) : ℝ) * (Nat.choose (k + h) m : ℝ) /
        (Nat.choose (k + h + 1) (m + 1) : ℝ) := by rw [hcnt]
    _ = ((m + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) /
        ((k + h + 1 : ℕ) : ℝ) := by
      field_simp [hden, hN]
      nlinarith [congrArg (fun x : ℝ => ((k + 1 : ℕ) : ℝ) * x) hrec]

end ExactHoeffding
