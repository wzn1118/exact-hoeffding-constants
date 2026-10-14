import ExactHoeffding.Normalization

/-!
# First factorial moment of a hypergeometric sampling count

A weighted Vandermonde identity is proved uniformly in both population
margins and the sample size. No finite-case enumeration is used.
-/

namespace ExactHoeffding

/-- The unnormalized first moment of the hypergeometric counting law.
Here the population has `k+1` marked and `h` unmarked elements and
`m+1` elements are sampled. The identity is valid even when the
sample size exceeds the population (both sides are then zero). -/
theorem hypergeomCount_first_moment_succ (k h m : ℕ) :
    (∑ i ∈ Finset.range (m + 2),
      i * (Nat.choose (k + 1) i *
        Nat.choose h (m + 1 - i))) =
    (k + 1) * Nat.choose (k + h) m := by
  have hv :
      (∑ i ∈ Finset.range (m + 1),
        Nat.choose k i * Nat.choose h (m - i)) =
        Nat.choose (k + h) m := by
    simpa [hypergeomCount] using
      (hypergeomCount_total (k + h) k m (by omega))
  calc
    (∑ i ∈ Finset.range (m + 2),
        i * (Nat.choose (k + 1) i *
          Nat.choose h (m + 1 - i))) =
        ∑ i ∈ Finset.range (m + 1),
          (k + 1) * (Nat.choose k i * Nat.choose h (m - i)) := by
      rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ']
      simp only [Nat.zero_mul, add_zero]
      apply Finset.sum_congr rfl
      intro i hi
      have hsub : m + 1 - (i + 1) = m - i := by omega
      rw [hsub]
      have hc : (i + 1) * Nat.choose (k + 1) (i + 1) =
          (k + 1) * Nat.choose k i := by
        calc
          _ = Nat.choose (k + 1) (i + 1) * (i + 1) := by ac_rfl
          _ = (k + 1) * Nat.choose k i :=
            (Nat.add_one_mul_choose_eq k i).symm
      calc
        (i + 1) * (Nat.choose (k + 1) (i + 1) *
          Nat.choose h (m - i)) =
          ((i + 1) * Nat.choose (k + 1) (i + 1)) *
            Nat.choose h (m - i) := by ac_rfl
        _ = ((k + 1) * Nat.choose k i) * Nat.choose h (m - i) := by rw [hc]
        _ = (k + 1) * (Nat.choose k i * Nat.choose h (m - i)) := by ac_rfl
    _ = (k + 1) * Nat.choose (k + h) m := by
      rw [← Finset.mul_sum, hv]

end ExactHoeffding
