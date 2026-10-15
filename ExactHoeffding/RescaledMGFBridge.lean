import ExactHoeffding.RescaledFactorialFamily
import Mathlib.Data.Nat.Choose.Sum

/-! # Identification of the inverse-population MGF with the actual law -/

namespace ExactHoeffding

noncomputable section

private theorem cast_descFactorial_div_factorial (i q : ℕ) :
    (Nat.descFactorial i q : ℝ) / (Nat.factorial q : ℝ) = (Nat.choose i q : ℝ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hq : (Nat.factorial q : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  field_simp

/-- The factorial basis reconstructs the actual PGF, not just its derivatives. -/
theorem hypergeom_factorial_PGF (N k m : ℕ) (z : ℝ) :
    (∑ q ∈ Finset.range (m + 1),
      hypergeomFactorialMoment N k m q / (Nat.factorial q : ℝ) * z ^ q) =
    ∑ i ∈ Finset.range (m + 1), hypergeomMass N k m i * (1 + z) ^ i := by
  simp only [hypergeomFactorialMoment]
  simp_rw [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    (∑ q ∈ Finset.range (m + 1),
        ((Nat.descFactorial i q : ℝ) * hypergeomMass N k m i) /
          (Nat.factorial q : ℝ) * z ^ q) =
        hypergeomMass N k m i *
          ∑ q ∈ Finset.range (m + 1), (Nat.choose i q : ℝ) * z ^ q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [mul_div_right_comm, cast_descFactorial_div_factorial]
      ring
    _ = hypergeomMass N k m i *
          ∑ q ∈ Finset.range (i + 1), (Nat.choose i q : ℝ) * z ^ q := by
      congr 1
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ him))
      intro q hqm hqi
      have hiq : i < q := by
        have : ¬ q < i + 1 := by simpa only [Finset.mem_range] using hqi
        omega
      simp [Nat.choose_eq_zero_of_lt hiq]
    _ = _ := by
      congr 1
      rw [add_comm 1 z, add_pow]
      apply Finset.sum_congr rfl
      intro q hq
      simp [mul_comm]

theorem hypergeomMGF_factorial_basis (N k m : ℕ) (t : ℝ) :
    hypergeomMGF N k m t =
      ∑ q ∈ Finset.range (m + 1),
        hypergeomFactorialMoment N k m q / (Nat.factorial q : ℝ) *
          (Real.exp t - 1) ^ q := by
  rw [hypergeom_factorial_PGF]
  unfold hypergeomMGF finiteMGF
  apply Finset.sum_congr rfl
  intro i hi
  rw [add_sub_cancel, ← Real.exp_nat_mul]
  simp [mul_comm]

/-- Exact finite-MGF equality along the admissible inverse-population sequence. -/
theorem rescaledMGF_hypergeom (N k m : ℕ) (s t : ℝ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N)
    (hbalance : 2 * (k : ℝ) + s = (N : ℝ)) :
    rescaledMGF m s (1 / (N : ℝ)) t = hypergeomMGF N k m t := by
  rw [rescaledMGF, hypergeomMGF_factorial_basis]
  apply Finset.sum_congr rfl
  intro q hq
  rw [rescaledFactorialMoment_hypergeom N k m q s hN hk hm
    ((Nat.le_of_lt_succ (Finset.mem_range.mp hq)).trans hm) hbalance]

theorem rescaledMGF_at_zero (m : ℕ) (s t : ℝ) :
    rescaledMGF m s 0 t = ((1 + Real.exp t) / 2) ^ m := by
  unfold rescaledMGF
  simp_rw [rescaledFactorialMoment_at_zero, mul_div_right_comm,
    cast_descFactorial_div_factorial]
  have hsum := add_pow ((Real.exp t - 1) / 2) (1 : ℝ) m
  have hbase : (Real.exp t - 1) / 2 + 1 = (1 + Real.exp t) / 2 := by ring
  rw [hbase] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [one_pow, mul_one, div_pow]
  ring

end

end ExactHoeffding
