import ExactHoeffding.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Exact finite subset exponential-sum algebra

The integer degree convention makes every out-of-range degree zero. This
allows insertion and three-coordinate splitting without natural truncation.
-/

namespace ExactHoeffding

noncomputable def sliceExponential {α : Type*} [DecidableEq α]
    (T : Finset α) (y : α → ℝ) (k : ℤ) : ℝ :=
  ∑ S ∈ T.powerset, if (S.card : ℤ) = k then Real.exp (∑ i ∈ S, y i) else 0

theorem sliceExponential_nonneg {α : Type*} [DecidableEq α]
    (T : Finset α) (y : α → ℝ) (k : ℤ) : 0 ≤ sliceExponential T y k := by
  unfold sliceExponential
  apply Finset.sum_nonneg
  intro S hS
  split_ifs <;> positivity

theorem sliceExponential_nat {α : Type*} [DecidableEq α]
    (T : Finset α) (y : α → ℝ) (k : ℕ) :
    sliceExponential T y k = ∑ S ∈ T.powersetCard k, Real.exp (∑ i ∈ S, y i) := by
  unfold sliceExponential
  simp only [Int.natCast_inj]
  rw [← Finset.sum_filter, ← Finset.powersetCard_eq_filter]

theorem sliceExponential_pos {α : Type*} [DecidableEq α]
    (T : Finset α) (y : α → ℝ) (k : ℕ) (hk : k ≤ T.card) :
    0 < sliceExponential T y k := by
  rw [sliceExponential_nat]
  exact Finset.sum_pos (fun S hS => Real.exp_pos _) (Finset.powersetCard_nonempty.mpr hk)

/-- Inserting one coordinate gives the exact elementary-symmetric recurrence. -/
theorem sliceExponential_insert {α : Type*} [DecidableEq α]
    (T : Finset α) (y : α → ℝ) (k : ℤ) (j : α) (hj : j ∉ T) :
    sliceExponential (insert j T) y k =
      sliceExponential T y k + Real.exp (y j) * sliceExponential T y (k - 1) := by
  unfold sliceExponential
  rw [Finset.sum_powerset_insert hj]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hjS : j ∉ S := fun h => hj ((Finset.mem_powerset.mp hS) h)
  rw [Finset.card_insert_of_notMem hjS, Finset.sum_insert hjS]
  push_cast
  have hiff : (S.card : ℤ) + 1 = k ↔ (S.card : ℤ) = k - 1 := by omega
  simp only [hiff]
  split_ifs <;> simp [Real.exp_add]

/-- Three inserted coordinates separate into zero-, one-, two-, and three-hit contributions. -/
theorem sliceExponential_three_insert {α : Type*} [DecidableEq α]
    (T : Finset α) (y : α → ℝ) (k : ℤ) (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∉ T) (hb : b ∉ T) (hc : c ∉ T) :
    sliceExponential (insert a (insert b (insert c T))) y k =
      sliceExponential T y k +
      sliceExponential T y (k - 1) * (Real.exp (y a) + Real.exp (y b) + Real.exp (y c)) +
      sliceExponential T y (k - 2) *
        (Real.exp (y a) * Real.exp (y b) + Real.exp (y a) * Real.exp (y c) +
          Real.exp (y b) * Real.exp (y c)) +
      sliceExponential T y (k - 3) * Real.exp (y a) * Real.exp (y b) * Real.exp (y c) := by
  have ha' : a ∉ insert b (insert c T) := by simp [hab, hac, ha]
  have hb' : b ∉ insert c T := by simp [hbc, hb]
  rw [sliceExponential_insert _ _ _ _ ha']
  simp_rw [sliceExponential_insert _ _ _ _ hb', sliceExponential_insert _ _ _ _ hc]
  have h₂ : k - 1 - 1 = k - 2 := by omega
  have h₃ : k - 2 - 1 = k - 3 := by omega
  simp only [h₂, h₃]
  ring

theorem sliceExponential_congr {α : Type*} [DecidableEq α]
    (T : Finset α) (y v : α → ℝ) (k : ℤ) (h : ∀ i ∈ T, y i = v i) :
    sliceExponential T y k = sliceExponential T v k := by
  unfold sliceExponential
  apply Finset.sum_congr rfl
  intro S hS
  congr 2
  exact Finset.sum_congr rfl (fun i hi => h i ((Finset.mem_powerset.mp hS) hi))

theorem sliceExponential_two_coefficients_pos {α : Type*} [DecidableEq α]
    (T : Finset α) (y : α → ℝ) (k : ℕ) (hk0 : 0 < k) (hk : k ≤ T.card + 2) (s : ℝ) :
    0 < sliceExponential T y ((k : ℤ) - 1) + Real.exp s * sliceExponential T y ((k : ℤ) - 2) := by
  have hA := sliceExponential_nonneg T y ((k : ℤ) - 1)
  have hB := sliceExponential_nonneg T y ((k : ℤ) - 2)
  by_cases hsmall : k ≤ T.card + 1
  · have hc : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    have hp := sliceExponential_pos T y (k - 1) (by omega)
    rw [hc] at hp
    exact add_pos_of_pos_of_nonneg hp (mul_nonneg (Real.exp_pos s).le hB)
  · have hc : (k : ℤ) - 2 = (T.card : ℤ) := by omega
    have hp := sliceExponential_pos T y T.card le_rfl
    rw [hc]
    exact add_pos_of_nonneg_of_pos hA (mul_pos (Real.exp_pos s) hp)

end ExactHoeffding
