import ExactHoeffding.RealMarginMasses
import ExactHoeffding.ExactImbalanceAlgebra

/-! # Exact factorial moments of the positive real-margin law -/

namespace ExactHoeffding

noncomputable section

open Finset

/-- Splitting a falling product at an arbitrary index. -/
theorem scaledFalling_add_degree (a e : ℝ) (q r : ℕ) :
    scaledFalling a e (q+r) = scaledFalling a e q *
      scaledFalling (a-(q:ℝ)*e) e r := by
  unfold scaledFalling
  rw [Finset.prod_range_add]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  push_cast
  ring

private theorem realMarginNumerator_factorial_shift (m q : ℕ) (a b e : ℝ) :
    (∑ i ∈ range (m+2), (Nat.descFactorial i (q+1):ℝ) *
      ((m+1).choose i:ℝ)*scaledFalling a e i*scaledFalling b e (m+1-i)) =
    ((m:ℝ)+1)*a*(∑ i ∈ range (m+1), (Nat.descFactorial i q:ℝ)*
      (m.choose i:ℝ)*scaledFalling (a-e) e i*scaledFalling b e (m-i)) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.zero_descFactorial_succ, Nat.cast_zero, zero_mul, add_zero,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hs : m+1-(i+1) = m-i := by omega
  rw [hs, Nat.succ_descFactorial_succ, Nat.cast_mul, scaledFalling_succ_left]
  have hc : ((i:ℝ)+1)*((m+1).choose (i+1):ℝ) =
      ((m:ℝ)+1)*(m.choose i:ℝ) := by
    have h := congrArg (fun n:ℕ => (n:ℝ)) (Nat.add_one_mul_choose_eq m i)
    push_cast at h
    nlinarith
  push_cast
  calc
    _ = (((i:ℝ)+1)*((m+1).choose (i+1):ℝ))*
      ((Nat.descFactorial i q:ℝ)*a*scaledFalling (a-e) e i*scaledFalling b e (m-i)) := by ring
    _ = _ := by rw [hc]; ring

/-- All factorial moments before division by the common denominator. -/
theorem realMarginNumerator_factorial (m q : ℕ) (a b e : ℝ) :
    (∑ i ∈ range (m+1), (Nat.descFactorial i q:ℝ) *
      (m.choose i:ℝ)*scaledFalling a e i*scaledFalling b e (m-i)) =
    if q ≤ m then (Nat.descFactorial m q:ℝ)*scaledFalling a e q*
      scaledFalling (a+b-(q:ℝ)*e) e (m-q) else 0 := by
  induction q generalizing m a with
  | zero =>
      simp only [Nat.descFactorial_zero, Nat.cast_one, one_mul, Nat.zero_le,
        ↓reduceIte, scaledFalling_zero, mul_one, Nat.cast_zero, zero_mul,
        sub_zero, Nat.sub_zero]
      simpa only [mul_assoc] using (scaledFalling_add a b e m).symm
  | succ q ih =>
      by_cases hqm : q+1 ≤ m
      · cases m with
        | zero => omega
        | succ m =>
          have hq : q ≤ m := by omega
          rw [realMarginNumerator_factorial_shift, ih, if_pos hq, if_pos hqm,
            Nat.succ_descFactorial_succ, Nat.cast_mul, scaledFalling_succ_left]
          have hs : m+1-(q+1) = m-q := by omega
          have ha : a-e+b-(q:ℝ)*e = a+b-((q+1:ℕ):ℝ)*e := by push_cast; ring
          rw [hs, ha]
          push_cast
          ring
      · rw [if_neg hqm]
        apply Finset.sum_eq_zero
        intro i hi
        have hiq : i < q+1 := by have := Finset.mem_range.mp hi; omega
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hiq]
        simp

/-- The exact factorial-moment formula comes from the actual normalized
masses, for every degree within the finite support. -/
theorem realMarginMass_factorialMoment (m q : ℕ) (e p : ℝ)
    (hqm : q ≤ m) (hden : scaledFalling 1 e m ≠ 0) :
    (∑ i ∈ range (m+1), (Nat.descFactorial i q:ℝ)*realMarginMass m e p i) =
      (Nat.descFactorial m q:ℝ)*scaledFalling p e q / scaledFalling 1 e q := by
  have hsplit : scaledFalling 1 e m = scaledFalling 1 e q*
      scaledFalling (1-(q:ℝ)*e) e (m-q) := by
    simpa only [Nat.add_sub_of_le hqm] using scaledFalling_add_degree 1 e q (m-q)
  have hleft : scaledFalling 1 e q ≠ 0 := by
    intro hz
    rw [hsplit, hz, zero_mul] at hden
    exact hden rfl
  have hright : scaledFalling (1-(q:ℝ)*e) e (m-q) ≠ 0 := by
    intro hz
    rw [hsplit, hz, mul_zero] at hden
    exact hden rfl
  unfold realMarginMass
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  simp only [← mul_assoc]
  rw [realMarginNumerator_factorial, if_pos hqm]
  rw [show p+(1-p)-(q:ℝ)*e = 1-(q:ℝ)*e by ring, hsplit]
  field_simp

/-- An order above the support is zero on both the real law and its
falling-factorial expression. -/
theorem realMarginMass_factorialMoment_all (m q : ℕ) (e p : ℝ)
    (hden : scaledFalling 1 e m ≠ 0) :
    (∑ i ∈ range (m+1), (Nat.descFactorial i q:ℝ)*realMarginMass m e p i) =
      (Nat.descFactorial m q:ℝ)*scaledFalling p e q / scaledFalling 1 e q := by
  by_cases hqm : q ≤ m
  · exact realMarginMass_factorialMoment m q e p hqm hden
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : m < q)]
    simp only [Nat.cast_zero, zero_mul, zero_div]
    apply Finset.sum_eq_zero
    intro i hi
    have hiq : i < q := by have := Finset.mem_range.mp hi; omega
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hiq]
    simp

/-- The formal factorial expressions in the imbalance calculation are
therefore factorial moments of the genuine real-margin probability law. -/
theorem realMarginMass_marginFactorialMoment (N m q : ℕ) (d : ℝ)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) :
    (∑ i ∈ range (m+1), (Nat.descFactorial i q:ℝ)*
      realMarginMass m (1/(N:ℝ)) ((1-d)/2) i) = marginFactorialMoment N m q d := by
  rw [realMarginMass_factorialMoment_all m q _ _ hden]
  unfold marginFactorialMoment scaledFalling
  rw [Finset.prod_div_distrib]
  simp only [div_eq_mul_inv, mul_one, mul_comm, mul_left_comm]

end
end ExactHoeffding
