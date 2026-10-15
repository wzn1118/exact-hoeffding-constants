import ExactHoeffding.RealMarginMoments

/-! # Ordinary moments and cumulants of the genuine real-margin law -/

namespace ExactHoeffding

noncomputable section

open Finset

private theorem real_stirling_one (i : ℕ) :
    (i:ℝ)^1 = (Nat.descFactorial i 1:ℝ) := by simp

private theorem real_stirling_two (i : ℕ) :
    (i:ℝ)^2 = (Nat.descFactorial i 2:ℝ)+(Nat.descFactorial i 1:ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring

private theorem real_stirling_three (i : ℕ) :
    (i:ℝ)^3 = (Nat.descFactorial i 3:ℝ)+3*(Nat.descFactorial i 2:ℝ)+
      (Nat.descFactorial i 1:ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring

private theorem real_stirling_four (i : ℕ) :
    (i:ℝ)^4 = (Nat.descFactorial i 4:ℝ)+6*(Nat.descFactorial i 3:ℝ)+
      7*(Nat.descFactorial i 2:ℝ)+(Nat.descFactorial i 1:ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring

/-- Through degree six, the algebraic margin moments are the ordinary
moments of the explicit normalized finite law, including `m<r`. -/
theorem realMarginMass_rawMoment (N m r : ℕ) (d : ℝ) (hr : r ≤ 6)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) :
    finiteRawMoment (range (m+1)) (fun i => (i:ℝ))
      (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) r = marginRawMoment N m r d := by
  have hfac (q : ℕ) := realMarginMass_marginFactorialMoment N m q d hden
  unfold marginRawMoment
  interval_cases r
  · simpa only [finiteRawMoment, pow_zero, one_mul, momentFromFactorials,
      Nat.descFactorial_zero, Nat.cast_one] using hfac 0
  all_goals
    simp only [finiteRawMoment, momentFromFactorials, real_stirling_one,
      real_stirling_two, real_stirling_three, real_stirling_four, stirling_five_real,
      stirling_six_real, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← hfac]

/-- The second cumulant is the actual variance of the real-margin law. -/
theorem realMarginMass_cumulant2 (N m : ℕ) (d : ℝ)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) :
    finiteCumulant2 (range (m+1)) (fun i => (i:ℝ))
      (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) = marginCumulant2 N m d := by
  unfold finiteCumulant2 marginCumulant2
  rw [realMarginMass_rawMoment N m 2 d (by omega) hden,
    realMarginMass_rawMoment N m 1 d (by omega) hden]

/-- The cubic cumulant formula is attached to the actual real-margin law. -/
theorem realMarginMass_cumulant3 (N m : ℕ) (d : ℝ)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) :
    finiteCumulant3 (range (m+1)) (fun i => (i:ℝ))
      (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) = marginCumulant3 N m d := by
  unfold finiteCumulant3 marginCumulant3
  rw [realMarginMass_rawMoment N m 3 d (by omega) hden,
    realMarginMass_rawMoment N m 2 d (by omega) hden,
    realMarginMass_rawMoment N m 1 d (by omega) hden]

/-- The quartic cumulant formula is attached to the actual real-margin law. -/
theorem realMarginMass_cumulant4 (N m : ℕ) (d : ℝ)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) :
    finiteCumulant4 (range (m+1)) (fun i => (i:ℝ))
      (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) = marginCumulant4 N m d := by
  unfold finiteCumulant4 marginCumulant4
  rw [realMarginMass_rawMoment N m 4 d (by omega) hden,
    realMarginMass_rawMoment N m 3 d (by omega) hden,
    realMarginMass_rawMoment N m 2 d (by omega) hden,
    realMarginMass_rawMoment N m 1 d (by omega) hden]

end
end ExactHoeffding
