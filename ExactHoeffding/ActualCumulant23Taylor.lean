import ExactHoeffding.Cumulant23Taylor
import ExactHoeffding.RealMarginMoments

/-!
# The second- and third-cumulant expansions for the actual real-margin law

The analytic continuation is identified with the finite law made from the
real-margin masses.  Along each fixed-imbalance curve this law is a strictly
positive normalized law in a neighborhood of the binomial limit.
-/

open Filter
open scoped Topology

namespace ExactHoeffding

noncomputable section

private theorem c23_stirling_one (i : ℕ) :
    (i : ℝ) ^ 1 = (Nat.descFactorial i 1 : ℝ) := by simp

private theorem c23_stirling_two (i : ℕ) :
    (i : ℝ) ^ 2 = (Nat.descFactorial i 2 : ℝ) +
      (Nat.descFactorial i 1 : ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring

private theorem c23_stirling_three (i : ℕ) :
    (i : ℝ) ^ 3 = (Nat.descFactorial i 3 : ℝ) +
      3 * (Nat.descFactorial i 2 : ℝ) + (Nat.descFactorial i 1 : ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring


private theorem c23_stirling_four (i : ℕ) :
    (i : ℝ) ^ 4 = (Nat.descFactorial i 4 : ℝ) +
      6 * (Nat.descFactorial i 3 : ℝ) + 7 * (Nat.descFactorial i 2 : ℝ) +
      (Nat.descFactorial i 1 : ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring

/-- The factorial moments of the normalized real-margin law equal the
continued hypergeometric factorial moments at every parameter where the law is
normalized. -/
theorem realMarginMass_rescaledFactorialMoment (m q : ℕ) (s e : ℝ)
    (hden : scaledFalling 1 e m ≠ 0) :
    (∑ i ∈ Finset.range (m + 1), (Nat.descFactorial i q : ℝ) *
      realMarginMass m e ((1 - s * e) / 2) i) =
      hypergeomRescaledFactorial m q s e := by
  rw [realMarginMass_factorialMoment_all m q e ((1 - s * e) / 2) hden]
  unfold hypergeomRescaledFactorial scaledFalling
  rw [Finset.prod_div_distrib]
  simp only [div_eq_mul_inv, mul_comm, mul_left_comm]

/-- Ordinary moments of the actual real-margin law agree with the continued
moments through degree six, including sample sizes below the moment degree. -/
theorem realMarginMass_rescaledMoment (m r : ℕ) (s e : ℝ) (hr : r ≤ 6)
    (hden : scaledFalling 1 e m ≠ 0) :
    finiteRawMoment (Finset.range (m + 1)) (fun i => (i : ℝ))
      (realMarginMass m e ((1 - s * e) / 2)) r =
      hypergeomRescaledMoment m r s e := by
  have hfac (q : ℕ) := realMarginMass_rescaledFactorialMoment m q s e hden
  unfold hypergeomRescaledMoment
  interval_cases r
  · simpa only [finiteRawMoment, momentFromFactorials, Nat.descFactorial_zero,
      Nat.cast_one, pow_zero, one_mul] using hfac 0
  all_goals
    simp only [finiteRawMoment, momentFromFactorials, c23_stirling_one,
      c23_stirling_two, c23_stirling_three, c23_stirling_four, stirling_five_real,
      stirling_six_real, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← hfac]

/-- The actual normalized real-margin variance is the inverse-population
continuation. -/
theorem realMarginMass_cumulant2_rescaled (m : ℕ) (s e : ℝ)
    (hden : scaledFalling 1 e m ≠ 0) :
    finiteCumulant2 (Finset.range (m + 1)) (fun i => (i : ℝ))
      (realMarginMass m e ((1 - s * e) / 2)) =
      hypergeomRescaledCumulant2 m s e := by
  unfold finiteCumulant2 hypergeomRescaledCumulant2
  rw [realMarginMass_rescaledMoment m 2 s e (by omega) hden,
    realMarginMass_rescaledMoment m 1 s e (by omega) hden]

/-- The actual normalized real-margin third cumulant is the
inverse-population continuation. -/
theorem realMarginMass_cumulant3_rescaled (m : ℕ) (s e : ℝ)
    (hden : scaledFalling 1 e m ≠ 0) :
    finiteCumulant3 (Finset.range (m + 1)) (fun i => (i : ℝ))
      (realMarginMass m e ((1 - s * e) / 2)) =
      hypergeomRescaledCumulant3 m s e := by
  unfold finiteCumulant3 hypergeomRescaledCumulant3
  rw [realMarginMass_rescaledMoment m 3 s e (by omega) hden,
    realMarginMass_rescaledMoment m 2 s e (by omega) hden,
    realMarginMass_rescaledMoment m 1 s e (by omega) hden]

/-- The real-margin mass denominator remains nonzero near the binomial limit. -/
theorem realMarginMass_denominator_near_zero (m : ℕ) :
    ∀ᶠ e : ℝ in 𝓝 0, scaledFalling 1 e m ≠ 0 := by
  have hc : ContinuousAt (fun e : ℝ => scaledFalling 1 e m) 0 := by
    unfold scaledFalling
    fun_prop
  exact hc.eventually_ne (by simp [scaledFalling])

/-- Along every fixed-imbalance curve, the real-margin masses form a strictly
positive normalized finite law near the binomial limit. -/
theorem realMarginMass_balanced_curve_eventually_probability (m : ℕ) (s : ℝ) :
    ∀ᶠ e : ℝ in 𝓝 0,
      scaledFalling 1 e m ≠ 0 ∧
      (∀ i ∈ Finset.range (m + 1),
        0 < realMarginMass m e ((1 - s * e) / 2) i) ∧
      (∑ i ∈ Finset.range (m + 1), realMarginMass m e ((1 - s * e) / 2) i = 1) := by
  have hden := realMarginMass_denominator_near_zero m
  have hmass : ∀ᶠ e : ℝ in 𝓝 0,
      ∀ i ∈ Finset.range (m + 1),
        0 < realMarginMass m e ((1 - s * e) / 2) i := by
    apply (Finset.range (m + 1)).eventually_all.mpr
    intro i hi
    have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have ha : AnalyticAt ℝ
        (fun e : ℝ => realMarginMass m e ((1 - s * e) / 2) i) 0 := by
      have hm : AnalyticAt ℝ (fun e : ℝ => (e, (1 - s * e) / 2)) 0 :=
        analyticAt_id.prod ((analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).div_const)
      exact (realMarginMass_joint_analytic m i (0, 1 / 2) (by simp)
        ).comp_of_eq hm (by simp)
    have hzero : 0 < realMarginMass m 0 (1 / 2) i := by
      apply realMarginMass_pos m 0 (1 / 2) (by intro j hj; norm_num)
        (by intro j hj; norm_num) (by simp [scaledFalling]) i him
    have hzero' : 0 < realMarginMass m 0 ((1 - s * 0) / 2) i := by simpa using hzero
    exact continuousAt_const.eventually_lt ha.continuousAt hzero'
  filter_upwards [hden, hmass] with e hd hm
  exact ⟨hd, hm, realMarginMass_sum m e ((1 - s * e) / 2) hd⟩

/-- The variance expansion holds for the actual real-margin law. -/
theorem realMarginMass_cumulant2_balanced_expansion (m : ℕ) (s : ℝ) :
    (fun e => finiteCumulant2 (Finset.range (m + 1)) (fun i => (i : ℝ))
      (realMarginMass m e ((1 - s * e) / 2)) - hypergeomCumulant2Taylor m s e)
      =O[𝓝 0] (fun e : ℝ => e ^ 5) := by
  have h := hypergeom_rescaled_cumulant2_remainder m s
  refine h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [realMarginMass_denominator_near_zero m] with e hden
  exact congrArg (fun x : ℝ => x - hypergeomCumulant2Taylor m s e)
    (realMarginMass_cumulant2_rescaled m s e hden).symm

/-- The cubic-cumulant expansion holds for the actual real-margin law. -/
theorem realMarginMass_cumulant3_balanced_expansion (m : ℕ) (s : ℝ) :
    (fun e => finiteCumulant3 (Finset.range (m + 1)) (fun i => (i : ℝ))
      (realMarginMass m e ((1 - s * e) / 2)) - hypergeomCumulant3Taylor m s e)
      =O[𝓝 0] (fun e : ℝ => e ^ 4) := by
  have h := hypergeom_rescaled_cumulant3_remainder m s
  refine h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [realMarginMass_denominator_near_zero m] with e hden
  exact congrArg (fun x : ℝ => x - hypergeomCumulant3Taylor m s e)
    (realMarginMass_cumulant3_rescaled m s e hden).symm

end
end ExactHoeffding
