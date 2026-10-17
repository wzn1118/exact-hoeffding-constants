import ExactHoeffding.FactorialChernoff
import ExactHoeffding.Support

/-!
# Exact factorial and Chernoff values above the true support

All statements concern the original finite hypergeometric law. The actual
Legendre transform and the piecewise KL rate are not extended outside their
proved support domains.
-/

namespace ExactHoeffding
noncomputable section
open Set

/-- Above the true support maximum, every term on the actual sampling range
has zero hypergeometric weight. -/
theorem hypergeomMass_eq_zero_of_supportUpper_lt (N k m i : ℕ)
    (him : i ≤ m) (hi : min k m < i) :
    hypergeomMass N k m i = 0 := by
  have hki : k < i := by omega
  simp [hypergeomMass, hypergeomCount, Nat.choose_eq_zero_of_lt hki]

/-- The actual upper-tail probability vanishes above `min k m`. -/
theorem hypergeomIntegerTailMass_eq_zero_of_supportUpper_lt (N k m d : ℕ)
    (hd : min k m < d) :
    finiteIntegerTailMass (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d = 0 := by
  unfold finiteIntegerTailMass
  apply Finset.sum_eq_zero
  intro i hi
  have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  by_cases hdi : d ≤ i
  · simp only [if_pos hdi]
    exact hypergeomMass_eq_zero_of_supportUpper_lt N k m i him (by omega)
  · simp [hdi]

/-- The highest-degree admissible candidate is zero outside the true support. -/
theorem hypergeomFactorialCandidate_eq_zero_of_supportUpper_lt (N k m d : ℕ)
    (hd : min k m < d) :
    finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d d = 0 := by
  unfold finiteFactorialCandidate finiteBinomialMoment
  have hsum : (∑ i ∈ Finset.range (m + 1),
      (Nat.choose i d : ℝ) * hypergeomMass N k m i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    by_cases hid : i < d
    · simp [Nat.choose_eq_zero_of_lt hid]
    · rw [hypergeomMass_eq_zero_of_supportUpper_lt N k m i him (by omega), mul_zero]
  rw [hsum, zero_div]

/-- The optimized factorial bound is exactly zero outside the true support. -/
theorem hypergeomFactorialBound_eq_zero_of_supportUpper_lt (N k m d : ℕ)
    (hd : min k m < d) :
    finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d = 0 := by
  apply le_antisymm
  · have h := finiteFactorialBound_le_candidate (Finset.range (m + 1))
      (fun i => i) (hypergeomMass N k m) d d le_rfl
    rw [hypergeomFactorialCandidate_eq_zero_of_supportUpper_lt N k m d hd] at h
    exact h
  · unfold finiteFactorialBound
    apply Finset.le_min'
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    exact finiteFactorialCandidate_nonneg _ _ _ _ _
      (fun i hi => hypergeomMass_nonneg N k m i)

/-- Every genuine hypergeometric Chernoff candidate is nonnegative. -/
theorem hypergeomChernoffCandidate_nonneg (N k m d : ℕ) (t : ℝ) :
    0 ≤ Real.exp (-t * (d : ℝ)) * hypergeomMGF N k m t :=
  mul_nonneg (Real.exp_pos _).le (hypergeomMGF_nonneg N k m t)

/-- A nonnegative-tilt candidate is bounded by the exponential of the
positive distance from the upper support endpoint. -/
theorem hypergeomChernoffCandidate_le_supportGap (N k m d : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t * (d : ℝ)) * hypergeomMGF N k m t ≤
      Real.exp (-t * ((d : ℝ) - (min k m : ℕ))) := by
  have hmgf : hypergeomMGF N k m t ≤ Real.exp (t * (min k m : ℕ)) := by
    unfold hypergeomMGF finiteMGF
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1),
          hypergeomMass N k m i * Real.exp (t * (min k m : ℕ)) := by
        apply Finset.sum_le_sum
        intro i hi
        dsimp only
        have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        by_cases hiup : i ≤ min k m
        · apply mul_le_mul_of_nonneg_left _ (hypergeomMass_nonneg N k m i)
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hiup) ht
        · rw [hypergeomMass_eq_zero_of_supportUpper_lt N k m i him (by omega)]
          simp
      _ = Real.exp (t * (min k m : ℕ)) := by
        rw [← Finset.sum_mul, hypergeomMass_total N k m hk hm, one_mul]
  calc
    _ ≤ Real.exp (-t * (d : ℝ)) * Real.exp (t * (min k m : ℕ)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Above the true support, arbitrarily small nonnegative-tilt Chernoff
candidates exist, also for degenerate legal hypergeometric laws. -/
theorem hypergeomChernoffCandidate_arbitrarily_small_of_supportUpper_lt
    (N k m d : ℕ) (hk : k ≤ N) (hm : m ≤ N) (hd : min k m < d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧
      Real.exp (-t * (d : ℝ)) * hypergeomMGF N k m t < ε := by
  let gap : ℝ := (d : ℝ) - (min k m : ℕ)
  have hgap : 0 < gap := by
    dsimp [gap]
    exact sub_pos.mpr (by exact_mod_cast hd)
  let t : ℝ := (|Real.log ε| + 1) / gap
  have ht : 0 ≤ t := div_nonneg (by positivity) hgap.le
  refine ⟨t, ht, (hypergeomChernoffCandidate_le_supportGap N k m d hk hm t ht).trans_lt ?_⟩
  have hexponent : -t * gap = -|Real.log ε| - 1 := by
    dsimp [t]
    field_simp [hgap.ne']
    ring
  change Real.exp (-t * gap) < ε
  rw [hexponent]
  have hlog : -|Real.log ε| - 1 < Real.log ε := by
    linarith [neg_abs_le (Real.log ε)]
  calc
    _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr hlog
    _ = ε := Real.exp_log hε

/-- The exact positive-tilt Chernoff infimum is zero above the support. -/
theorem hypergeomChernoffInf_eq_zero_of_supportUpper_lt
    (N k m d : ℕ) (hk : k ≤ N) (hm : m ≤ N) (hd : min k m < d) :
    sInf (finiteChernoffSet (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d) = 0 := by
  let S := finiteChernoffSet (Finset.range (m + 1)) (fun i => i)
    (hypergeomMass N k m) d
  have hnon : ∀ y ∈ S, 0 ≤ y := by
    rintro y ⟨t, ht, rfl⟩
    exact hypergeomChernoffCandidate_nonneg N k m d t
  have hne : S.Nonempty := by
    refine ⟨Real.exp (-(0 : ℝ) * (d : ℝ)) * hypergeomMGF N k m 0, ?_⟩
    exact ⟨0, le_rfl, rfl⟩
  have hbdd : BddBelow S := ⟨0, hnon⟩
  change sInf S = 0
  have hge : 0 ≤ sInf S := le_csInf hne hnon
  apply le_antisymm _ hge
  by_contra hnle
  have hpos : 0 < sInf S := lt_of_not_ge hnle
  obtain ⟨t, ht, hsmall⟩ :=
    hypergeomChernoffCandidate_arbitrarily_small_of_supportUpper_lt
      N k m d hk hm hd (sInf S) hpos
  have hmem : Real.exp (-t * (d : ℝ)) * hypergeomMGF N k m t ∈ S :=
    ⟨t, ht, rfl⟩
  exact (not_lt_of_ge (csInf_le hbdd hmem)) hsmall

/-- All three actual upper-tail bounds coincide at zero above true support. -/
theorem hypergeom_factorial_chernoff_support_exterior_end_to_end
    (N k m d : ℕ) (hk : k ≤ N) (hm : m ≤ N) (hd : min k m < d) :
    finiteIntegerTailMass (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d = 0 ∧
      finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d = 0 ∧
      sInf (finiteChernoffSet (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d) = 0 :=
  ⟨hypergeomIntegerTailMass_eq_zero_of_supportUpper_lt N k m d hd,
    hypergeomFactorialBound_eq_zero_of_supportUpper_lt N k m d hd,
    hypergeomChernoffInf_eq_zero_of_supportUpper_lt N k m d hk hm hd⟩

end
end ExactHoeffding
