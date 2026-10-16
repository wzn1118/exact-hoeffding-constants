import ExactHoeffding.PiecewiseKLFull
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Integer thresholds and two-sided tails for the actual hypergeometric law

These results convert the real-threshold, finite-mass piecewise-KL bounds to
integer-valued upper and lower events.  The ceiling and floor are the exact
thresholds; events beyond the true support have mass zero.
-/

namespace ExactHoeffding
noncomputable section

/-- Actual upper-deviation probability mass on the finite hypergeometric law. -/
def hypergeomUpperDeviationMass (N k m : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1),
    if x ≤ (i : ℝ) - (m : ℝ) * k / N then hypergeomMass N k m i else 0

/-- Actual lower-deviation probability mass on the finite hypergeometric law. -/
def hypergeomLowerDeviationMass (N k m : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1),
    if x ≤ (m : ℝ) * k / N - (i : ℝ) then hypergeomMass N k m i else 0

/-- Actual two-sided deviation probability mass on the finite hypergeometric law. -/
def hypergeomTwoSidedDeviationMass (N k m : ℕ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1),
    if x ≤ |(i : ℝ) - (m : ℝ) * k / N| then hypergeomMass N k m i else 0

private lemma upper_deviation_indicator_ceil (μ x : ℝ) (i : ℕ) :
    (x ≤ (i : ℝ) - μ) ↔ Int.ceil (μ + x) ≤ (i : ℤ) := by
  rw [Int.ceil_le]
  constructor <;> intro h <;> norm_cast at h ⊢ <;> linarith

private lemma lower_deviation_indicator_floor (μ x : ℝ) (i : ℕ) :
    (x ≤ μ - (i : ℝ)) ↔ (i : ℤ) ≤ Int.floor (μ - x) := by
  rw [Int.le_floor]
  constructor <;> intro h <;> norm_cast at h ⊢ <;> linarith

/-- The integer upper-deviation event is exactly the ceiling-threshold tail. -/
theorem hypergeomUpperDeviationMass_eq_ceil_tail (N k m : ℕ) (x : ℝ) :
    hypergeomUpperDeviationMass N k m x =
      ∑ i ∈ Finset.range (m + 1),
        if (Int.ceil ((m : ℝ) * k / N + x) : ℝ) ≤ (i : ℝ)
        then hypergeomMass N k m i else 0 := by
  unfold hypergeomUpperDeviationMass
  apply Finset.sum_congr rfl
  intro i hi
  have h := upper_deviation_indicator_ceil ((m : ℝ) * k / N) x i
  by_cases hxcond : x ≤ (i : ℝ) - (m : ℝ) * k / N
  · have hzcond := h.mp hxcond
    have hcast : (Int.ceil ((m : ℝ) * k / N + x) : ℝ) ≤ (i : ℝ) :=
      Int.cast_le.mpr hzcond
    simp [hxcond, hcast]
  · have hznot : ¬ (Int.ceil ((m : ℝ) * k / N + x) : ℝ) ≤ (i : ℝ) := by
      intro hz
      exact hxcond (h.mpr (Int.cast_le.mp hz))
    simp [hxcond, hznot]

/-- The integer lower-deviation event is exactly the floor-threshold tail. -/
theorem hypergeomLowerDeviationMass_eq_floor_tail (N k m : ℕ) (x : ℝ) :
    hypergeomLowerDeviationMass N k m x =
      ∑ i ∈ Finset.range (m + 1),
        if (i : ℝ) ≤ (Int.floor ((m : ℝ) * k / N - x) : ℝ)
        then hypergeomMass N k m i else 0 := by
  unfold hypergeomLowerDeviationMass
  apply Finset.sum_congr rfl
  intro i hi
  have h := lower_deviation_indicator_floor ((m : ℝ) * k / N) x i
  by_cases hxcond : x ≤ (m : ℝ) * k / N - (i : ℝ)
  · have hzcond := h.mp hxcond
    have hcast : (i : ℝ) ≤ (Int.floor ((m : ℝ) * k / N - x) : ℝ) :=
      Int.cast_le.mpr hzcond
    simp [hxcond, hcast]
  · have hznot : ¬ (i : ℝ) ≤ (Int.floor ((m : ℝ) * k / N - x) : ℝ) := by
      intro hz
      exact hxcond (h.mpr (Int.cast_le.mp hz))
    simp [hxcond, hznot]

/-- The two-sided event splits into disjoint upper and lower deviation events. -/
theorem hypergeomTwoSidedDeviationMass_eq_sum (N k m : ℕ) (x : ℝ) (hx : 0 < x) :
    hypergeomTwoSidedDeviationMass N k m x =
      hypergeomUpperDeviationMass N k m x + hypergeomLowerDeviationMass N k m x := by
  unfold hypergeomTwoSidedDeviationMass hypergeomUpperDeviationMass
    hypergeomLowerDeviationMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  let d : ℝ := (i : ℝ) - (m : ℝ) * k / N
  have habs : x ≤ |d| ↔ x ≤ d ∨ x ≤ -d := by
    by_cases hd : 0 ≤ d
    · rw [abs_of_nonneg hd]
      constructor
      · intro h
        exact Or.inl h
      · rintro (h | h)
        · exact h
        · linarith
    · have hd' : d ≤ 0 := le_of_not_ge hd
      rw [abs_of_nonpos hd']
      constructor
      · intro h
        exact Or.inr (by linarith)
      · rintro (h | h)
        · linarith
        · exact h
  have hdisj : ¬ (x ≤ d ∧ x ≤ -d) := by
    intro h
    linarith
  by_cases hu : x ≤ d
  · by_cases hl : x ≤ -d
    · exact False.elim (hdisj ⟨hu, hl⟩)
    · have hhu : x ≤ (i : ℝ) - (m : ℝ) * k / N := by
        simpa [d] using hu
      have hhl : ¬ x ≤ (m : ℝ) * k / N - (i : ℝ) := by
        intro h
        apply hl
        simpa [d] using h
      have habs' : x ≤ |(i : ℝ) - (m : ℝ) * k / N| := by
        simpa [d] using (habs.mpr (Or.inl hu))
      simp [habs', hhu, hhl]
  · by_cases hl : x ≤ -d
    · have hhu : ¬ x ≤ (i : ℝ) - (m : ℝ) * k / N := by
        intro h
        apply hu
        simpa [d] using h
      have hhl : x ≤ (m : ℝ) * k / N - (i : ℝ) := by
        simpa [d] using hl
      have habs' : x ≤ |(i : ℝ) - (m : ℝ) * k / N| := by
        simpa [d] using (habs.mpr (Or.inr hl))
      simp [habs', hhu, hhl]
    · have hhu : ¬ x ≤ (i : ℝ) - (m : ℝ) * k / N := by
        intro h
        apply hu
        simpa [d] using h
      have hhl : ¬ x ≤ (m : ℝ) * k / N - (i : ℝ) := by
        intro h
        apply hl
        simpa [d] using h
      have habs' : ¬ x ≤ |(i : ℝ) - (m : ℝ) * k / N| := by
        intro h
        rcases habs.mp (by simpa [d] using h) with h' | h'
        · exact hu h'
        · exact hl h'
      simp [habs', hhu, hhl]

/-- Integer upper-tail bound with the paper's ceiling and support cutoff. -/
theorem hypergeom_integer_upper_deviation_piecewise_kl (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2 * k ≤ N) (hhalf : 2 * m < N)
    (x : ℝ) (hx : 0 < x) :
    hypergeomUpperDeviationMass N k m x ≤
      (if Int.ceil ((m : ℝ) * k / N + x) ≤ (m : ℤ) then
        Real.exp (-canonicalPiecewiseRate N k m
          (Int.ceil ((m : ℝ) * k / N + x) : ℝ)) else 0) := by
  let z : ℤ := Int.ceil ((m : ℝ) * k / N + x)
  change hypergeomUpperDeviationMass N k m x ≤
    (if z ≤ (m : ℤ) then Real.exp (-canonicalPiecewiseRate N k m (z : ℝ)) else 0)
  by_cases hz : z ≤ (m : ℤ)
  · have hμz : (m : ℝ) * k / N ≤ (z : ℝ) := by
      dsimp [z]
      have hc := Int.le_ceil ((m : ℝ) * k / N + x)
      exact le_of_lt (lt_of_lt_of_le (by linarith) hc)
    have hzm : (z : ℝ) ≤ (m : ℝ) := by exact_mod_cast hz
    rw [if_pos hz, hypergeomUpperDeviationMass_eq_ceil_tail]
    have htail := hypergeom_upper_tail_piecewise_kl N k m hm hmk hk hhalf
      (z : ℝ) hμz hzm
    simpa only [z] using htail
  · rw [if_neg hz]
    have hgt : (m : ℤ) < z := lt_of_not_ge hz
    rw [hypergeomUpperDeviationMass_eq_ceil_tail]
    have hgtR : (m : ℝ) < (z : ℝ) := by
      exact_mod_cast hgt
    have hempty :
        (∑ i ∈ Finset.range (m + 1),
          if (z : ℝ) ≤ (i : ℝ) then hypergeomMass N k m i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have him : i ≤ m := by
        have hi' : i < m + 1 := Finset.mem_range.mp hi
        omega
      have himR : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast him
      have hnot : ¬ (z : ℝ) ≤ (i : ℝ) := by linarith
      simp [hnot]
    rw [hempty]

/-- Integer lower-tail bound with the paper's floor and support cutoff. -/
theorem hypergeom_integer_lower_deviation_piecewise_kl (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2 * k ≤ N) (hhalf : 2 * m < N)
    (x : ℝ) (hx : 0 < x) :
    hypergeomLowerDeviationMass N k m x ≤
      (if (0 : ℤ) ≤ Int.floor ((m : ℝ) * k / N - x) then
        Real.exp (-canonicalPiecewiseRate N k m
          (Int.floor ((m : ℝ) * k / N - x) : ℝ)) else 0) := by
  let z : ℤ := Int.floor ((m : ℝ) * k / N - x)
  change hypergeomLowerDeviationMass N k m x ≤
    (if (0 : ℤ) ≤ z then Real.exp (-canonicalPiecewiseRate N k m (z : ℝ)) else 0)
  by_cases hz : (0 : ℤ) ≤ z
  · have hzμ : (z : ℝ) ≤ (m : ℝ) * k / N := by
      dsimp [z]
      have hf := Int.floor_le ((m : ℝ) * k / N - x)
      exact le_of_lt (lt_of_le_of_lt hf (by linarith))
    have h0z : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    rw [if_pos hz, hypergeomLowerDeviationMass_eq_floor_tail]
    have htail := hypergeom_lower_tail_piecewise_kl N k m hm hmk hk hhalf
      (z : ℝ) hzμ h0z
    simpa only [z] using htail
  · rw [if_neg hz]
    have hneg : z < (0 : ℤ) := lt_of_not_ge hz
    rw [hypergeomLowerDeviationMass_eq_floor_tail]
    have hnegR : (z : ℝ) < 0 := by exact_mod_cast hneg
    have hempty :
        (∑ i ∈ Finset.range (m + 1),
          if (i : ℝ) ≤ (z : ℝ) then hypergeomMass N k m i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi0 : 0 ≤ i := Nat.zero_le i
      have hiR : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi0
      have hnot : ¬ (i : ℝ) ≤ (z : ℝ) := by linarith
      simp [hnot]
    rw [hempty]

/-- Integer two-sided deviation bound, capped by one using normalization. -/
theorem hypergeom_integer_two_sided_deviation_piecewise_kl (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2 * k ≤ N) (hhalf : 2 * m < N)
    (x : ℝ) (hx : 0 < x) :
    hypergeomTwoSidedDeviationMass N k m x ≤
      min 1 ((if Int.ceil ((m : ℝ) * k / N + x) ≤ (m : ℤ) then
          Real.exp (-canonicalPiecewiseRate N k m
            (Int.ceil ((m : ℝ) * k / N + x) : ℝ)) else 0) +
        (if (0 : ℤ) ≤ Int.floor ((m : ℝ) * k / N - x) then
          Real.exp (-canonicalPiecewiseRate N k m
            (Int.floor ((m : ℝ) * k / N - x) : ℝ)) else 0)) := by
  have htotal := hypergeomMass_total N k m (by omega) (by omega)
  have hmass : hypergeomTwoSidedDeviationMass N k m x ≤ 1 := by
    unfold hypergeomTwoSidedDeviationMass
    calc
      _ ≤ ∑ i ∈ Finset.range (m + 1), hypergeomMass N k m i := by
        apply Finset.sum_le_sum
        intro i hi
        split_ifs
        · exact le_rfl
        · exact hypergeomMass_nonneg N k m i
      _ = 1 := htotal
  have hsplit := hypergeomTwoSidedDeviationMass_eq_sum N k m x hx
  have hu := hypergeom_integer_upper_deviation_piecewise_kl N k m hm hmk hk hhalf x hx
  have hl := hypergeom_integer_lower_deviation_piecewise_kl N k m hm hmk hk hhalf x hx
  apply le_min hmass
  rw [hsplit]
  exact add_le_add hu hl

end
end ExactHoeffding
