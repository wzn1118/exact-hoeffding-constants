import ExactHoeffding.TwoLevelExistence
import ExactHoeffding.TwoLevelRepresentation

namespace ExactHoeffding

/-- The actual finite-slice exponential moment of a nonzero centered vector
is dominated by a centered hypergeometric MGF at exactly the same squared norm. -/
theorem centered_slice_two_level_reduction (N k : ℕ) (hk0 : 0 < k) (hkN : k < N)
    (y : Fin N → ℝ) (hy : ∑ i, y i = 0) (hq : 0 < ∑ i, (y i) ^ 2) :
    ∃ (M : Finset (Fin N)) (t : ℝ),
      0 < M.card ∧ M.card < N ∧ t ≠ 0 ∧
      (∑ i, (y i) ^ 2) = (M.card : ℝ) * ((N : ℝ) - M.card) * t ^ 2 / N ∧
      hammingSliceAverage (fun S => Real.exp (∑ i ∈ S, y i)) k ≤
        centeredHypergeomMGF N k M.card t := by
  classical
  have hN : 0 < N := hk0.trans hkN
  obtain ⟨v, hvsum, hvsq, hvcard, hvdom⟩ := exists_two_level_slice_dominator N k hk0 hkN y
  have hvzero : ∑ i, v i = 0 := hvsum.trans hy
  rcases atMostTwo_zero_sum_representation v hN hvzero hvcard with hv | ⟨M,t,hM0,hMN,ht,hrepr⟩
  · rw [hv] at hvsq
    simp only [Pi.zero_apply, zero_pow (by omega : (2 : ℕ) ≠ 0), Finset.sum_const_zero] at hvsq
    linarith
  · refine ⟨M,t,hM0,hMN,ht,?_,?_⟩
    · rw [← hvsq, hrepr]
      exact twoLevelVector_sq_norm M t hN
    · have hden : 0 <
          (((Finset.univ : Finset (Fin N)).powersetCard k).card : ℝ) := by
        rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
        exact_mod_cast Nat.choose_pos (Nat.le_of_lt hkN)
      have havg := div_le_div_of_nonneg_right hvdom hden.le
      simp only [sliceExponential_nat] at havg
      change hammingSliceAverage (fun S => Real.exp (∑ i ∈ S, y i)) k ≤
        hammingSliceAverage (fun S => Real.exp (∑ i ∈ S, v i)) k at havg
      rw [hrepr, twoLevelVector_slice_mgf M k (Nat.le_of_lt hkN) t hN] at havg
      exact havg

end ExactHoeffding
