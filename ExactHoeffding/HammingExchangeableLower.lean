import ExactHoeffding.HammingCoefficientLower
import ExactHoeffding.ExchangeableConstants
import ExactHoeffding.HammingMeasure

open MeasureTheory

namespace ExactHoeffding

/-- Every universally valid exchangeable coefficient controls each actual
Hamming-law half-two-level MGF, hence each normalized hypergeometric proxy. -/
theorem normalized_proxy_le_exchangeable_coefficient (N k m : ℕ)
    (hN : 2 ≤ N) (_hk0 : 0 < k) (hkN : k < N) (hm0 : 0 < m) (hmN : m < N)
    (C : ℝ) (hC : IsExchangeableCoefficient N C) :
    normalizedHypergeomProxy N k m ≤ C := by
  classical
  obtain ⟨M, hMsub, hMcard⟩ := Finset.exists_subset_card_eq
    (show m ≤ (Finset.univ : Finset (Fin N)).card by simpa using hmN.le)
  have hN0 : 0 < N := by omega
  have hM0 : 0 < M.card := by omega
  have hMN : M.card < N := by omega
  have hfamily : ∀ s : ℝ,
      hammingSliceAverage
        (fun S => Real.exp (booleanContrast (fun i => twoLevelVector M s i / 2) S)) k ≤
      Real.exp (C * (∑ i : Fin N, (twoLevelVector M s i / 2) ^ 2) / 2) := by
    intro s
    let a : Fin N → ℝ := fun i => twoLevelVector M s i / 2
    have ha : ∑ i, a i = 0 := by
      dsimp [a]
      rw [← Finset.sum_div, twoLevelVector_sum M s hN0, zero_div]
    have h := hC (uniformHammingMeasure N k)
      (uniformHammingMeasure_isProbability N k hkN.le)
      (uniformHammingMeasure_exchangeable N k)
      (uniformHammingMeasure_ae_cube N k) a ha 1
    unfold expContrast at h
    simp only [one_mul, one_pow, mul_one] at h
    have hi := uniformHammingMeasure_expContrast N k a 1
    simp only [one_mul] at hi
    rw [hi] at h
    exact h
  simpa only [hMcard] using normalized_proxy_le_hamming_coefficient k hkN.le M hM0 hMN C hfamily

/-- Any valid exchangeable coefficient is at least the whole hypergeometric
variational value, derived by instantiating genuine Hamming probability measures. -/
theorem hypergeomVariationalConstant_le_exchangeable_coefficient (N : ℕ) (hN : 2 ≤ N)
    (C : ℝ) (hC : IsExchangeableCoefficient N C) : hypergeomVariationalConstant N ≤ C := by
  apply hypergeomVariationalConstant_le N hN C
  intro k m hk0 hkN hm0 hmN
  exact normalized_proxy_le_exchangeable_coefficient N k m hN hk0 hkN hm0 hmN C hC

/-- The zero-tilt variance lower bound for every genuinely valid exchangeable coefficient. -/
theorem normalized_variance_le_exchangeable_coefficient (N k m : ℕ)
    (hN : 2 ≤ N) (hk0 : 0 < k) (hkN : k < N) (hm0 : 0 < m) (hmN : m < N)
    (C : ℝ) (hC : IsExchangeableCoefficient N C) :
    (4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) * hypergeomTiltVariance N k m 0 ≤ C := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmNR : (m : ℝ) < N := by exact_mod_cast hmN
  have h := mul_le_mul_of_nonneg_left (hypergeomOptimalProxy_ge_variance N k m hkN.le hmN.le)
    (show 0 ≤ 4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m)) by positivity)
  exact h.trans (normalized_proxy_le_exchangeable_coefficient N k m hN hk0 hkN hm0 hmN C hC)

/-- The balanced Hamming example forces the sharp even coefficient. -/
theorem even_coefficient_lower_from_hamming (q : ℕ) (hq : 0 < q)
    (C : ℝ) (hC : IsExchangeableCoefficient (2 * q) C) :
    ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) ≤ C := by
  have h := normalized_proxy_le_exchangeable_coefficient (2 * q) q 1 (by omega)
    hq (by omega) (by omega) (by omega) C hC
  rwa [normalizedHypergeomProxy_even_attains q 1 hq (by omega) (by omega)] at h

end ExactHoeffding
