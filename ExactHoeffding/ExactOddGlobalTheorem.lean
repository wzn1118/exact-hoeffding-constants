import ExactHoeffding.ExactParityConstants

namespace ExactHoeffding
noncomputable section

/-- The odd-population proxy is globally bounded, and its complete equality
classification holds simultaneously for every legal pair of margins. -/
theorem odd_normalized_proxy_global_optimality (n k m : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkN : k < 2*n+1)
    (hm : 0 < m) (hmN : m < 2*n+1) :
    normalizedHypergeomProxy (2*n+1) k m ≤ oddHypergeomConstant (2*n+1) ∧
      (normalizedHypergeomProxy (2*n+1) k m = oddHypergeomConstant (2*n+1) ↔
        (m = 1 ∨ m = 2*n) ∧ (k = n ∨ k = n+1)) := by
  exact ⟨odd_normalized_proxy_all_upper n k m hn hk hkN hm hmN,
    odd_normalized_proxy_all_equality n k m hn hk hkN hm hmN⟩

/-- The odd variational optimum is the singleton extremizer's value. -/
theorem odd_variational_constant_global_optimum (n : ℕ) (hn : 0 < n) :
    hypergeomVariationalConstant (2*n+1) = oddHypergeomConstant (2*n+1) :=
  hypergeomVariationalConstant_odd n hn

/-- The exact odd finite-exchangeability constant in closed form. -/
theorem exact_odd_exchangeable_constant_closed_form (n : ℕ) (hn : 0 < n) :
    exactExchangeableConstant (2*n+1) =
      1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) :=
  exactExchangeableConstant_odd n hn

/-- The closed-form odd constant is valid for every finitely exchangeable
law on the cube and every zero-sum contrast. -/
theorem odd_exchangeable_constant_is_valid (n : ℕ) (hn : 0 < n) :
    IsExchangeableCoefficient (2*n+1)
      (1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ)))) := by
  rw [← exact_odd_exchangeable_constant_closed_form n hn,
    exactExchangeableConstant_eq_variational (2*n+1) (by omega)]
  exact hypergeomVariationalConstant_is_valid (2*n+1) (by omega)

/-- No smaller coefficient gives the uniform finite-exchangeability MGF
inequality for an odd population. -/
theorem odd_exchangeable_constant_is_least (n : ℕ) (hn : 0 < n) (C : ℝ)
    (hC : IsExchangeableCoefficient (2*n+1) C) :
    1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) ≤ C := by
  rw [← exact_odd_exchangeable_constant_closed_form n hn,
    exactExchangeableConstant_eq_variational (2*n+1) (by omega)]
  exact (exchangeable_coefficient_iff_variational (2*n+1) (by omega) C).1 hC

/-- The center-margin singleton realizes the odd closed-form constant. -/
theorem odd_exchangeable_constant_attained (n : ℕ) (hn : 0 < n) :
    normalizedHypergeomProxy (2*n+1) n 1 =
      1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) := by
  rw [← oddHypergeomConstant_eq_artanh (2*n+1) (by omega)]
  exact (odd_normalized_proxy_all_equality n n 1 hn hn (by omega) (by omega)
    (by omega)).2 ⟨Or.inl rfl, Or.inl rfl⟩

end
end ExactHoeffding
