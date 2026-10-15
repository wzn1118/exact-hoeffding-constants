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

/-- Valid odd-population coefficients form exactly the closed upper ray
starting at the explicit optimal coefficient. -/
theorem odd_exchangeable_coefficient_iff (n : ℕ) (hn : 0 < n) (C : ℝ) :
    IsExchangeableCoefficient (2*n+1) C ↔
      1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) ≤ C := by
  rw [exchangeable_coefficient_iff_variational (2*n+1) (by omega) C,
    ← exactExchangeableConstant_eq_variational (2*n+1) (by omega),
    exact_odd_exchangeable_constant_closed_form n hn]

/-- The odd closed form is an attained minimum, not merely an infimum. -/
theorem odd_exchangeable_constant_isLeast (n : ℕ) (hn : 0 < n) :
    IsLeast {C : ℝ | IsExchangeableCoefficient (2*n+1) C}
      (1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ)))) := by
  exact ⟨odd_exchangeable_constant_is_valid n hn,
    fun C hC => odd_exchangeable_constant_is_least n hn C hC⟩

/-- End-to-end odd-population theorem: all legal margins, the exhaustive
extremizers, the finite variational optimum, the exact exchangeability
constant, and validity with leastness of its explicit closed form.
There is no asymptotic or bounded-sample-size hypothesis. -/
theorem exact_odd_global_theorem (n : ℕ) (hn : 0 < n) :
    let N := 2*n+1
    let C : ℝ := 1 / (((N:ℝ)-1) * Real.artanh (1/(N:ℝ)))
    (∀ k m : ℕ, 0 < k → k < N → 0 < m → m < N →
      normalizedHypergeomProxy N k m ≤ C ∧
        (normalizedHypergeomProxy N k m = C ↔
          (m = 1 ∨ m = 2*n) ∧ (k = n ∨ k = n+1))) ∧
      hypergeomVariationalConstant N = C ∧
      exactExchangeableConstant N = C ∧
      IsLeast {D : ℝ | IsExchangeableCoefficient N D} C := by
  dsimp only
  have hclosed := oddHypergeomConstant_eq_artanh (2*n+1) (by omega)
  refine ⟨?_, ?_, exact_odd_exchangeable_constant_closed_form n hn,
    odd_exchangeable_constant_isLeast n hn⟩
  · intro k m hk hkN hm hmN
    rw [← hclosed]
    exact odd_normalized_proxy_global_optimality n k m hn hk hkN hm hmN
  · rw [hypergeomVariationalConstant_odd n hn, hclosed]

end
end ExactHoeffding
