import ExactHoeffding.ExactOddGlobalTheorem
import ExactHoeffding.ConstantAsymptotics
import Mathlib.Analysis.SpecificLimits.Basic

open Filter
open scoped Topology

namespace ExactHoeffding
noncomputable section

/-- The closed expression displayed for the exact finite-exchangeability
constant in the frozen manuscript. -/
def manuscriptExchangeabilityConstantFormula (N : ℕ) : ℝ :=
  if Even N then (N : ℝ) / ((N : ℝ) - 1)
  else 1 / (((N : ℝ) - 1) * Real.artanh (1 / (N : ℝ)))

/-- The manuscript's parity formula agrees with the infimum over actual
finite-exchangeable probability laws and zero-sum contrasts. -/
theorem manuscript_exchangeability_constant_formula (N : ℕ) (hN : 2 ≤ N) :
    exactExchangeableConstant N = manuscriptExchangeabilityConstantFormula N := by
  have hbase := exact_finite_exchangeability_constants N hN
  by_cases he : Even N
  · rw [hbase]
    simp [manuscriptExchangeabilityConstantFormula, paritySharpConstant, he]
  · rw [hbase]
    simp [manuscriptExchangeabilityConstantFormula, paritySharpConstant, he,
      oddHypergeomConstant_eq_artanh N (by omega)]

/-- The finite constant is attained as a hypergeometric variational maximum.
The witnesses are the balanced even margin and the center-margin singleton
in odd populations. -/
theorem manuscript_exchangeability_variational_max_attained
    (N : ℕ) (hN : 2 ≤ N) :
    ∃ k m : ℕ, 0 < k ∧ k < N ∧ 0 < m ∧ m < N ∧
      normalizedHypergeomProxy N k m = hypergeomVariationalConstant N := by
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' N
  · subst N
    refine ⟨q, 1, by omega, by omega, by omega, by omega, ?_⟩
    rw [hypergeomVariationalConstant_even q (by omega)]
    exact normalizedHypergeomProxy_even_attains q 1 (by omega) (by omega) (by omega)
  · subst N
    have hn : 0 < q := by omega
    refine ⟨q, 1, by omega, by omega, by omega, by omega, ?_⟩
    rw [hypergeomVariationalConstant_odd q hn]
    exact (odd_normalized_proxy_all_equality q q 1 hn hn (by omega) (by omega)
      (by omega)).2 ⟨Or.inl rfl, Or.inl rfl⟩

/-- For odd populations, the manuscript's closed-form maximum has exactly
its stated equality cases, including the sample and success complements. -/
theorem manuscript_exchangeability_odd_extremizers
    (n k m : ℕ) (hn : 0 < n) (hk : 0 < k) (hkN : k < 2*n+1)
    (hm : 0 < m) (hmN : m < 2*n+1) :
    normalizedHypergeomProxy (2*n+1) k m ≤
        1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) ∧
      (normalizedHypergeomProxy (2*n+1) k m =
          1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) ↔
        (m = 1 ∨ m = 2*n) ∧ (k = n ∨ k = n+1)) := by
  rw [← oddHypergeomConstant_eq_artanh (2*n+1) (by omega)]
  exact odd_normalized_proxy_global_optimality n k m hn hk hkN hm hmN

/-- Typed proposition contract for the complete frozen theorem
`thm:exchange`: exact formula, validity and leastness over genuine exchangeable
laws, sharp variational witnesses, odd equality cases, the universal upper
comparison, and the first-order asymptotic. -/
theorem manuscript_exchangeability_constants_contract
    (N : ℕ) (hN : 2 ≤ N) :
    exactExchangeableConstant N = manuscriptExchangeabilityConstantFormula N ∧
      IsExchangeableCoefficient N (manuscriptExchangeabilityConstantFormula N) ∧
      IsLeast {C : ℝ | IsExchangeableCoefficient N C}
        (manuscriptExchangeabilityConstantFormula N) ∧
      manuscriptExchangeabilityConstantFormula N ≤ (N : ℝ) / ((N : ℝ) - 1) ∧
      (¬ Even N → manuscriptExchangeabilityConstantFormula N <
        (N : ℝ) / ((N : ℝ) - 1)) ∧
      (∀ n : ℕ, 0 < n →
        exactExchangeableConstant (2*n+1) =
          1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) ∧
        (∀ k m : ℕ, 0 < k → k < 2*n+1 → 0 < m → m < 2*n+1 →
          normalizedHypergeomProxy (2*n+1) k m ≤
              1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) ∧
            (normalizedHypergeomProxy (2*n+1) k m =
                1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) ↔
              (m = 1 ∨ m = 2*n) ∧ (k = n ∨ k = n+1)))) ∧
      (∃ k m : ℕ, 0 < k ∧ k < N ∧ 0 < m ∧ m < N ∧
        normalizedHypergeomProxy N k m = hypergeomVariationalConstant N) ∧
      Tendsto (fun N : ℕ => (N : ℝ) * (exactExchangeableConstant N - 1))
        atTop (𝓝 1) := by
  have hformula := manuscript_exchangeability_constant_formula N hN
  have hparity : paritySharpConstant N = manuscriptExchangeabilityConstantFormula N := by
    calc
      paritySharpConstant N = exactExchangeableConstant N :=
        (exact_finite_exchangeability_constants N hN).symm
      _ = manuscriptExchangeabilityConstantFormula N := hformula
  have hvalid : IsExchangeableCoefficient N (manuscriptExchangeabilityConstantFormula N) := by
    rw [← hparity]
    exact paritySharpConstant_is_valid N hN
  have hleast : IsLeast {C : ℝ | IsExchangeableCoefficient N C}
      (manuscriptExchangeabilityConstantFormula N) := by
    rw [← hparity]
    exact ⟨paritySharpConstant_is_valid N hN,
      fun C hC => paritySharpConstant_is_least N hN C hC⟩
  have hupper : manuscriptExchangeabilityConstantFormula N ≤ (N : ℝ) / ((N : ℝ) - 1) := by
    rw [← hparity]
    unfold paritySharpConstant
    split_ifs with he
    · rfl
    · exact (oddHypergeomConstant_lt_even_bound N (by omega)).le
  have hstrict : ¬ Even N → manuscriptExchangeabilityConstantFormula N <
      (N : ℝ) / ((N : ℝ) - 1) := by
    intro hodd
    rw [← hparity, paritySharpConstant, if_neg hodd]
    exact oddHypergeomConstant_lt_even_bound N (by omega)
  have hodd : ∀ n : ℕ, 0 < n →
      exactExchangeableConstant (2*n+1) =
        1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) ∧
      (∀ k m : ℕ, 0 < k → k < 2*n+1 → 0 < m → m < 2*n+1 →
        normalizedHypergeomProxy (2*n+1) k m ≤
            1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) ∧
          (normalizedHypergeomProxy (2*n+1) k m =
              1 / ((((2*n+1:ℕ):ℝ)-1) * Real.artanh (1/((2*n+1:ℕ):ℝ))) ↔
            (m = 1 ∨ m = 2*n) ∧ (k = n ∨ k = n+1))) := by
    intro n hn
    constructor
    · exact exact_odd_exchangeable_constant_closed_form n hn
    · intro k m hk hkN hm hmN
      exact manuscript_exchangeability_odd_extremizers n k m hn hk hkN hm hmN
  exact ⟨hformula, hvalid, hleast, hupper, hstrict, hodd,
    manuscript_exchangeability_variational_max_attained N hN,
    exactExchangeableConstant_first_order_limit⟩

end
end ExactHoeffding
