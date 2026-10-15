import ExactHoeffding.OddHypergeomExtremizers
import ExactHoeffding.VariationalIdentity
import Mathlib.Algebra.Ring.Parity

namespace ExactHoeffding
noncomputable section

/-- The paper's odd and even finite-population coefficient. -/
def paritySharpConstant (N : ℕ) : ℝ :=
  if Even N then (N:ℝ)/((N:ℝ)-1) else oddHypergeomConstant N

theorem hypergeomVariationalConstant_odd (n : ℕ) (hn : 0<n) :
    hypergeomVariationalConstant (2*n+1)=oddHypergeomConstant (2*n+1) := by
  apply le_antisymm
  · apply hypergeomVariationalConstant_le (2*n+1) (by omega)
    exact fun k m hk0 hkN hm0 hmN => odd_normalized_proxy_all_upper n k m hn hk0 hkN hm0 hmN
  · have heq : normalizedHypergeomProxy (2*n+1) n 1=oddHypergeomConstant (2*n+1) :=
      (odd_normalized_proxy_all_equality n n 1 hn hn (by omega) (by omega) (by omega)).2 ⟨Or.inl rfl,Or.inl rfl⟩
    rw [←heq]
    exact normalizedHypergeomProxy_le_variational (2*n+1) n 1 (by omega) hn (by omega) (by omega) (by omega)

theorem exactExchangeableConstant_even (q : ℕ) (hq : 0<q) :
    exactExchangeableConstant (2*q)=((2*q:ℕ):ℝ)/(((2*q:ℕ):ℝ)-1) := by
  rw [exactExchangeableConstant_eq_variational (2*q) (by omega),hypergeomVariationalConstant_even q hq]

theorem exactExchangeableConstant_odd (n : ℕ) (hn : 0<n) :
    exactExchangeableConstant (2*n+1)=1/((((2*n+1:ℕ):ℝ)-1)*Real.artanh (1/((2*n+1:ℕ):ℝ))) := by
  rw [exactExchangeableConstant_eq_variational (2*n+1) (by omega),
    hypergeomVariationalConstant_odd n hn,oddHypergeomConstant_eq_artanh (2*n+1) (by omega)]

/-- The exact finite-exchangeability constant, with no asymptotic
restriction or unproved analytic assumption. -/
theorem exact_finite_exchangeability_constants (N : ℕ) (hN : 2≤N) :
    exactExchangeableConstant N=paritySharpConstant N := by
  obtain ⟨q,hq|hq⟩ := Nat.even_or_odd' N
  · subst N
    have he : Even (2*q) := ⟨q,by omega⟩
    rw [paritySharpConstant,if_pos he,exactExchangeableConstant_even q (by omega)]
  · subst N
    have he : ¬Even (2*q+1) := by
      intro h
      obtain ⟨r, hr⟩ := h
      omega
    rw [paritySharpConstant,if_neg he,exactExchangeableConstant_eq_variational (2*q+1) (by omega),
      hypergeomVariationalConstant_odd q (by omega)]

theorem paritySharpConstant_is_valid (N : ℕ) (hN : 2≤N) :
    IsExchangeableCoefficient N (paritySharpConstant N) := by
  rw [←exact_finite_exchangeability_constants N hN,exactExchangeableConstant_eq_variational N hN]
  exact hypergeomVariationalConstant_is_valid N hN

theorem paritySharpConstant_is_least (N : ℕ) (hN : 2≤N) (C : ℝ)
    (hC : IsExchangeableCoefficient N C) : paritySharpConstant N≤C := by
  rw [←exact_finite_exchangeability_constants N hN,exactExchangeableConstant_eq_variational N hN]
  exact (exchangeable_coefficient_iff_variational N hN C).1 hC

end
end ExactHoeffding
