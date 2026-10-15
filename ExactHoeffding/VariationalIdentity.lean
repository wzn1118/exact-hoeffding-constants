import ExactHoeffding.VariationalUpper
import ExactHoeffding.HammingExchangeableLower

open MeasureTheory

namespace ExactHoeffding

/-- The hypergeometric variational value itself is a valid universal
coefficient for arbitrary exchangeable laws on the real cube. -/
theorem hypergeomVariationalConstant_is_valid (N : ℕ) (hN : 2≤N) :
    IsExchangeableCoefficient N (hypergeomVariationalConstant N) := by
  apply isExchangeableCoefficient_of_proxy_ceiling N hN _
    (hypergeomVariationalConstant_pos N hN).le
  exact fun k m hk0 hkN hm0 hmN =>
    normalizedHypergeomProxy_le_variational N k m hN hk0 hkN hm0 hmN

/-- Universal validity is equivalent to exceeding the actual
hypergeometric variational supremum. -/
theorem exchangeable_coefficient_iff_variational (N : ℕ) (hN : 2≤N) (C : ℝ) :
    IsExchangeableCoefficient N C ↔ hypergeomVariationalConstant N≤C := by
  constructor
  · intro hC
    exact hypergeomVariationalConstant_le_exchangeable_coefficient N hN C hC
  · intro hC
    apply isExchangeableCoefficient_of_proxy_ceiling N hN C
      ((hypergeomVariationalConstant_pos N hN).le.trans hC)
    intro k m hk0 hkN hm0 hmN
    exact (normalizedHypergeomProxy_le_variational N k m hN hk0 hkN hm0 hmN).trans hC

/-- Exact Lee-Kim variational identity between genuine measure-theoretic
finite exchangeability and the finite hypergeometric optimization. -/
theorem exactExchangeableConstant_eq_variational (N : ℕ) (hN : 2≤N) :
    exactExchangeableConstant N=hypergeomVariationalConstant N := by
  have hn : ({C : ℝ | IsExchangeableCoefficient N C} : Set ℝ).Nonempty :=
    ⟨hypergeomVariationalConstant N,hypergeomVariationalConstant_is_valid N hN⟩
  have hb : BddBelow {C : ℝ | IsExchangeableCoefficient N C} := by
    refine ⟨hypergeomVariationalConstant N,?_⟩
    intro C hC
    exact (exchangeable_coefficient_iff_variational N hN C).1 hC
  apply le_antisymm
  · exact csInf_le hb (hypergeomVariationalConstant_is_valid N hN)
  · exact le_csInf hn (fun C hC => (exchangeable_coefficient_iff_variational N hN C).1 hC)

end ExactHoeffding
