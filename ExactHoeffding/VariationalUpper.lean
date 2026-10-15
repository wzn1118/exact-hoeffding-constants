import ExactHoeffding.ExchangeableConstants
import ExactHoeffding.TwoLevelReduction
import ExactHoeffding.HypergeometricTail

open MeasureTheory

namespace ExactHoeffding

private theorem subset_average_zero {N : ℕ} (y : Fin N→ℝ) :
    hammingSliceAverage (fun S => Real.exp (∑i∈S,y i)) 0=1 := by
  simp [hammingSliceAverage,Finset.powersetCard_zero]

private theorem subset_average_full {N : ℕ} (y : Fin N→ℝ) (hy : ∑i,y i=0) :
    hammingSliceAverage (fun S => Real.exp (∑i∈S,y i)) N=1 := by
  have hpow : (Finset.univ : Finset (Fin N)).powersetCard N={Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin N))
  unfold hammingSliceAverage
  rw [hpow]
  simp [hy]

theorem centered_slice_mgf_bound_of_proxy_ceiling (N k : ℕ) (hN : 2≤N) (hk : k≤N)
    (C : ℝ) (hC : 0≤C)
    (hbound : ∀j m : ℕ,0<j → j<N → 0<m → m<N → normalizedHypergeomProxy N j m≤C)
    (y : Fin N→ℝ) (hy : ∑i,y i=0) :
    hammingSliceAverage (fun S => Real.exp (∑i∈S,y i)) k≤Real.exp (C*(∑i,(y i)^2)/8) := by
  have hsq : 0≤∑i,(y i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hExp : 1≤Real.exp (C*(∑i,(y i)^2)/8) := Real.one_le_exp (by positivity)
  by_cases hk0 : k=0
  · subst k
    rw [subset_average_zero]
    exact hExp
  by_cases hkN : k=N
  · subst k
    rw [subset_average_full y hy]
    exact hExp
  by_cases hq : 0<∑i,(y i)^2
  · obtain ⟨M,t,hM0,hMN,ht,hnorm,hdom⟩ := centered_slice_two_level_reduction N k
      (by omega) (by omega) y hy hq
    have hproxy := (hypergeomOptimalProxy_isOptimal N k M.card hk hMN.le).1 t
    have hup := hbound k M.card (by omega) (by omega) hM0 hMN
    have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    have hmR : (0:ℝ)<M.card := by exact_mod_cast hM0
    have hmNR : (M.card:ℝ)<N := by exact_mod_cast hMN
    have hd : 0<(M.card:ℝ)*((N:ℝ)-M.card) := by positivity
    have hop : hypergeomOptimalProxy N k M.card≤C*((M.card:ℝ)*((N:ℝ)-M.card))/(4*(N:ℝ)) := by
      unfold normalizedHypergeomProxy at hup
      apply (le_div_iff₀ (show 0<4*(N:ℝ) by positivity)).2
      have h := (div_le_iff₀ hd).mp (show
        (4*(N:ℝ)*hypergeomOptimalProxy N k M.card)/((M.card:ℝ)*((N:ℝ)-M.card))≤C by
          simpa only [div_mul_eq_mul_div] using hup)
      nlinarith only [h]
    have hscaled := mul_le_mul_of_nonneg_right hop (show 0≤t^2/2 by positivity)
    have hpsi : hypergeomCenteredLogMGF N k M.card t≤C*(∑i,(y i)^2)/8 := by
      rw [hnorm]
      apply hproxy.trans
      convert hscaled using 1 <;> ring
    apply hdom.trans
    rw [centeredHypergeomMGF_eq_exp_log N k M.card hk hMN.le t]
    exact Real.exp_le_exp.mpr hpsi
  · have hzero : ∑i,(y i)^2=0 := le_antisymm (le_of_not_gt hq) hsq
    have hyzero : y=0 := by
      funext i
      have h := Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j∈Finset.univ) => sq_nonneg (y j)) |>.mp hzero
      exact (sq_eq_zero_iff).mp (h i (Finset.mem_univ i))
    rw [hyzero]
    have hden : ((N.choose k):ℝ)≠0 := by
      exact_mod_cast Nat.choose_ne_zero hk
    simp [hammingSliceAverage,hden]

/-- A bound on the actual hypergeometric variational family gives the
universal finite-exchangeability exponential inequality. -/
theorem isExchangeableCoefficient_of_proxy_ceiling (N : ℕ) (hN : 2≤N)
    (C : ℝ) (hC : 0≤C)
    (hbound : ∀j m : ℕ,0<j → j<N → 0<m → m<N → normalizedHypergeomProxy N j m≤C) :
    IsExchangeableCoefficient N C := by
  intro μ hμ hex hcube a ha t
  let : IsProbabilityMeasure μ := hμ
  have hred := finiteExchangeable_mgf_le_max_slice μ hex hcube a t
  apply hred.trans
  apply Finset.sup'_le
  intro k hk
  have hkN : k≤N := by have hh := Finset.mem_range.mp hk; omega
  let y : Fin N→ℝ := fun i => 2*t*a i
  have hysum : ∑i,y i=0 := by
    dsimp [y]
    rw [←Finset.mul_sum,ha,mul_zero]
  have hsq : (∑i,(y i)^2)=4*t^2*(∑i,(a i)^2) := by
    dsimp [y]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hpoint (S : Finset (Fin N)) : t*booleanContrast a S=∑i∈S,y i := by
    rw [booleanContrast_eq,ha,sub_zero]
    dsimp [y]
    rw [←Finset.mul_sum]
    ring
  simp_rw [hpoint]
  have h := centered_slice_mgf_bound_of_proxy_ceiling N k hN hkN C hC hbound y hysum
  rw [hsq] at h
  convert h using 1
  congr 1
  ring

theorem universal_even_coefficient_valid (N : ℕ) (hN : 2≤N) :
    IsExchangeableCoefficient N ((N:ℝ)/((N:ℝ)-1)) := by
  have hNR : (2:ℝ)≤N := by exact_mod_cast hN
  have hN0 : (0:ℝ)<N := by linarith
  have hN1 : (0:ℝ)<(N:ℝ)-1 := by linarith
  apply isExchangeableCoefficient_of_proxy_ceiling N hN _ (by positivity)
  intro k m hk0 hkN hm0 hmN
  exact normalizedHypergeomProxy_universal_upper N k m hN hkN.le hm0 hmN

end ExactHoeffding
