import ExactHoeffding.MeasureExchangeability
import ExactHoeffding.NormalizedProxy

open MeasureTheory

namespace ExactHoeffding
noncomputable section

/-- A coefficient valid for every exchangeable probability law supported
on the real cube and every zero-sum linear contrast. -/
def IsExchangeableCoefficient (N : ℕ) (C : ℝ) : Prop :=
  ∀(μ : Measure (Fin N→ℝ)), IsProbabilityMeasure μ →
    FiniteExchangeableMeasure μ → (∀ᵐx ∂μ,x∈realCube N) →
    ∀(a : Fin N→ℝ), (∑i,a i)=0 → ∀t : ℝ,
      (∫x,expContrast a t x ∂μ)≤Real.exp (C*t^2*(∑i,(a i)^2)/2)

/-- The exact finite-exchangeability constant of the manuscript. -/
def exactExchangeableConstant (N : ℕ) : ℝ := sInf {C : ℝ | IsExchangeableCoefficient N C}

/-- The finite-dimensional hypergeometric variational value. -/
def hypergeomVariationalConstant (N : ℕ) : ℝ :=
  sSup {v : ℝ | ∃k m : ℕ,0<k ∧ k<N ∧ 0<m ∧ m<N ∧ v=normalizedHypergeomProxy N k m}

theorem hypergeomVariationalSet_nonempty (N : ℕ) (hN : 2≤N) :
    ({v : ℝ | ∃k m : ℕ,0<k ∧ k<N ∧ 0<m ∧ m<N ∧ v=normalizedHypergeomProxy N k m} : Set ℝ).Nonempty := by
  refine ⟨normalizedHypergeomProxy N 1 1,1,1,by omega,by omega,by omega,by omega,rfl⟩

theorem hypergeomVariationalConstant_le (N : ℕ) (hN : 2≤N) (C : ℝ)
    (hC : ∀k m : ℕ,0<k → k<N → 0<m → m<N → normalizedHypergeomProxy N k m≤C) :
    hypergeomVariationalConstant N≤C := by
  apply csSup_le (hypergeomVariationalSet_nonempty N hN)
  rintro v ⟨k,m,hk0,hkN,hm0,hmN,rfl⟩
  exact hC k m hk0 hkN hm0 hmN

theorem hypergeomVariationalSet_bddAbove (N : ℕ) (hN : 2≤N) :
    BddAbove {v : ℝ | ∃k m : ℕ,0<k ∧ k<N ∧ 0<m ∧ m<N ∧ v=normalizedHypergeomProxy N k m} := by
  refine ⟨(N:ℝ)/((N:ℝ)-1),?_⟩
  rintro v ⟨k,m,hk0,hkN,hm0,hmN,rfl⟩
  exact normalizedHypergeomProxy_universal_upper N k m hN hkN.le hm0 hmN

theorem normalizedHypergeomProxy_le_variational (N k m : ℕ)
    (hN : 2≤N) (hk0 : 0<k) (hkN : k<N) (hm0 : 0<m) (hmN : m<N) :
    normalizedHypergeomProxy N k m≤hypergeomVariationalConstant N :=
  le_csSup (hypergeomVariationalSet_bddAbove N hN) ⟨k,m,hk0,hkN,hm0,hmN,rfl⟩

theorem hypergeomVariationalConstant_even (q : ℕ) (hq : 0<q) :
    hypergeomVariationalConstant (2*q)=((2*q:ℕ):ℝ)/(((2*q:ℕ):ℝ)-1) := by
  apply le_antisymm
  · exact hypergeomVariationalConstant_le (2*q) (by omega) _
      (fun k m _ hkN hm0 hmN => normalizedHypergeomProxy_universal_upper (2*q) k m (by omega) hkN.le hm0 hmN)
  · rw [← normalizedHypergeomProxy_even_attains q 1 hq (by omega) (by omega)]
    exact normalizedHypergeomProxy_le_variational (2*q) q 1 (by omega) hq (by omega) (by omega) (by omega)

theorem hypergeomVariationalConstant_pos (N : ℕ) (hN : 2≤N) :
    0<hypergeomVariationalConstant N := by
  have hNR : (2:ℝ)≤N := by exact_mod_cast hN
  have hN0 : (0:ℝ)<N := by linarith
  have hN1 : (0:ℝ)<(N:ℝ)-1 := by linarith
  have hvar := hypergeomOptimalProxy_ge_variance N 1 1 (by omega) (by omega)
  rw [hypergeomTiltVariance_zero N 1 1 (by omega) (by omega)] at hvar
  have hNsub : ((N-1:ℕ):ℝ)=(N:ℝ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
  rw [hNsub] at hvar
  norm_num only [Nat.cast_one,one_mul] at hvar
  have hvpos : 0<((N:ℝ)-1)*((N:ℝ)-1)/((N:ℝ)^2*((N:ℝ)-1)) := by positivity
  have hop : 0<hypergeomOptimalProxy N 1 1 := hvpos.trans_le hvar
  have hnorm : 0<normalizedHypergeomProxy N 1 1 := by
    unfold normalizedHypergeomProxy
    norm_num only [Nat.cast_one,one_mul]
    positivity
  exact hnorm.trans_le (normalizedHypergeomProxy_le_variational N 1 1 hN (by omega) (by omega) (by omega) (by omega))

end
end ExactHoeffding
