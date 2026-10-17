import ExactHoeffding.ManuscriptCoreContracts
import ExactHoeffding.ParityProxyComparison
import ExactHoeffding.OddHypergeomExtremizers
import ExactHoeffding.ExchangeableVarianceSupremum
import ExactHoeffding.FiniteSupportLegendreCalculus
import ExactHoeffding.ManuscriptMeanCurveContracts

/-!
# Extended typed contracts for full displayed manuscript clauses

These wrappers collect already proved clauses under one proposition whose type
can be inspected against the corresponding frozen theorem environment.
-/

namespace ExactHoeffding
noncomputable section
open Filter Asymptotics
open scoped Topology

/-- Full contract for `prop:variance_parity`, including the sequence-form
fourth-order odd expansion in addition to the exact constant and integral gap. -/
theorem manuscript_prop_variance_parity_full_contract
    (N : ℕ) (hN : 2 ≤ N) :
    (exactExchangeableVarianceConstant N = parityVarianceConstant N ∧
      exactExchangeableVarianceConstant N =
        4 * (⌊(N:ℝ)^2 / 4⌋₊ : ℝ) / ((N:ℝ) * ((N:ℝ)-1)) ∧
      (Even N → exactExchangeableConstant N = exactExchangeableVarianceConstant N) ∧
      (¬ Even N → exactExchangeableVarianceConstant N < exactExchangeableConstant N ∧
        exactExchangeableConstant N < (N:ℝ) / ((N:ℝ)-1) ∧
        exactExchangeableConstant N - exactExchangeableVarianceConstant N =
          (2 * ∫ t in (0:ℝ)..(1/(N:ℝ)), t * Real.artanh t) /
            ((1-1/(N:ℝ))*Real.artanh (1/(N:ℝ))))) ∧
    (∀ (Nseq Jseq : ℕ → ℕ), Filter.Tendsto Nseq Filter.atTop Filter.atTop →
      (∀ᶠ i in atTop, Nseq i = 2*Jseq i+1) →
      (fun i => exactExchangeableConstant (Nseq i) -
          exactExchangeableVarianceConstant (Nseq i) -
          (2/3:ℝ)*(1/(Nseq i:ℝ))^2 -
          (2/3:ℝ)*(1/(Nseq i:ℝ))^3 -
          (26/45:ℝ)*(1/(Nseq i:ℝ))^4) =O[Filter.atTop]
        (fun i => (1/(Nseq i:ℝ))^5)) := by
  refine ⟨manuscript_prop_variance_parity_contract N hN, ?_⟩
  intro Nseq Jseq hNseq hodd
  exact exact_variance_gap_fourth_expansion_along Nseq Jseq hNseq hodd

/-- Full typed contract for `odd:lem:PB`: the actual Jacobi/Bernoulli
factorization in tilt coordinates and the feasible variance region at every
interior mean. -/
theorem manuscript_odd_lem_PB_full_contract
    (j h r : ℕ) (hj : 0 < j) :
    (∀ t : ℝ, let N := j + (j + h) + r
      (∃ p : Fin (min (min (j+h) (N-(j+h))) (min j (N-j))) → unitInterval,
        (∀ i, 0 < (p i : ℝ) ∧ (p i : ℝ) < 1) ∧
        (hypergeomTiltMeasure N (j+h) j t).map
          (fun i : Fin (j+1) => (i : ℝ)) =
          (independentBernoulliMeasure p).map
            (fun x => ((j+h+j-N : ℕ) : ℝ) + ∑ i, x i)) ∧
      hypergeomMGF N (j+h) j t = hypergeomMGF N j (j+h) t ∧
      0 < hypergeomTiltMean N (j+h) j t ∧
      hypergeomTiltMean N (j+h) j t < j ∧
      0 < hypergeomTiltVariance N (j+h) j t ∧
      hypergeomTiltVariance N (j+h) j t ≤
        hypergeomTiltMean N (j+h) j t *
          ((j:ℝ)-hypergeomTiltMean N (j+h) j t)/j) ∧
    (∀ u : ℝ, 0 < u → u < (j:ℝ) →
      0 < manuscriptHypergeomVarianceAtMean (j+h) j r (by omega) hj u ∧
        manuscriptHypergeomVarianceAtMean (j+h) j r (by omega) hj u ≤
          u * ((j:ℝ)-u)/j) := by
  refine ⟨?_, ?_⟩
  · intro t
    exact manuscript_lem_PB_contract j h r hj t
  · intro u hu0 hum
    exact manuscript_odd_lem_PB_mean_contract (j+h) j r (by omega) hj hu0 hum

/-- The parity-uniform envelope theorem with its displayed normalized proxy
comparison and the odd-lattice consequence. -/
theorem manuscript_odd_envelope_full_contract
    (N k m : ℕ) (hN : 7 ≤ N) (hm : 3 ≤ m) (hmk : m ≤ k)
    (hkhalf : 2*k ≤ N) (hmhalf : 2*m < N) :
    (∀ t, hypergeomCenteredLogMGF N k m t ≤
      scaledBernoulliLogLaplace (envelopeM (N:ℝ) (m:ℝ))
        ((k:ℝ)/(N:ℝ)) (envelopeScale (N:ℝ) (m:ℝ)) t) ∧
    (∀ t, t ≠ 0 → hypergeomCenteredLogMGF N k m t <
      scaledBernoulliLogLaplace (envelopeM (N:ℝ) (m:ℝ))
        ((k:ℝ)/(N:ℝ)) (envelopeScale (N:ℝ) (m:ℝ)) t) ∧
    (2*k < N → hypergeomOptimalProxy N k m <
      envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) ∧
      normalizedHypergeomProxy N k m <
        (N:ℝ)/((N:ℝ)-1)*imbalanceFactor (1-2*(k:ℝ)/(N:ℝ))) ∧
    (2*k=N → hypergeomOptimalProxy N k m =
      envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) ∧
      normalizedHypergeomProxy N k m = (N:ℝ)/((N:ℝ)-1)) ∧
    (∀ n : ℕ, N=2*n+1 → 0<n → k≤n →
      (N:ℝ)/((N:ℝ)-1)*imbalanceFactor (1-2*(k:ℝ)/(N:ℝ)) ≤
        oddHypergeomConstant N) := by
  have h := manuscript_odd_envelope_contract N k m hN hm hmk hkhalf hmhalf
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · intro hkstrict
    have hkneq : 2*k ≠ N := by omega
    have hmNk : m≤N-k := by omega
    have hproxy := hypergeom_proxy_lt_scaled_bernoulli N k m
      (by omega) hmk hmNk hkneq
    have hnorm := normalizedHypergeomProxy_inner_lt_bernoulli N k m
      (by omega) hmk (by omega)
    exact ⟨hproxy, hnorm⟩
  · intro hbal
    have heven : Even N := by
      refine ⟨k, ?_⟩
      omega
    have hproxy := h.2.2.2 heven hbal
    have hnorm : normalizedHypergeomProxy N k m = (N:ℝ)/((N:ℝ)-1) := by
      rw [show N=2*k by omega]
      exact normalizedHypergeomProxy_even_attains k m (by omega) (by omega) (by omega)
    exact ⟨hproxy, hnorm⟩
  · intro n hNodd hn hkn
    have hkpos : 0<k := by omega
    have hbound := odd_imbalance_bound n k hn hkpos hkn
    rw [hNodd]
    exact hbound

end
end ExactHoeffding
