import ExactHoeffding.ManuscriptLaplaceContract
import ExactHoeffding.ManuscriptABContracts
import ExactHoeffding.ManuscriptSupplementContracts
import ExactHoeffding.ManuscriptTwoDrawContract
import ExactHoeffding.OptimalProxyFourthExpansion

namespace ExactHoeffding
noncomputable section
open Filter Asymptotics
open scoped Topology

/-- Unified contract for the two parameter regimes stated in the main
hypergeometric Laplace theorem: the all-tilt result for m ≥ 3 and the
separately stated two-draw proxy result. -/
theorem manuscript_main_laplace_full_contract :
    (∀ N k m : ℕ, 7 ≤ N → 3 ≤ m → m ≤ k → 2*k ≤ N → 2*m < N →
      (∀ t : ℝ,
        hypergeomCenteredLogMGF N k m t ≤
          scaledBernoulliLogLaplace (envelopeM (N:ℝ) (m:ℝ))
            ((k:ℝ)/(N:ℝ)) (envelopeScale (N:ℝ) (m:ℝ)) t) ∧
      (∀ t : ℝ, t ≠ 0 →
        hypergeomCenteredLogMGF N k m t <
          scaledBernoulliLogLaplace (envelopeM (N:ℝ) (m:ℝ))
            ((k:ℝ)/(N:ℝ)) (envelopeScale (N:ℝ) (m:ℝ)) t) ∧
      hypergeomOptimalProxy N k m ≤
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) ∧
      (hypergeomOptimalProxy N k m =
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) ↔ 2*k=N) ∧
      (2*k<N → hypergeomOptimalProxy N k m <
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ))) ∧
      (2*k=N →
        hypergeomOptimalProxy N k m = envelopeM (N:ℝ) (m:ℝ) / 4 ∧
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) =
          envelopeM (N:ℝ) (m:ℝ) / 4 ∧
        normalizedHypergeomProxy N k m = (N:ℝ)/((N:ℝ)-1))) ∧
    (∀ N k : ℕ, 5 ≤ N → 2 ≤ k → 2*k ≤ N →
      hypergeomOptimalProxy N k 2 ≤
        envelopeM (N:ℝ) (2:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) ∧
      (hypergeomOptimalProxy N k 2 =
        envelopeM (N:ℝ) (2:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) ↔ 2*k=N) ∧
      (2*k<N → hypergeomOptimalProxy N k 2 <
        envelopeM (N:ℝ) (2:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ))) ∧
      (2*k=N →
        hypergeomOptimalProxy N k 2 = envelopeM (N:ℝ) (2:ℝ) / 4 ∧
        envelopeM (N:ℝ) (2:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) =
          envelopeM (N:ℝ) (2:ℝ) / 4 ∧
        normalizedHypergeomProxy N k 2 = (N:ℝ)/((N:ℝ)-1))) := by
  constructor
  · intro N k m hN hm hmk hk hhalf
    exact manuscript_main_laplace_contract N k m hN hm hmk hk hhalf
  · intro N k hN hk hhalf
    exact manuscript_main_laplace_two_draw_contract N k hN hk hhalf

/-- Full odd two-draw result, including its extremizer classification and
closed constants together with the stated asymptotic gap. -/
theorem manuscript_prop_odd2_semantic_contract (n : ℕ) (hn : 2 ≤ n) :
    manuscriptPropOdd2FiniteStatement n ∧ manuscriptPropOdd2GapStatement :=
  manuscript_prop_odd2_full_contract n hn

/-- Unified contract for the complete fixed-m singleton-gap corollary.  It
includes the central fourth-order expansion, the fixed off-balance second-
order expansion, and the eventual strict comparison for every fixed s ≥ 3. -/
theorem manuscript_cor_fixedm_gap_full_contract
    (m : ℕ) (hm : 2 ≤ m) (N J K : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hodd : ∀ᶠ n in atTop, N n = 2 * J n + 1)
    (s : ℝ) (hs : 3 ≤ s)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ)) :
    (fun n => oddHypergeomConstant (N n) - normalizedHypergeomProxy (N n) (J n) m -
      2*((m:ℝ)-1)/3*(1/(N n:ℝ))^3 -
      2*((m:ℝ)-1)*(2*(m:ℝ)+1)/3*(1/(N n:ℝ))^4)
      =O[atTop] (fun n => (1/(N n:ℝ))^5) ∧
    Tendsto (fun n =>
      (oddHypergeomConstant (N n) - normalizedHypergeomProxy (N n) (J n) m -
        2*((m:ℝ)-1)/3*(1/(N n:ℝ))^3)/(1/(N n:ℝ))^4)
      atTop (𝓝 (2*((m:ℝ)-1)*(2*(m:ℝ)+1)/3)) ∧
    (fun n => oddHypergeomConstant (N n) -
      normalizedHypergeomProxy (N n) (K n) m -
      (s^2-1)/3*(1/(N n:ℝ))^2)
      =O[atTop] (fun n => (1/(N n:ℝ))^3) ∧
    (∀ᶠ n in atTop,
      normalizedHypergeomProxy (N n) (J n) m < oddHypergeomConstant (N n)) ∧
    ∀ᶠ n in atTop,
      normalizedHypergeomProxy (N n) (K n) m < oddHypergeomConstant (N n) := by
  have hcenter := odd_nearly_balanced_gap_fourth_expansion_along m (by omega) N J hN hodd
  have hcenterLimit := manuscript_cor_fixedm_gap_limit_contract m hm N J hN hodd
  have hcenterCoeff : 0 < 2*((m:ℝ)-1)*(2*(m:ℝ)+1)/3 := by
    have hmR : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hm1 : 0 < (m:ℝ) - 1 := by linarith
    have hplus : 0 < 2*(m:ℝ)+1 := by positivity
    positivity
  have hcenterEventuallyPos : ∀ᶠ n in atTop,
      0 < (oddHypergeomConstant (N n) -
        normalizedHypergeomProxy (N n) (J n) m -
        2*((m:ℝ)-1)/3*(1/(N n:ℝ))^3)/(1/(N n:ℝ))^4 :=
    hcenterLimit.eventually (eventually_gt_nhds hcenterCoeff)
  have hcenterStrict : ∀ᶠ n in atTop,
      normalizedHypergeomProxy (N n) (J n) m < oddHypergeomConstant (N n) := by
    filter_upwards [hcenterEventuallyPos, hN.eventually (eventually_ge_atTop 2)]
      with n hratio hlarge
    have hNpos : 0 < (N n:ℝ) := by exact_mod_cast (show 0 < N n by omega)
    have hden : 0 < (1/(N n:ℝ))^4 := by positivity
    have hnum : 0 < oddHypergeomConstant (N n) -
        normalizedHypergeomProxy (N n) (J n) m -
        2*((m:ℝ)-1)/3*(1/(N n:ℝ))^3 := by
      simpa using (lt_div_iff₀ hden).mp hratio
    have hmR : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (show 1 ≤ m by omega)
    have hmfac : 0 ≤ 2*((m:ℝ)-1)/3 := by positivity
    have hinv : 0 ≤ 1/(N n:ℝ) := by positivity
    have hcubic : 0 ≤ 2*((m:ℝ)-1)/3*(1/(N n:ℝ))^3 :=
      mul_nonneg hmfac (pow_nonneg hinv 3)
    linarith
  have hoff := odd_singleton_gap_second_expansion_along m (by omega) s
    (by linarith) N K J hN hvalid hodd
  have hstrict := odd_singleton_gap_eventually_pos_along m (by omega) s
    (by linarith) N K J hN hvalid hodd
  exact ⟨hcenter, ⟨hcenterLimit, ⟨hoff, ⟨hcenterStrict, hstrict⟩⟩⟩⟩

/-- Unified interior and degenerate-boundary contract for the odd-central
finite-sum representation and its nonzero optimal stationary tilt. -/
theorem manuscript_extra_B2_odd_central_full_contract (n m : ℕ)
    (hn : 0 < n) :
    (0 < m → m < 2*n+1 →
      (∀ t : ℝ,
        hypergeomCenteredLogMGF (2*n+1) n m t =
          Real.log (oddCentralSupportedTiltSum n m t)) ∧
      (∃ t : ℝ, t ≠ 0 ∧
        (∀ u : ℝ, oddCentralSupportedProxy n m u ≤ oddCentralSupportedProxy n m t) ∧
        hypergeomOptimalProxy (2*n+1) n m = oddCentralSupportedProxy n m t ∧
        t * deriv (hypergeomCenteredLogMGF (2*n+1) n m) t =
          2 * hypergeomCenteredLogMGF (2*n+1) n m t)) ∧
    (m = 0 ∨ m = 2*n+1 →
      ∀ t : ℝ, oddCentralSupportedProxy n m t = 0) := by
  constructor
  · intro hm hmN
    exact manuscript_extra_B2_odd_central_interior_contract n m hn hm hmN
  · intro hm
    exact manuscript_extra_B2_odd_central_boundary_contract n m hn hm

/-- Unified Legendre-calculus contract including the mean-point value,
inverse, and derivative identities in addition to the interior derivatives. -/
theorem manuscript_extra_A_Legendre_derivatives_full_contract
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    (L.rawLegendreRate L.mean0 = 0 ∧
      L.rawMeanInverse L.mean0 = 0 ∧
      deriv L.rawLegendreRate L.mean0 = 0) ∧
    ∀ v : ℝ, L.value L.loIndex < v → v < L.value L.hiIndex →
      (L.mean (L.rawMeanInverse v) + L.mean0 = v) ∧
      HasDerivAt L.rawMeanInverse (L.variance (L.rawMeanInverse v))⁻¹ v ∧
      deriv L.rawLegendreRate v = L.rawMeanInverse v ∧
      deriv (deriv L.rawLegendreRate) v =
        1 / L.variance (L.rawMeanInverse v) := by
  refine ⟨manuscript_extra_A_Legendre_mean_point_contract L, ?_⟩
  intro v hvlo hvhi
  exact manuscript_extra_A_Legendre_derivatives_contract L hvlo hvhi

end
end ExactHoeffding
