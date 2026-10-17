import ExactHoeffding.LaplaceEnvelopeTheorem
import ExactHoeffding.FinitePopulationBernoulliEnvelope
import ExactHoeffding.NormalizedProxy
import ExactHoeffding.BernoulliBalancedLimit

open Filter Set
open scoped Topology

namespace ExactHoeffding

/-- Independently transcribed contract for manuscript Theorem `thm:main_laplace`.
The first pair of clauses is the all-tilt scaled-Bernoulli comparison, with
strictness away from zero. The proxy clauses state the sub-half strict case,
the balanced equality case, and the normalized balanced value. The hypotheses
are exactly the theorem's integer parameter domain. -/
theorem manuscript_main_laplace_contract (N k m : ℕ)
    (hN : 7 ≤ N) (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N)
    (hhalf : 2*m < N) :
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
      normalizedHypergeomProxy N k m = (N:ℝ)/((N:ℝ)-1)) := by
  have hLap := hypergeom_laplace_envelope N k m hm hmk hk hhalf
  have hmN : m ≤ N := by omega
  have hk0 : 0 < k := by omega
  have hm2 : 2 ≤ m := by omega
  have hProxyEq (hbal : 2*k=N) :=
    hypergeom_proxy_eq_scaled_bernoulli_balanced N k m hk0 hbal hmN
  have hProxyStrict (hne : 2*k<N) :
      hypergeomOptimalProxy N k m <
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) :=
    hypergeom_proxy_lt_scaled_bernoulli_subhalf N k m hm2 hmk hne
  have hProxyLe : hypergeomOptimalProxy N k m ≤
      envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) := by
    by_cases hbal : 2*k=N
    · exact le_of_eq (hProxyEq hbal)
    · exact (hProxyStrict (by omega)).le
  have hProxyIff : (hypergeomOptimalProxy N k m =
      envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) ↔ 2*k=N) := by
    constructor
    · intro heq
      by_contra hne
      have hlt := hProxyStrict (by omega)
      exact (ne_of_lt hlt) heq
    · exact hProxyEq
  refine ⟨hLap.1, hLap.2, hProxyLe, hProxyIff, hProxyStrict, ?_⟩
  intro hbal
  have hNcast : (N:ℝ) = 2*(k:ℝ) := by exact_mod_cast hbal.symm
  have hp : (k:ℝ)/(N:ℝ) = 1/2 := by
    rw [hNcast]
    field_simp
  have hBeta : bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) = 1/4 := by
    rw [hp, bernoulliSharpBeta_half]
  have hEq := hProxyEq hbal
  have hProxy : hypergeomOptimalProxy N k m =
      envelopeM (N:ℝ) (m:ℝ) / 4 := by
    rw [hBeta] at hEq
    nlinarith [hEq]
  have hNorm : normalizedHypergeomProxy N k m =
      (N:ℝ)/((N:ℝ)-1) := by
    have hNeven : N=2*k := by omega
    subst N
    have hq : 0 < k := by omega
    have hm_lt : m < 2*k := by omega
    simpa using normalizedHypergeomProxy_even_attains k m hq (by omega) hm_lt
  exact ⟨hProxy, by rw [hBeta]; ring, hNorm⟩

/-- The same optimal-proxy comparison and equality classification stated in
Theorem `thm:main_laplace` for its separate two-draw case `m=2`, `N≥5`.
This records the balanced endpoint as well as every strict sub-half case. -/
theorem manuscript_main_laplace_two_draw_contract (N k : ℕ)
    (hN : 5 ≤ N) (hk : 2 ≤ k) (hhalf : 2*k ≤ N) :
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
      normalizedHypergeomProxy N k 2 = (N:ℝ)/((N:ℝ)-1)) := by
  have hProxyEq (hbal : 2*k=N) :=
    hypergeom_proxy_eq_scaled_bernoulli_balanced N k 2 (by omega) hbal (by omega)
  have hProxyStrict (hne : 2*k<N) :
      hypergeomOptimalProxy N k 2 <
        envelopeM (N:ℝ) (2:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) :=
    hypergeom_proxy_lt_scaled_bernoulli_subhalf N k 2 (by omega) (by omega) hne
  have hProxyLe : hypergeomOptimalProxy N k 2 ≤
      envelopeM (N:ℝ) (2:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) := by
    by_cases hbal : 2*k=N
    · exact le_of_eq (hProxyEq hbal)
    · exact (hProxyStrict (by omega)).le
  have hProxyIff : (hypergeomOptimalProxy N k 2 =
      envelopeM (N:ℝ) (2:ℝ) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) ↔ 2*k=N) := by
    constructor
    · intro heq
      by_contra hne
      exact (ne_of_lt (hProxyStrict (by omega))) heq
    · exact hProxyEq
  refine ⟨hProxyLe, hProxyIff, hProxyStrict, ?_⟩
  intro hbal
  have hNcast : (N:ℝ) = 2*(k:ℝ) := by exact_mod_cast hbal.symm
  have hp : (k:ℝ)/(N:ℝ) = 1/2 := by
    rw [hNcast]
    field_simp
  have hBeta : bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) = 1/4 := by
    rw [hp, bernoulliSharpBeta_half]
  have hEq := hProxyEq hbal
  have hProxy : hypergeomOptimalProxy N k 2 =
      envelopeM (N:ℝ) (2:ℝ) / 4 := by
    rw [hBeta] at hEq
    nlinarith [hEq]
  have hNorm : normalizedHypergeomProxy N k 2 =
      (N:ℝ)/((N:ℝ)-1) := by
    have hNeven : N=2*k := by omega
    subst N
    simpa using normalizedHypergeomProxy_even_attains k 2 (by omega) (by omega) (by omega)
  exact ⟨hProxy, by rw [hBeta]; ring, hNorm⟩

/-- Continuous balanced-scale endpoint of the comparison envelope. The
manuscript's strict theorem assumes `N>2m` (so its scale is positive); this
auxiliary limit records the continuous extension as that scale tends to zero. -/
theorem manuscript_scaled_envelope_balanced_limit_contract
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (M t : ℝ) :
    Tendsto (fun a : ℝ => scaledBernoulliLogLaplace M p a t)
      (𝓝[≠] (0:ℝ)) (𝓝 (M*p*(1-p)*t^2/2)) := by
  simpa [balancedBernoulliLogLaplace] using
    scaledBernoulliLogLaplace_tendsto_scale_zero_closed hp0 hp1 M t

end ExactHoeffding
