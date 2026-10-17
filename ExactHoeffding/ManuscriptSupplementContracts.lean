import ExactHoeffding.ManuscriptA1Contract
import ExactHoeffding.ManuscriptLaplaceContract
import ExactHoeffding.FactorialMinimizer
import ExactHoeffding.FactorialChernoffExact
import ExactHoeffding.IndividualMarginEndToEnd
import ExactHoeffding.OddCentralVariationalBoundary
import ExactHoeffding.PiecewiseKLComparison
import ExactHoeffding.ScaledKLGaussian
import ExactHoeffding.ScaledKLTaylor
import ExactHoeffding.PiecewiseKLRegularity
import ExactHoeffding.FiniteSupportLawLegendreCalculus
import ExactHoeffding.Cumulant23Taylor
import ExactHoeffding.ActualCumulant23Taylor
import ExactHoeffding.ActualProxyUniformTaylor
import ExactHoeffding.StationaryRadicalComparisons
import ExactHoeffding.BernoulliGapIdentities

open Set Filter
open scoped Topology

namespace ExactHoeffding
noncomputable section

/- The finite-law interface is already covered by the directly typed
`manuscript_A_integration_contract` in `ManuscriptA1Contract.lean`; it is
reused there, so this supplement file does not introduce a duplicate alias. -/
/-! `A:factorial` at lines 1560--1582 remains scope-qualified: its displayed
falling-factorial quotient lacks the condition `j ≤ N`, and its strict-rate
sentence omits `d ≤ m`. The separate supplementary cutoff statement at lines
1595--1601 explicitly assumes `μ < d ≤ min(k,m)` and is formalized below on
its stated supported domain. The broader A:factorial domain is not narrowed. -/

/-- Typed contract for the separate supported cutoff statement following
Proposition `A:factorial`: the displayed ceiling index is admissible and
minimizes every candidate, gives the exact optimized bound, characterizes the
adjacent ratio decrease, handles integral cutoff ties, and reaches the endpoint
at `d = min(k,m)`. -/
theorem manuscript_extra_A2_factorial_index_contract (N k m d : ℕ)
    (hmean : (k : ℝ) * m < (N : ℝ) * d)
    (hd0 : 0 < d) (hdm : d ≤ m) (hdk : d ≤ k)
    (hmkN : k + m ≤ N) :
    (hypergeomFactorialIndex N k m d =
      ⌈((N : ℝ) * d - (k : ℝ) * m) /
        ((N : ℝ) + d - k - m)⌉₊) ∧
    1 ≤ hypergeomFactorialIndex N k m d ∧
    hypergeomFactorialIndex N k m d ≤ d ∧
    (∀ j : ℕ, j ≤ d →
      hypergeomFactorialValue N k m d (hypergeomFactorialIndex N k m d) ≤
        hypergeomFactorialValue N k m d j) ∧
    finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d =
        hypergeomFactorialValue N k m d (hypergeomFactorialIndex N k m d) ∧
    (∀ j : ℕ, j + 1 ≤ d →
      (hypergeomFactorialValue N k m d (j + 1) ≤ hypergeomFactorialValue N k m d j ↔
        (j : ℝ) ≤ ((N : ℝ) * d - (k : ℝ) * m) /
          ((N : ℝ) + d - k - m))) ∧
    (∀ j : ℕ, j + 1 ≤ d →
      (j : ℝ) = ((N : ℝ) * d - (k : ℝ) * m) /
        ((N : ℝ) + d - k - m) →
      hypergeomFactorialValue N k m d (j + 1) =
        hypergeomFactorialValue N k m d j) ∧
    (d = min k m → hypergeomFactorialIndex N k m d = d) := by
  have hkN : k ≤ N := by omega
  have hmN : m ≤ N := by omega
  have hmem := hypergeomFactorialIndex_mem N k m d hmean hd0 hdm hdk hmkN
  refine ⟨rfl, hmem.1, hmem.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact hypergeomFactorialValue_index_min N k m d hmean hd0 hdm hdk hmkN j hj
  · exact hypergeomFactorialBound_eq_ceiling_candidate N k m d hkN hmN
      hmean hd0 hdm hdk hmkN
  · intro j hj
    exact hypergeomFactorialValue_succ_le_iff N k m d j hj hdm hdk hmkN
  · intro j hj hcut
    exact hypergeomFactorialValue_succ_eq_of_integral_cutoff
      N k m d j hj hdm hdk hmkN hcut
  · intro hend
    exact hypergeomFactorialIndex_eq_endpoint N k m d hd0 hdm hdk hmkN hend

/-- Typed contract for Corollary `cor:two_bern_envelope`, expressed using
`hypergeomOptimalProxy` for the left-hand optimal coefficient and the exact
Bernoulli optimal coefficient. It records strictness below balance and equality
at even balance. -/
theorem manuscript_cor_two_bern_envelope_contract (N k : ℕ)
    (hN : 5 ≤ N) (hk : 2 ≤ k) (hhalf : 2*k ≤ N) :
    hypergeomOptimalProxy N k 2 ≤
      (2*((N:ℝ)-2)/((N:ℝ)-1)) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) ∧
    (2*k < N → hypergeomOptimalProxy N k 2 <
      (2*((N:ℝ)-2)/((N:ℝ)-1)) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ))) ∧
    (2*k = N → hypergeomOptimalProxy N k 2 =
      (2*((N:ℝ)-2)/((N:ℝ)-1)) * bernoulliSharpBeta ((k:ℝ)/(N:ℝ))) := by
  have h := manuscript_main_laplace_two_draw_contract N k hN hk hhalf
  have hM : envelopeM (N:ℝ) (2:ℝ) = 2*((N:ℝ)-2)/((N:ℝ)-1) := by
    unfold envelopeM
    ring
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hM] using h.1
  · intro hstrict
    simpa only [hM] using h.2.2.1 hstrict
  · intro hbal
    have hp : (k:ℝ)/(N:ℝ) = (1/2:ℝ) := by
      have hcast : (2:ℝ)*(k:ℝ) = (N:ℝ) := by exact_mod_cast hbal
      field_simp [show (N:ℝ) ≠ 0 by exact_mod_cast (show N ≠ 0 by omega)]
      nlinarith
    have hbeta : bernoulliSharpBeta ((k:ℝ)/(N:ℝ)) = (1/4:ℝ) := by
      rw [hp, bernoulliSharpBeta_half]
    simpa only [hM, hbeta, mul_one_div] using (h.2.2.2 hbal).1

/-- Exact quantified individual-margin conclusion in Proposition
`B:individual`, including the positive parity-uniform gap and strict proxy
separation from the central value. -/
theorem manuscript_extra_B1_individual_margin_contract
    (N k m : ℕ) (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N)
    (hkc : k ≠ N/2) (hkc' : k ≠ N-N/2) :
    0 < individualMarginDelta N m ∧
      individualMarginDelta N m ≤ individualMarginGap N k m ∧
      hypergeomOptimalProxy N k m ≤ individualMarginW N m - individualMarginGap N k m ∧
      hypergeomOptimalProxy N k m ≤ individualMarginW N m - individualMarginDelta N m ∧
      hypergeomOptimalProxy N k m < individualMarginW N m :=
  hypergeomOptimalProxy_individualMargin_end_to_end N k m hN hk hkN hm hmN hkc hkc'

/-- Odd-central finite-sum variational formula and its attained nonzero
stationary optimizer, together with the deterministic boundary cases. -/
theorem manuscript_extra_B2_odd_central_interior_contract (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hmN : m < 2 * n + 1) :
    (∀ t : ℝ,
      hypergeomCenteredLogMGF (2 * n + 1) n m t =
        Real.log (oddCentralSupportedTiltSum n m t)) ∧
    (∃ t : ℝ, t ≠ 0 ∧
      (∀ u : ℝ, oddCentralSupportedProxy n m u ≤ oddCentralSupportedProxy n m t) ∧
      hypergeomOptimalProxy (2 * n + 1) n m = oddCentralSupportedProxy n m t ∧
      t * deriv (hypergeomCenteredLogMGF (2 * n + 1) n m) t =
        2 * hypergeomCenteredLogMGF (2 * n + 1) n m t) := by
  constructor
  · intro t
    exact oddCentral_logMGF_eq_supported_sum n m hn hmN.le t
  · exact oddCentral_supported_variational_maximum n m hn hm hmN

theorem manuscript_extra_B2_odd_central_boundary_contract (n m : ℕ)
    (hn : 0 < n) (hm : m = 0 ∨ m = 2 * n + 1) :
    ∀ t : ℝ, oddCentralSupportedProxy n m t = 0 :=
  oddCentralSupportedProxy_boundary_zero n m hn hm

/-- The complete quadratic comparison chain in the stated canonical
hypergeometric parameter domain. -/
theorem manuscript_extra_A_quadratic_chain_contract (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    let μ : ℝ := (m:ℝ)*k/N
    let M := envelopeM (N:ℝ) (m:ℝ)
    let IP := scaledKLRate M ((k:ℝ)/N) (envelopeScale (N:ℝ) (m:ℝ)) μ v
    let B := (v-μ)^2/(2*(M*bernoulliSharpBeta ((k:ℝ)/N)))
    let U := (v-μ)^2/(2*hypergeomUniformQuadraticVariance N m)
    IP ≤ canonicalPiecewiseRate N k m v ∧ B ≤ IP ∧ U ≤ B :=
  hypergeom_piecewise_gaussian_chain N k m hm hmk hk hhalf v hv0 hvm

/-- Mean-point derivatives and the analytic fourth-order expansion of the
scaled KL rate, with its order-five remainder. -/
theorem manuscript_extra_A_scaled_rate_Taylor_contract (M p a μ : ℝ)
    (hM : 0 < M) (hp : 0 < p) (hp1 : p < 1) (ha : 0 < a) :
    (let F := fun x => scaledKLRate M p a μ (μ + x)
     AnalyticAt ℝ F 0 ∧ F 0 = 0 ∧ deriv F 0 = 0 ∧
       iteratedDeriv 2 F 0 = 1 / (M * p * (1 - p)) ∧
       iteratedDeriv 3 F 0 = -a * (1 - 2 * p) / (M ^ 2 * p ^ 2 * (1 - p) ^ 2) ∧
       iteratedDeriv 4 F 0 =
         2 * a ^ 2 * (p ^ 3 + (1 - p) ^ 3) / (M ^ 3 * p ^ 3 * (1 - p) ^ 3)) ∧
    (∃ R, AnalyticAt ℝ R 0 ∧
      (∀ x : ℝ, scaledKLRate M p a μ (μ + x) =
        x ^ 2 / (2 * M * p * (1 - p)) -
          a * (1 - 2 * p) * x ^ 3 / (6 * M ^ 2 * p ^ 2 * (1 - p) ^ 2) +
          a ^ 2 * (p ^ 3 + (1 - p) ^ 3) * x ^ 4 /
            (12 * M ^ 3 * p ^ 3 * (1 - p) ^ 3) + x ^ 5 * R x) ∧
      (fun x => scaledKLRate M p a μ (μ + x) -
        (x ^ 2 / (2 * M * p * (1 - p)) -
          a * (1 - 2 * p) * x ^ 3 / (6 * M ^ 2 * p ^ 2 * (1 - p) ^ 2) +
          a ^ 2 * (p ^ 3 + (1 - p) ^ 3) * x ^ 4 /
            (12 * M ^ 3 * p ^ 3 * (1 - p) ^ 3))) =O[nhds 0] fun x => x ^ 5) := by
  exact ⟨scaledKLRate_target_mean_jets M p a μ hM hp hp1 ha,
    scaledKLRate_target_mean_quartic_expansion M p a μ hM hp hp1 ha⟩

/-- The actual canonical piecewise rate is C² on the manuscript's open
support; its curvature is the reciprocal of the smaller envelope. -/
theorem manuscript_extra_A_piecewise_C2_contract {N k m : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2 * k ≤ N) (hhalf : 2 * m < N) :
    ContDiffOn ℝ 2 (canonicalPiecewiseRate N k m) (Ioo 0 m) ∧
    (∀ v ∈ Ioo 0 m,
      HasDerivAt (canonicalPiecewiseRate N k m)
        (canonicalPiecewiseSlope N k m v) v ∧
      deriv (deriv (canonicalPiecewiseRate N k m)) v =
        1 / min (klQuadraticEnvelope N k m v) (klBinomialEnvelope m v)) ∧
    ContinuousOn (fun v =>
      1 / min (klQuadraticEnvelope N k m v) (klBinomialEnvelope m v)) (Ioo 0 m) := by
  refine ⟨canonicalPiecewiseRate_contDiffOn_two hm hmk hk hhalf, ?_,
    canonicalPiecewiseCurvature_continuousOn hm hmk hk hhalf⟩
  intro v hv
  exact ⟨canonicalPiecewiseRate_hasDerivAt hm hmk hk hhalf hv,
    canonicalPiecewiseRate_second_deriv hm hmk hk hhalf hv⟩

/-- Ordinary Legendre differentiation for the actual finite weighted law,
including the tilted-mean inverse and the mean-point identities. -/
theorem manuscript_extra_A_Legendre_derivatives_contract
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    {v : ℝ} (hvlo : L.value L.loIndex < v) (hvhi : v < L.value L.hiIndex) :
    (L.mean (L.rawMeanInverse v) + L.mean0 = v) ∧
    HasDerivAt L.rawMeanInverse (L.variance (L.rawMeanInverse v))⁻¹ v ∧
    deriv L.rawLegendreRate v = L.rawMeanInverse v ∧
    deriv (deriv L.rawLegendreRate) v = 1 / L.variance (L.rawMeanInverse v) := by
  exact ⟨L.rawMeanInverse_spec hvlo hvhi,
    L.rawMeanInverse_hasDerivAt hvlo hvhi,
    L.rawLegendreRate_deriv hvlo hvhi,
    L.rawLegendreRate_second_deriv hvlo hvhi⟩

theorem manuscript_extra_A_Legendre_mean_point_contract
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    L.rawLegendreRate L.mean0 = 0 ∧
    L.rawMeanInverse L.mean0 = 0 ∧
    deriv L.rawLegendreRate L.mean0 = 0 := by
  exact ⟨L.rawLegendreRate_at_mean0, L.rawMeanInverse_mean0,
    L.rawLegendreRate_deriv_at_mean0⟩

/-- The exact balanced cumulant expansions for hypergeometric sequences and
for the positive finite real-margin laws used to realize the expansions. -/
theorem manuscript_extra_appendix_cumulant23_remainders_contract
    (Ns ks : ℕ → ℕ) (m : ℕ) (s : ℝ)
    (hN : ∀ n, 0 < Ns n) (hk : ∀ n, ks n ≤ Ns n)
    (hm : ∀ n, m ≤ Ns n)
    (hs : ∀ n, (Ns n : ℝ) - 2 * (ks n : ℝ) = s)
    (hlim : Tendsto (fun n => (Ns n : ℝ)) atTop atTop) :
    ((fun n => hypergeomCumulant2 (Ns n) (ks n) m -
      hypergeomCumulant2Taylor m s (1 / (Ns n : ℝ))) =O[atTop]
        (fun n => (1 / (Ns n : ℝ)) ^ 5)) ∧
    ((fun n => hypergeomCumulant3 (Ns n) (ks n) m -
      hypergeomCumulant3Taylor m s (1 / (Ns n : ℝ))) =O[atTop]
        (fun n => (1 / (Ns n : ℝ)) ^ 4)) ∧
    ((fun e => finiteCumulant2 (Finset.range (m + 1)) (fun i => (i : ℝ))
      (realMarginMass m e ((1 - s * e) / 2)) - hypergeomCumulant2Taylor m s e) =O[nhds 0]
        (fun e => e ^ 5)) ∧
    ((fun e => finiteCumulant3 (Finset.range (m + 1)) (fun i => (i : ℝ))
      (realMarginMass m e ((1 - s * e) / 2)) - hypergeomCumulant3Taylor m s e) =O[nhds 0]
        (fun e => e ^ 4)) ∧
    ∀ᶠ e in nhds (0 : ℝ),
      scaledFalling 1 e m ≠ 0 ∧
      (∀ i ∈ Finset.range (m + 1), 0 < realMarginMass m e ((1 - s * e) / 2) i) ∧
      ∑ i ∈ Finset.range (m + 1), realMarginMass m e ((1 - s * e) / 2) i = 1 := by
  exact ⟨hypergeom_cumulant2_balanced_expansion Ns ks m s hN hk hm hs hlim,
    hypergeom_cumulant3_balanced_expansion Ns ks m s hN hk hm hs hlim,
    realMarginMass_cumulant2_balanced_expansion m s,
    realMarginMass_cumulant3_balanced_expansion m s,
    realMarginMass_balanced_curve_eventually_probability m s⟩

/-- Local analytic proxy Taylor expansion with a single joint radius in
population and tilt and an explicit continuous fifth-order remainder. -/
theorem manuscript_extra_appendix_proxy_uniform_Taylor_contract
    (m : ℕ) (hm : 1 ≤ m) (s : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ × ℝ → ℝ,
      Continuous R ∧
      ∀ e t : ℝ, |e| < δ → |t| < δ →
        rescaledProxyExtension m s e t =
          hypergeomRescaledCumulant2 m s e +
          hypergeomRescaledCumulant3 m s e / 3 * t +
          hypergeomRescaledCumulant4 m s e / 12 * t ^ 2 +
          hypergeomRescaledCumulant5 m s e / 60 * t ^ 3 +
          hypergeomRescaledCumulant6 m s e / 360 * t ^ 4 +
          t ^ 5 * R (e, t) :=
  rescaledProxyExtension_joint_uniform_taylor m hm s

/-- The three Case II radical comparisons in the manuscript's domain. -/
theorem manuscript_extra_stationary_q0_radicals_contract
    (j L A q : ℝ) (hj : 3 ≤ j) (hL : j - 1 ≤ L) (hq : 0 ≤ q)
    (hrel : A = j ^ 2 * (j - 1) - (L + j) * q ^ 2)
    (hsmall : A * L < j ^ 2) :
    stationaryQZero j L < q ∧
    j / L ≤ stationaryQZero j L ∧
    2 * j * (L - j + 1) ≤
      (L * (L + 1) - 2 * j) * stationaryQZero j L := by
  exact ⟨stationary_q_gt_qZero j L A q hj hL hq hrel hsmall,
    stationary_qZero_ge_div j L hj hL,
    stationary_E_mul_qZero_ge j L hj hL⟩

/-- Reflection, contact derivatives, and the exact second derivative of the
fixed-parameter Bernoulli proxy gap. -/
theorem manuscript_extra_Bernoulli_gap_display_identities_contract
    (p t : ℝ) (hp : 0 < p) (hp1 : p < 1 / 2) :
    bernoulliProxyGap p (2 * Real.log ((1 - p) / p) - t) = bernoulliProxyGap p t ∧
    deriv (bernoulliProxyGap p) 0 = 0 ∧
    deriv (bernoulliProxyGap p) (Real.log ((1 - p) / p)) = 0 ∧
    deriv (deriv (bernoulliProxyGap p)) t =
      bernoulliSharpBeta p -
        1 / (4 * Real.cosh ((t - Real.log ((1 - p) / p)) / 2) ^ 2) := by
  exact ⟨bernoulliProxyGap_reflection p t hp hp1,
    bernoulliProxyGap_deriv_zero p hp hp1,
    bernoulliProxyGap_deriv_logOdds p hp hp1,
    bernoulliProxyGap_second_derivative p t hp hp1⟩

end
end ExactHoeffding
