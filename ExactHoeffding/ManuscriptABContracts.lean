import ExactHoeffding.SharpCurvatureTheorem
import ExactHoeffding.FinitePopulationBernoulliEnvelope
import ExactHoeffding.CompactAnalyticHypergeomContraction
import ExactHoeffding.GoalBFixedSample
import ExactHoeffding.GoalBIndividualMargin
import ExactHoeffding.IndividualMarginEndToEnd
import ExactHoeffding.NormalizedProxy
import ExactHoeffding.OddCentralVariationalBoundary
import ExactHoeffding.OddCentralStrict
import ExactHoeffding.OddCentralSupportFormula
import ExactHoeffding.OddCentralVariationalMaximum
import ExactHoeffding.PiecewiseKLStrict
import ExactHoeffding.OptimalProxyFourthExpansion
import ExactHoeffding.ActualUniqueOptimizer
import ExactHoeffding.PublicFormulaClosure
import ExactHoeffding.TwoDrawSingletonComparison

/-!
# Typed proposition contracts for selected Main A and Goal B results

These declarations assemble existing kernel-checked results into propositions
that state the corresponding manuscript conclusions at their actual parameter
domains. The fourth-order optimizer-location and proxy-value expansions are
assembled in `ManuscriptAsymptoticsContract.lean` from the joint fourth-order
analytic theorem.
-/

namespace ExactHoeffding
noncomputable section
open Filter Asymptotics
open scoped Topology

/-- The exact-input statement of Proposition `B:inputs`, including the actual
finite-law proxy bound and the complete success/sample complement symmetries. -/
theorem manuscript_B_inputs_contract (N k m : ℕ)
    (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N) :
    (∀ t : ℝ,
      hypergeomTiltVariance N k m t ≤ sharpCurvatureConstant N k m) ∧
    hypergeomOptimalProxy N k m ≤ sharpCurvatureConstant N k m ∧
    (m ≤ k → m ≤ N-k → 2 ≤ m →
      hypergeomOptimalProxy N k m ≤
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) ∧
      (hypergeomOptimalProxy N k m =
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) ↔ 2*k=N)) ∧
    (m=1 → hypergeomOptimalProxy N k m =
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N)) ∧
    hypergeomOptimalProxy N k m = hypergeomOptimalProxy N (N-k) m ∧
    hypergeomOptimalProxy N k m = hypergeomOptimalProxy N m k ∧
    hypergeomOptimalProxy N k m = hypergeomOptimalProxy N k (N-m) := by
  have hcurv := hypergeomTiltVariance_sharp N k m hkN.le hmN.le
  have hproxy := hypergeomOptimalProxy_le_curvature N k m hkN.le hmN.le
  have hcomp (hmk : m ≤ k) (hmNk : m ≤ N-k) (hm2 : 2 ≤ m) :
      hypergeomOptimalProxy N k m ≤
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) ∧
      (hypergeomOptimalProxy N k m =
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) ↔ 2*k=N) :=
    ⟨hypergeom_proxy_le_scaled_bernoulli N k m hm2 hmk hmNk,
      hypergeom_proxy_scaled_bernoulli_equality_iff N k m hm2 hmk hmNk⟩
  have hsingle : m=1 → hypergeomOptimalProxy N k m =
      envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) := by
    intro hm1
    subst m
    have h := hypergeomOptimalProxy_singleton_bernoulliSharpBeta N k (by omega) hkN.le
    rw [h]
    unfold envelopeM
    norm_num
    have hN0 : (N:ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hN1 : (N:ℝ)-1 ≠ 0 := by
      have hN1' : (1:ℝ) < (N:ℝ) := by exact_mod_cast (show 1<N by omega)
      linarith
    field_simp [hN0, hN1]
  exact ⟨hcurv, ⟨hproxy, ⟨hcomp, ⟨hsingle,
    ⟨hypergeomOptimalProxy_success_complement N k m hkN.le hmN.le (by omega),
      ⟨hypergeomOptimalProxy_transpose N k m hkN.le hmN.le,
        hypergeomOptimalProxy_sample_complement N k m hkN.le hmN.le (by omega)⟩⟩⟩⟩⟩⟩

/-- Strict cubic inverse-hyperbolic-tangent and proxy consequences of
Lemma `B:atanh`, with the full open parameter interval. -/
theorem manuscript_B_atanh_contract (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    d + d^3/3 < Real.artanh d ∧
    d/(4*Real.artanh d) < 1/(4*(1+d^2/3)) :=
  ⟨real_artanh_cubic_strict_lower d hd0 hd1,
    bernoulli_cubic_proxy_strict_upper d hd0 hd1⟩

/-- The actual proxy, both branches of the individual-margin certificate,
its positive parity gap, and the outward monotonicity of the first branch. -/
theorem manuscript_B_individual_contract (N k m : ℕ)
    (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N)
    (hkc : k ≠ N/2) (hkc' : k ≠ N-N/2) :
    (0 < individualMarginDelta N m ∧
      individualMarginDelta N m ≤ individualMarginGap N k m ∧
      hypergeomOptimalProxy N k m ≤ individualMarginW N m - individualMarginGap N k m ∧
      hypergeomOptimalProxy N k m ≤ individualMarginW N m - individualMarginDelta N m ∧
      hypergeomOptimalProxy N k m < individualMarginW N m) ∧
    (∀ W M d₁ d₂ : ℝ, 0 ≤ M → 0 ≤ d₁ → d₁ ≤ d₂ →
      W - M/(4*(1+d₁^2/3)) ≤ W - M/(4*(1+d₂^2/3))) := by
  exact ⟨hypergeomOptimalProxy_individualMargin_end_to_end N k m hN hk hkN hm hmN hkc hkc',
    individualMargin_first_branch_gap_mono⟩

/-- All-size fixed-sample extremizers and the exact positive margin deficit,
using `individualMarginGap` for the two displayed branches of `G`. -/
theorem manuscript_B_main_contract (N k m : ℕ)
    (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N) :
    (hypergeomOptimalProxy N k m ≤ hypergeomOptimalProxy N (N/2) m ∧
      (hypergeomOptimalProxy N k m = hypergeomOptimalProxy N (N/2) m ↔
        k = N/2 ∨ k = N-N/2)) ∧
    ∀ hkc : k ≠ N/2, ∀ hkc' : k ≠ N-N/2,
      0 < individualMarginDelta N m ∧
      individualMarginDelta N m ≤ individualMarginGap N k m ∧
      hypergeomOptimalProxy N k m ≤ individualMarginW N m - individualMarginGap N k m ∧
      hypergeomOptimalProxy N k m ≤ individualMarginW N m - individualMarginDelta N m ∧
      hypergeomOptimalProxy N k m < individualMarginW N m := by
  refine ⟨hypergeomOptimalProxy_fixed_sample_extremizers N k m hN hk hkN hm hmN, ?_⟩
  intro hkc hkc'
  exact hypergeomOptimalProxy_individualMargin_end_to_end N k m hN hk hkN hm hmN hkc hkc'

/-- Even-population proxy maximum, equality classification, and its closed
form and zero-tilt variance value. -/
theorem manuscript_B_even_contract (q k m : ℕ)
    (hq : 0 < q) (hk : 0 < k) (hkN : k < 2*q)
    (hm : 0 < m) (hmN : m < 2*q) :
    (hypergeomOptimalProxy (2*q) k m ≤ hypergeomOptimalProxy (2*q) q m ∧
      (hypergeomOptimalProxy (2*q) k m = hypergeomOptimalProxy (2*q) q m ↔ k=q)) ∧
    hypergeomOptimalProxy (2*q) q m =
      (m:ℝ) * (((2*q:ℕ):ℝ)-(m:ℝ)) / (4*(((2*q:ℕ):ℝ)-1)) ∧
    hypergeomTiltVariance (2*q) q m 0 = hypergeomOptimalProxy (2*q) q m := by
  have hmax := hypergeomOptimalProxy_fixed_sample_extremizers_even q k m hq hk hkN hm hmN
  have hnorm := normalizedHypergeomProxy_even_attains q m hq hm hmN
  have hS : hypergeomOptimalProxy (2*q) q m =
      (m:ℝ) * (((2*q:ℕ):ℝ)-(m:ℝ)) / (4*(((2*q:ℕ):ℝ)-1)) := by
    unfold normalizedHypergeomProxy at hnorm
    have hqR : (0:ℝ) < ((2*q:ℕ):ℝ) := by positivity
    have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
    have hmq : (m:ℝ) < ((2*q:ℕ):ℝ) := by
      exact_mod_cast (show m<2*q by omega)
    have hmqR : (0:ℝ) < ((2*q:ℕ):ℝ)-(m:ℝ) := sub_pos.mpr hmq
    have hden : (m:ℝ)*(((2*q:ℕ):ℝ)-(m:ℝ)) ≠ 0 := (mul_pos hmR hmqR).ne'
    have hN1 : ((2*q:ℕ):ℝ)-1 ≠ 0 := by
      have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq
      push_cast
      linarith
    field_simp [hden, hN1, hqR.ne'] at hnorm ⊢
    nlinarith [hnorm]
  have hvar : hypergeomTiltVariance (2*q) q m 0 =
      (m:ℝ) * (((2*q:ℕ):ℝ)-(m:ℝ)) / (4*(((2*q:ℕ):ℝ)-1)) := by
    rw [hypergeomTiltVariance_zero_balanced_marks q m hq (by omega)]
  exact ⟨hmax, ⟨hS, hvar.trans hS.symm⟩⟩

/-- Odd-central finite-sum variational formula: its continuous-at-zero
support proxy attains the actual optimal coefficient at a nonzero tilt,
strictly above the ordinary variance; all odd fixed-sample equalities are
classified without assuming uniqueness of the maximizing tilt. -/
theorem manuscript_B_odd_contract (n k m : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkN : k < 2*n+1)
    (hm : 0 < m) (hmN : m < 2*n+1) :
    (hypergeomOptimalProxy (2*n+1) k m ≤ hypergeomOptimalProxy (2*n+1) n m ∧
      (hypergeomOptimalProxy (2*n+1) k m = hypergeomOptimalProxy (2*n+1) n m ↔
        k=n ∨ k=n+1)) ∧
    hypergeomCumulant2 (2*n+1) n m < hypergeomOptimalProxy (2*n+1) n m ∧
    (∀ t : ℝ, oddCentralSupportedProxy n m t =
      actualHypergeomProxy (2*n+1) n m t) ∧
    ∃ t : ℝ, t ≠ 0 ∧
      (∀ u : ℝ, oddCentralSupportedProxy n m u ≤ oddCentralSupportedProxy n m t) ∧
      hypergeomOptimalProxy (2*n+1) n m = oddCentralSupportedProxy n m t ∧
      t * deriv (hypergeomCenteredLogMGF (2*n+1) n m) t =
        2 * hypergeomCenteredLogMGF (2*n+1) n m t := by
  refine ⟨hypergeomOptimalProxy_fixed_sample_extremizers_odd n k m hn hk hkN hm hmN,
    ⟨hypergeomOptimalProxy_odd_center_gt_variance n m hn hm hmN,
      ⟨?_, ?_⟩⟩⟩
  · intro t
    exact oddCentralSupportedProxy_eq_actual n m hn hmN.le t
  · exact oddCentral_supported_variational_maximum n m hn hm hmN

/-- Odd one- and two-draw closed forms, their failure-count complements,
and all maximizing success margins. -/
theorem manuscript_B_small_contract (n k : ℕ)
    (hn : 2 ≤ n) (hk : 0 < k) (hkN : k < 2*n+1) :
    (hypergeomOptimalProxy (2*n+1) k 1 ≤ hypergeomOptimalProxy (2*n+1) n 1 ∧
      (hypergeomOptimalProxy (2*n+1) k 1 = hypergeomOptimalProxy (2*n+1) n 1 ↔
        k=n ∨ k=n+1)) ∧
    (hypergeomOptimalProxy (2*n+1) k (2*n) ≤ hypergeomOptimalProxy (2*n+1) n (2*n) ∧
      (hypergeomOptimalProxy (2*n+1) k (2*n) = hypergeomOptimalProxy (2*n+1) n (2*n) ↔
        k=n ∨ k=n+1)) ∧
    (hypergeomOptimalProxy (2*n+1) k 2 ≤ hypergeomOptimalProxy (2*n+1) n 2 ∧
      (hypergeomOptimalProxy (2*n+1) k 2 = hypergeomOptimalProxy (2*n+1) n 2 ↔
        k=n ∨ k=n+1)) ∧
    (hypergeomOptimalProxy (2*n+1) k (2*n-1) ≤ hypergeomOptimalProxy (2*n+1) n (2*n-1) ∧
      (hypergeomOptimalProxy (2*n+1) k (2*n-1) = hypergeomOptimalProxy (2*n+1) n (2*n-1) ↔
        k=n ∨ k=n+1)) ∧
    hypergeomOptimalProxy (2*n+1) n 1 =
      1/(2*((2*n+1:ℕ):ℝ)*Real.log ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-1))) ∧
    hypergeomOptimalProxy (2*n+1) n (2*n) =
      1/(2*((2*n+1:ℕ):ℝ)*Real.log ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-1))) ∧
    hypergeomOptimalProxy (2*n+1) n 2 =
      2/(((2*n+1:ℕ):ℝ)*Real.log ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-3))) ∧
    hypergeomOptimalProxy (2*n+1) n (2*n-1) =
      2/(((2*n+1:ℕ):ℝ)*Real.log ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-3))) := by
  have hmain (r : ℕ) (hr : 0 < r) (hrN : r < 2*n+1) :=
    hypergeomOptimalProxy_fixed_sample_extremizers_odd n k r (by omega) (by omega) hkN hr hrN
  have h1 := hmain 1 (by omega) (by omega)
  have hN1 := hmain (2*n) (by omega) (by omega)
  have h2 := hmain 2 (by omega) (by omega)
  have hN2 := hmain (2*n-1) (by omega) (by omega)
  have hval1 : hypergeomOptimalProxy (2*n+1) n 1 =
      1/(2*((2*n+1:ℕ):ℝ)*Real.log ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-1))) := by
    rw [hypergeomOptimalProxy_singleton_subhalf (2*n+1) n (by omega) (by omega)]
    have hratio :
        (1-(n:ℝ)/((2*n+1:ℕ):ℝ))/((n:ℝ)/((2*n+1:ℕ):ℝ)) =
          ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-1)) := by
      push_cast
      have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
      field_simp
      <;> ring
    rw [hratio]
    have hN : (2*n+1:ℕ) ≠ 0 := by omega
    push_cast
    have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hNR : (0:ℝ) < (2*n+1:ℕ) := by positivity
    have hlog : Real.log ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-1)) ≠ 0 := by
      apply ne_of_gt
      apply Real.log_pos
      have hnR' : (1:ℝ) < n := by exact_mod_cast (show 1<n by omega)
      apply (one_lt_div (show (0:ℝ)<((2*n+1:ℕ):ℝ)-1 by push_cast; linarith)).2
      push_cast
      nlinarith
    field_simp [hlog, hNR.ne']
    <;> ring
  have hval2 : hypergeomOptimalProxy (2*n+1) n 2 =
      2/(((2*n+1:ℕ):ℝ)*Real.log ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-3))) := by
    rw [hypergeomOptimalProxy_two_draw (2*n+1) n (by omega) (by omega),
      hypergeom_two_draw_odd_max_value n hn]
    have hratio : (((n:ℝ)+1)/((n:ℝ)-1)) =
        ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-3)) := by
      push_cast
      have hn1 : (n:ℝ)-1 ≠ 0 := by
        have hnR : (1:ℝ) < n := by exact_mod_cast (show 1<n by omega)
        linarith
      have hnumEq : 2*(n:ℝ)+1+1 = 2*((n:ℝ)+1) := by ring
      have hdenEq : 2*(n:ℝ)+1-3 = 2*((n:ℝ)-1) := by ring
      rw [hnumEq, hdenEq]
      field_simp [hn1]
    rw [hratio]
  have hsample1 := hypergeomOptimalProxy_sample_complement (2*n+1) n 1
    (by omega) (by omega) (by omega)
  have hsample2 := hypergeomOptimalProxy_sample_complement (2*n+1) n 2
    (by omega) (by omega) (by omega)
  have hvalN1 : hypergeomOptimalProxy (2*n+1) n (2*n) =
      1/(2*((2*n+1:ℕ):ℝ)*Real.log ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-1))) := by
    calc
      hypergeomOptimalProxy (2*n+1) n (2*n) = hypergeomOptimalProxy (2*n+1) n 1 := by
        simpa [show 2*n+1-1=2*n by omega] using hsample1.symm
      _ = _ := hval1
  have hvalN2 : hypergeomOptimalProxy (2*n+1) n (2*n-1) =
      2/(((2*n+1:ℕ):ℝ)*Real.log ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-3))) := by
    calc
      hypergeomOptimalProxy (2*n+1) n (2*n-1) = hypergeomOptimalProxy (2*n+1) n 2 := by
        simpa [show 2*n+1-2=2*n-1 by omega] using hsample2.symm
      _ = _ := hval2
  exact ⟨h1, ⟨hN1, ⟨h2, ⟨hN2, ⟨hval1, ⟨hvalN1, ⟨hval2, hvalN2⟩⟩⟩⟩⟩⟩⟩

/-- Actual finite-law piecewise KL theorem on the manuscript's entire stated
parameter domain, including both tails, strict improvements, and exact
quadratic-comparison equality region. -/
theorem manuscript_A_piecewise_contract (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    let μ : ℝ := (m:ℝ)*k/N
    let J := canonicalPiecewiseRate N k m v
    let IP := scaledKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) μ v
    (μ ≤ v → (∑ i ∈ Finset.range (m+1),
      if v ≤ (i:ℝ) then hypergeomMass N k m i else 0) ≤ Real.exp (-J)) ∧
    (v ≤ μ → (∑ i ∈ Finset.range (m+1),
      if (i:ℝ) ≤ v then hypergeomMass N k m i else 0) ≤ Real.exp (-J)) ∧
    (v ≠ μ → m*bernoulliKL ((k:ℝ)/N) (v/m) < J ∧ J < hypergeomKLRate N k m v) ∧
    IP ≤ J ∧ (IP = J ↔ varianceSwitchMinus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m) ≤ v ∧
      v ≤ varianceSwitchPlus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)) ∧
    (IP < J ↔ v < varianceSwitchMinus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m) ∨
      varianceSwitchPlus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m) < v) :=
  hypergeom_piecewise_kl_end_to_end N k m hm hmk hk hhalf v hv0 hvm

/-- The fourth-order fixed-sample singleton-gap limit in the manuscript's
odd central regime. It records the expansion with its exact positive leading
coefficient; it is not inferred merely from a coefficient heuristic. -/
theorem manuscript_cor_fixedm_gap_limit_contract (m : ℕ) (hm : 2 ≤ m)
    (N J : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hodd : ∀ᶠ n in atTop, N n = 2*J n + 1) :
    Tendsto (fun n =>
      (oddHypergeomConstant (N n) - normalizedHypergeomProxy (N n) (J n) m -
        2*((m:ℝ)-1)/3*(1/(N n:ℝ))^3)/(1/(N n:ℝ))^4)
      atTop (𝓝 (2*((m:ℝ)-1)*(2*(m:ℝ)+1)/3)) := by
  have hmpos : 0 < m := by omega
  exact odd_nearly_balanced_gap_fourth_limit_along m hmpos N J hN hodd

end
end ExactHoeffding
