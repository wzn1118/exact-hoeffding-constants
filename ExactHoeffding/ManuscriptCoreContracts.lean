import ExactHoeffding.TwoLevelExistence
import ExactHoeffding.HypergeomBernoulliLaw
import ExactHoeffding.HypergeometricODEMargins
import ExactHoeffding.StationaryPositiveBranch
import ExactHoeffding.PublicFormulaClosure
import ExactHoeffding.StationaryCertificates
import ExactHoeffding.CanonicalCurvatureComplete
import ExactHoeffding.ExchangeableVarianceSupremum
import ExactHoeffding.ExplicitExtremizerTheorem
import ExactHoeffding.TwoDrawProxyComplete
import ExactHoeffding.FixedSampleExtrema
import ExactHoeffding.TwoDrawComparison
import ExactHoeffding.TwoDrawSingletonComparison
import ExactHoeffding.LaplaceEnvelopeTheorem
import ExactHoeffding.BernoulliOptimal
import ExactHoeffding.FinitePopulationBernoulliEnvelope
import ExactHoeffding.HypergeometricBarrier
import ExactHoeffding.ExactOddGlobalTheorem
import ExactHoeffding.FiniteSupportRecurrenceBridge
import ExactHoeffding.FiniteSupportLegendreCalculus
import ExactHoeffding.OptimalProxyAsymptotics
import ExactHoeffding.OddHypergeomExtremizers
import Mathlib.Analysis.Real.Sqrt

/-!
# Typed contracts for the frozen paper's core analysis results

Each theorem below records the paper result as a proposition over the actual
finite hypergeometric law or the exact polynomial objects used in the proof.
The declarations are assembled from the corresponding kernel-checked results.
-/

namespace ExactHoeffding
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

/-- The actual canonical hypergeometric masses as a positive recurrence law.
This gives a single inverse mean parameter for all statements below. -/
noncomputable def manuscriptHypergeomRecurrenceLaw
    (k m r : ℕ) (hmk : m ≤ k) : RealRecurrenceLaw where
  degree := m
  marks := (k : ℝ)
  remainder := (r : ℝ)
  mass := hypergeomMass (k + m + r) k m
  marks_ge := by exact_mod_cast hmk
  remainder_nonneg := Nat.cast_nonneg r
  mass_pos := by
    intro i hi
    exact hypergeomMass_pos_canonical k m r i hmk hi
  mass_total := hypergeomMass_total (k + m + r) k m (by omega) (by omega)
  adjacent := by
    intro i hi
    exact hypergeomMass_adjacent_real k m r i hmk hi

/-- The unique exponential tilt that realizes a prescribed interior mean. -/
noncomputable def manuscriptHypergeomTiltAtMean
    (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m) (u : ℝ) : ℝ :=
  finiteSupportMeanInverse
    ((manuscriptHypergeomRecurrenceLaw k m r hmk).toFiniteSupportTiltCurve
      (by exact_mod_cast hm)) u

/-- The actual hypergeometric variance expressed in its mean coordinate. -/
noncomputable def manuscriptHypergeomVarianceAtMean
    (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m) (u : ℝ) : ℝ :=
  (manuscriptHypergeomRecurrenceLaw k m r hmk).variance
    (manuscriptHypergeomTiltAtMean k m r hmk hm u)

@[simp] theorem manuscriptHypergeomTiltAtMean_spec
    (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m) {u : ℝ}
    (hu0 : 0 < u) (hum : u < (m : ℝ)) :
    hypergeomTiltMean (k + m + r) k m
      (manuscriptHypergeomTiltAtMean k m r hmk hm u) = u := by
  change (manuscriptHypergeomRecurrenceLaw k m r hmk).mean
    (manuscriptHypergeomTiltAtMean k m r hmk hm u) = u
  exact finiteSupportMeanInverse_spec
    ((manuscriptHypergeomRecurrenceLaw k m r hmk).toFiniteSupportTiltCurve
      (by exact_mod_cast hm)) hu0 hum

/-- The mean parameterization covers every point in the open support, with a
unique real tilt. -/
theorem manuscript_odd_mean_inverse_bridge
    (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m) {u : ℝ}
    (hu0 : 0 < u) (hum : u < (m : ℝ)) :
    ∃! t : ℝ, hypergeomTiltMean (k + m + r) k m t = u := by
  let L := manuscriptHypergeomRecurrenceLaw k m r hmk
  have h := L.exists_unique_mean hm hu0 hum
  have heq (t : ℝ) : L.mean t = hypergeomTiltMean (k+m+r) k m t := by
    rfl
  rcases h with ⟨t, ht, huniq⟩
  refine ⟨t, ?_, ?_⟩
  · change hypergeomTiltMean (k+m+r) k m t = u
    rw [← heq t]
    exact ht
  · intro s hs
    apply huniq s
    rw [heq s]
    exact hs

/-- The paper's real-root admissibility bound, now quantified in the actual
mean coordinate through the certified inverse-tilt map. -/
theorem manuscript_odd_lem_PB_mean_contract
    (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m) {u : ℝ}
    (hu0 : 0 < u) (hum : u < (m : ℝ)) :
    0 < manuscriptHypergeomVarianceAtMean k m r hmk hm u ∧
      manuscriptHypergeomVarianceAtMean k m r hmk hm u ≤
        u * ((m : ℝ) - u) / m := by
  let L := manuscriptHypergeomRecurrenceLaw k m r hmk
  let t := manuscriptHypergeomTiltAtMean k m r hmk hm u
  have hmean : L.mean t = u := by
    change hypergeomTiltMean (k + m + r) k m t = u
    exact manuscriptHypergeomTiltAtMean_spec k m r hmk hm hu0 hum
  have hpos := L.variance_pos hm t
  have hadm := L.varianceAdmissible hm t
  rw [hmean] at hadm
  have hdeg : (L.degree : ℝ) = (m : ℝ) := rfl
  rw [hdeg] at hadm
  exact ⟨by simpa [manuscriptHypergeomVarianceAtMean, t, L] using hpos,
    by simpa [manuscriptHypergeomVarianceAtMean, t, L] using hadm⟩

/-- Paper result `prop:two_level`: every maximizer on a fixed-sum,
fixed-squared-norm slice has at most two coordinate values. -/
theorem manuscript_prop_two_level_contract (N k : ℕ) (rho : ℝ)
    (hk0 : 0 < k) (hkN : k < N) (_hrho : 0 ≤ rho)
    (y : Fin N → ℝ) (hsum : (∑ i, y i) = 0)
    (hnorm : (∑ i, (y i)^2) = rho^2)
    (hmax : ∀ v : Fin N → ℝ, (∑ i, v i) = 0 →
      (∑ i, (v i)^2) = rho^2 →
      sliceExponential Finset.univ v k ≤ sliceExponential Finset.univ y k) :
    (Finset.univ.image y).card ≤ 2 := by
  apply sliceExponential_maximizer_at_most_two N k hk0 hkN y
  intro v hv hsquare
  exact hmax v (by rw [hsum] at hv; exact hv) (by rw [hnorm] at hsquare; exact hsquare)

/-- Paper result `lem:PB` in the canonical normal form. The product-law clause
records the real Bernoulli factorization of the actual tilted law; the remaining
clauses are the stated strict mean and mean--variance feasibility region. -/
theorem manuscript_lem_PB_contract (j h r : ℕ) (hj : 0 < j) (t : ℝ) :
    let N := j + (j + h) + r
    (∃ p : Fin (min (min (j + h) (N - (j + h))) (min j (N - j))) → unitInterval,
      (∀ i, 0 < (p i : ℝ) ∧ (p i : ℝ) < 1) ∧
      (hypergeomTiltMeasure N (j + h) j t).map (fun i : Fin (j + 1) => (i : ℝ)) =
        (independentBernoulliMeasure p).map (fun x =>
          ((j + h + j - N : ℕ) : ℝ) + ∑ i, x i)) ∧
    hypergeomMGF N (j + h) j t = hypergeomMGF N j (j + h) t ∧
    0 < hypergeomTiltMean N (j + h) j t ∧
    hypergeomTiltMean N (j + h) j t < j ∧
    0 < hypergeomTiltVariance N (j + h) j t ∧
    hypergeomTiltVariance N (j + h) j t ≤
      hypergeomTiltMean N (j + h) j t *
        ((j : ℝ) - hypergeomTiltMean N (j + h) j t) / j := by
  dsimp only
  have hN : j + h + j ≤ j + (j + h) + r := by omega
  have hkN : j + h ≤ j + (j + h) + r := by omega
  have hmN : j ≤ j + (j + h) + r := by omega
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hmean := hypergeomTiltMean_mem_Ioo_of_margins
    (j + (j + h) + r) (j + h) j (by omega) hN hj t
  have hvarpos := hypergeomTiltVariance_pos_of_margins
    (j + (j + h) + r) (j + h) j (by omega) hN hj t
  have hvar := hypergeomTiltVariance_admissible_of_margins
    (j + (j + h) + r) (j + h) j (by omega) hN hj t
  refine ⟨?_, hypergeomMGF_transpose _ _ _ hkN hmN t, hmean.1, hmean.2,
    hvarpos, hvar⟩
  obtain ⟨p, hp, hlaw⟩ := hypergeom_tilted_law_eq_shifted_independent_bernoulli
    (j + (j + h) + r) (j + h) j hkN hmN t
  exact ⟨p, hp, hlaw⟩

/-- The exact stationary branch statement in `lem:branch`: the polynomial has
one positive root, stationary balance implies that root equation, and any
nonpositive comparison value at B places the positive root at or below B. -/
theorem manuscript_lem_branch_contract (j m r u : ℝ)
    (hj : 1 ≤ j) (hjm : j ≤ m) (hr : 0 ≤ r) (hN : 1 < j + m + r)
    (hu : 0 < u) (huj : u < j) :
    (∃! v : ℝ, 0 < v ∧ stationaryPolynomial j m r u v = 0) ∧
    (∀ B : ℝ, 0 < B → stationaryPolynomial j m r u B ≤ 0 →
      ∃ v : ℝ, 0 < v ∧ stationaryPolynomial j m r u v = 0 ∧ v ≤ B) ∧
    (∀ v z : ℝ,
      (1-z)*(v+u^2)+(r+(j+m)*z)*u-j*m*z=0 →
      z*stationaryDen j m u v=v*(r+2*u) →
      stationaryPolynomial j m r u v=0) := by
  have hex := stationaryPolynomial_existsUnique_positive_root j m r u hj hjm hr hN hu huj
  refine ⟨hex, ?_, ?_⟩
  · intro B hB hFB
    obtain ⟨v, hv, huniq⟩ := hex
    let T := j + m + r - 1
    let b := -j*m*r-2*j*m*u+j*m+j*u^2-j*u+m*u^2-m*u+r*u^2+r*u+2*u^2
    let c := u*(j-u)*(r+u)*(m-u)
    have hT : 0 < T := by dsimp [T]; linarith
    have hc : 0 < c := by
      dsimp [c]
      have hju : 0 < j-u := sub_pos.mpr huj
      have hru : 0 < r+u := by linarith
      have hmu : 0 < m-u := by linarith
      positivity
    have hvpoly := hv.2
    have hroot : -T*v^2+b*v+c=0 := by
      rw [stationary_polynomial_quadratic] at hvpoly
      dsimp [T,b,c]
      exact hvpoly
    have hBquad : -T*B^2+b*B+c≤0 := by
      rw [stationary_polynomial_quadratic] at hFB
      dsimp [T,b,c]
      exact hFB
    have hvB := concave_quadratic_positive_root_bound T b c v B hT hc hv.1 hB hroot hBquad
    exact ⟨v, hv.1, hv.2, hvB⟩
  · intro v z hrq hsq
    exact stationary_elimination j m r u v z hrq hsq

/-- Paper result `lem:identity`, with its unrestricted polynomial domain and
sole nonzero-denominator condition. -/
theorem manuscript_lem_identity_contract (j h r x : ℝ)
    (hT : 2*j+h+r-1 ≠ 0) :
    -16*(2*j+h+r-1)*stationaryPolynomial j (j+h) r ((j+x)/2)
       (j*(j+h+r)/(4*(2*j+h+r-1))) =
    (j^2*(j-1)-(2*j+h+r-1)*x^2)*(h-r-x)^2+
      (j+h+r)*(2*j*(h-r)*x+((j+h+r-1)*(j+h+r)-2*j)*x^2) := by
  exact stationary_main_identity j h r x hT


/-- Paper result `lem:universal`, with the manuscript's strict square-root
threshold and the complete real parameter domain. -/
theorem manuscript_lem_universal_contract (j L D x : ℝ)
    (hj : 3 ≤ j) (hL : j - 1 ≤ L) (hD : |D| ≤ L - j + 1)
    (hx : |x| < j * Real.sqrt ((j - 1) / (L + j))) :
    0 ≤ (j^2 * (j - 1) - (L + j) * x^2) * (D - x)^2 +
      (L + 1) * (2 * j * D * x + (L * (L + 1) - 2 * j) * x^2) := by
  have hT : 0 < L + j := by linarith
  have hq : 0 ≤ (j - 1) / (L + j) := div_nonneg (by linarith) hT.le
  have hsqrt : (Real.sqrt ((j - 1) / (L + j)))^2 =
      (j - 1) / (L + j) := Real.sq_sqrt hq
  have hroot : 0 ≤ j * Real.sqrt ((j - 1) / (L + j)) := by positivity
  have hx2 : x^2 < j^2 * ((j - 1) / (L + j)) := by
    have hs := (sq_lt_sq₀ (abs_nonneg x) hroot).2 hx
    have habs : |x|^2 = x^2 := sq_abs x
    rw [habs, mul_pow, hsqrt] at hs
    exact hs
  have hA : 0 < j^2 * (j - 1) - (L + j) * x^2 := by
    have hmul : (L + j) * x^2 < (L + j) * (j^2 * ((j - 1) / (L + j))) :=
      mul_lt_mul_of_pos_left hx2 hT
    have hc : (L + j) * (j^2 * ((j - 1) / (L + j))) = j^2 * (j - 1) := by
      field_simp [ne_of_gt hT]
    rw [hc] at hmul
    nlinarith
  exact universal_stationary_comparison j L D x hj hL hD hA

/-- Paper result `prop:allinner`: the actual tilted variance over the whole
real tilt line has the stated supremum bound in every `j≥3` normal-form layer. -/
theorem manuscript_prop_allinner_contract (j h r : ℕ) (hj : 3 ≤ j) :
    let N := 2*j+h+r
    sSup (Set.range (fun t : ℝ => hypergeomTiltVariance N j (j+h) t)) ≤
      (j:ℝ) * ((N:ℝ) - j) / (4 * ((N:ℝ) - 1)) := by
  dsimp only
  apply csSup_le (Set.range_nonempty _)
  rintro z ⟨t, rfl⟩
  have hN : j + h + j ≤ 2*j+h+r := by omega
  have hjN : j ≤ 2*j+h+r := by omega
  have hsampleN : j+h ≤ 2*j+h+r := by omega
  change hypergeomTiltVariance (2*j+h+r) j (j+h) t ≤ _
  rw [hypergeomTiltVariance_transpose (2*j+h+r) j (j+h) hjN hsampleN t]
  rw [← hypergeomLogMGF_second_deriv_eq_variance (2*j+h+r) (j+h) j hsampleN hjN t]
  have hcurv := hypergeom_sharp_curvature_canonical_min
    (2*j+h+r) (j+h) j (by omega) hN t
  have hprod : ((j:ℝ) * ((2*j+h+r:ℕ):ℝ) - (j:ℝ)^2) ≤
      ((j+h:ℝ) * ((2*j+h+r:ℕ):ℝ) - (j+h:ℝ)^2) := by
    have hh : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
    have hr : 0 ≤ (r:ℝ) := Nat.cast_nonneg r
    push_cast
    nlinarith [mul_nonneg hh hr]
  have hprod' : (j:ℝ) * (((2*j+h+r:ℕ):ℝ) - j) ≤
      (j+h:ℝ) * (((2*j+h+r:ℕ):ℝ) - (j+h)) := by
    nlinarith
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcurv ⊢
  have hjR : 0 ≤ (j:ℝ) := Nat.cast_nonneg j
  have hhR : 0 ≤ (h:ℝ) := Nat.cast_nonneg h
  have hrR : 0 ≤ (r:ℝ) := Nat.cast_nonneg r
  have hmin : min
      (((j:ℝ)+h) * (2*(j:ℝ)+h+r-((j:ℝ)+h)))
      ((j:ℝ) * (2*(j:ℝ)+h+r-(j:ℝ))) =
      (j:ℝ) * (2*(j:ℝ)+h+r-(j:ℝ)) := by
    apply min_eq_right
    nlinarith [hprod']
  rw [hmin] at hcurv
  exact hcurv


/-- Core of paper result `prop:variance_parity`: exact variance supremum, both
parity values, equality for even N, and the strict odd gap with its integral
identity, all for the actual exchangeable variance set. -/
theorem manuscript_prop_variance_parity_contract (N : ℕ) (hN : 2 ≤ N) :
    exactExchangeableVarianceConstant N = parityVarianceConstant N ∧
    exactExchangeableVarianceConstant N =
      4 * (⌊(N:ℝ)^2 / 4⌋₊ : ℝ) / ((N:ℝ) * ((N:ℝ)-1)) ∧
    (Even N → exactExchangeableConstant N = exactExchangeableVarianceConstant N) ∧
    (¬ Even N → exactExchangeableVarianceConstant N < exactExchangeableConstant N ∧
      exactExchangeableConstant N < (N:ℝ) / ((N:ℝ)-1) ∧
      exactExchangeableConstant N - exactExchangeableVarianceConstant N =
        (2 * ∫ t in (0:ℝ)..(1/(N:ℝ)), t * Real.artanh t) /
          ((1-1/(N:ℝ))*Real.artanh (1/(N:ℝ)))) :=
  exact_variance_parity_theorem N hN

/-- Paper result `prop:explicit_extremizer`: the actual uniform Hamming-slice
law, contrast normalization and map to the Bernoulli pushforward, including
odd nonzero contact and even zero-tilt limiting sharpness. -/
theorem manuscript_prop_explicit_extremizer_contract
    (N : ℕ) (hN : 2 ≤ N) (i : Fin N) :
    let k := N/2
    let p : ℝ := (k:ℝ)/N
    let μ := uniformHammingMeasure N k
    let a := singleCoordinateContrast i
    IsProbabilityMeasure μ ∧ FiniteExchangeableMeasure μ ∧
      (∀ᵐ x ∂μ, x ∈ realCube N) ∧ (∑ j, a j = 0) ∧
      (∑ j, (a j)^2) = ((N:ℝ)-1)/N ∧
      (∀ x : Fin N → ℝ, ∑ j, a j*x j = x i - (∑ j, x j)/N) ∧
      μ.map (singleCoordinateBernoulli i) =
        ENNReal.ofReal p • Measure.dirac (1:ℝ) +
          ENNReal.ofReal (1-p) • Measure.dirac (0:ℝ) ∧
      (∀ᵐ x ∂μ, ∑ j, a j*x j = 2*(singleCoordinateBernoulli i x-p)) ∧
      ((¬ Even N) → let α := Real.log (((N:ℝ)+1)/((N:ℝ)-1));
        α ≠ 0 ∧ Real.log (∫ x, Real.exp (α*∑ j, a j*x j) ∂μ) =
          paritySharpConstant N*α^2*(∑ j, (a j)^2)/2) ∧
      ((Even N) → Tendsto (fun z : ℝ =>
        2*Real.log (∫ x, Real.exp (z*∑ j, a j*x j) ∂μ)/(z^2*(∑ j, (a j)^2)))
          (𝓝[≠] (0:ℝ)) (𝓝 (paritySharpConstant N))) :=
  explicit_single_coordinate_extremizer N hN i

/-- Paper result `lem:threemass`: the exact least quadratic coefficient of the
actual centered three-mass law, with positive masses and the stated shape
condition; the conditional formula includes its continuous balanced case. -/
theorem manuscript_lem_threemass_contract (p0 p1 p2 : ℝ)
    (hp0 : 0 < p0) (hp1 : 0 < p1) (hp2 : 0 < p2)
    (hn : p0+p1+p2=1) (hshape : p1 ≤ 4*Real.sqrt (p0*p2)) :
    IsOptimalQuadraticProxy (threeMassCenteredLog p0 p1 p2)
      (if p0=p2 then 2*p0 else 2*(p0-p2)/Real.log (p0/p2)) := by
  simpa [threeMassProxy] using threeMass_optimal_proxy p0 p1 p2 hp0 hp1 hp2 hn hshape

/-- Main analytic clauses of paper result `odd:thm:envelope`: the
finite-population Laplace inequality and its nonzero strictness, together with
the actual-proxy Bernoulli comparison and even balanced equality. -/
theorem manuscript_odd_envelope_contract (N k m : ℕ)
    (hN : 7 ≤ N) (hm : 3 ≤ m) (hmk : m ≤ k)
    (hkhalf : 2*k ≤ N) (hmhalf : 2*m < N) :
    (∀ t, hypergeomCenteredLogMGF N k m t ≤
      scaledBernoulliLogLaplace (envelopeM (N:ℝ) (m:ℝ))
        ((k:ℝ)/(N:ℝ)) (envelopeScale (N:ℝ) (m:ℝ)) t) ∧
    (∀ t, t ≠ 0 → hypergeomCenteredLogMGF N k m t <
      scaledBernoulliLogLaplace (envelopeM (N:ℝ) (m:ℝ))
        ((k:ℝ)/(N:ℝ)) (envelopeScale (N:ℝ) (m:ℝ)) t) ∧
    (k < N/2 → hypergeomOptimalProxy N k m <
      envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/(N:ℝ))) ∧
    (Even N → 2*k=N → hypergeomOptimalProxy N k m =
      envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/(N:ℝ))) := by
  have hLap := hypergeom_laplace_envelope N k m hm hmk hkhalf hmhalf
  have hStrict (hkstrict : 2*k<N) : hypergeomOptimalProxy N k m <
      envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/N) := by
    exact hypergeom_proxy_lt_scaled_bernoulli_subhalf N k m (by omega) hmk hkstrict
  refine ⟨hLap.1, hLap.2, ?_, ?_⟩
  · intro hklt
    have hks : 2*k<N := by omega
    exact hStrict hks
  · intro hEven hbal
    exact hypergeom_proxy_eq_scaled_bernoulli_balanced N k m (by omega) hbal (by omega)

/-- Paper result `odd:thm:odd`: the exact closed odd-population maximum,
validity for every legal pair, and the complete equality classification. -/
theorem manuscript_odd_global_extremizer_contract (n : ℕ) (hn : 0 < n) :
    let N := 2*n+1
    let C : ℝ := 1/(((N:ℝ)-1)*Real.artanh (1/(N:ℝ)))
    (∀ k m : ℕ, 0 < k → k < N → 0 < m → m < N →
      normalizedHypergeomProxy N k m ≤ C ∧
        (normalizedHypergeomProxy N k m=C ↔
          (m=1 ∨ m=2*n) ∧ (k=n ∨ k=n+1))) ∧
    hypergeomVariationalConstant N=C ∧
    exactExchangeableConstant N=C ∧
    IsLeast {D : ℝ | IsExchangeableCoefficient N D} C := by
  exact exact_odd_global_theorem n hn

end
end ExactHoeffding
