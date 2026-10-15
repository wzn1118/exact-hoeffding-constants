import ExactHoeffding.CompactCanonicalContraction
import ExactHoeffding.BernoulliOptimal

/-! # Actual finite-population contraction from the joint analytic factor -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

/-- The compact analytic comparison applies simultaneously to every physical
success margin in the nonnegative imbalance half interval. -/
theorem normalizedHypergeomProxy_eventually_analytic_contraction_nonnegative
    (m : ℕ) (hm : 2≤m) (d₀ : ℝ) (hd₀ : 0≤d₀) (hd₁ : d₀<1) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,k≤N→(1-2*(k:ℝ)/N)∈Icc 0 d₀→
      normalizedHypergeomProxy N k m≤normalizedHypergeomProxy N k 1 ∧
      (normalizedHypergeomProxy N k m=normalizedHypergeomProxy N k 1↔2*k=N) := by
  have hlim : Tendsto (fun N:ℕ => 1/(N:ℝ)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [hlim.eventually
      (jointOptimalValue_eventually_uniform_strict_contraction m hm d₀ hd₀ hd₁),
    hlim.eventually (jointOptimalValue_eventually_uniform_hypergeom m (by omega) d₀ hd₀ hd₁),
    hlim.eventually (jointOptimalValue_eventually_uniform_hypergeom 1 (by omega) d₀ hd₀ hd₁),
    eventually_ge_atTop (max 2 m)] with N hcomp hvm hv1 hlarge
  intro k hk hd
  have hN : 2≤N := le_trans (le_max_left _ _) hlarge
  have hmN : m≤N := le_trans (le_max_right _ _) hlarge
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hds : (1-2*(k:ℝ)/N)∈Icc (-d₀) d₀ := ⟨by linarith [hd.1],hd.2⟩
  have hzero : 1-2*(k:ℝ)/N=0 ↔ 2*k=N := by
    rw [sub_eq_zero,eq_div_iff hNR.ne',one_mul]
    constructor
    · intro h
      exact_mod_cast h.symm
    · intro h
      exact_mod_cast h.symm
  have h := hcomp (by positivity) _ hd
  rw [hvm _ hds N k hN hk hmN rfl rfl,
    hv1 _ hds N k hN hk (by omega) rfl rfl] at h
  exact ⟨h.1,h.2.trans hzero⟩

/-- Reflection gives a compact uniform comparison for all interior success
proportions, with exactly the balanced equality mechanism. -/
theorem normalizedHypergeomProxy_eventually_analytic_contraction
    (m : ℕ) (hm : 2≤m) (d₀ : ℝ) (hd₀ : 0≤d₀) (hd₁ : d₀<1) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,k≤N→(1-2*(k:ℝ)/N)∈Icc (-d₀) d₀→
      normalizedHypergeomProxy N k m≤normalizedHypergeomProxy N k 1 ∧
      (normalizedHypergeomProxy N k m=normalizedHypergeomProxy N k 1↔2*k=N) := by
  filter_upwards [normalizedHypergeomProxy_eventually_analytic_contraction_nonnegative m hm d₀ hd₀ hd₁,
    eventually_ge_atTop (max 2 m)] with N hcomp hlarge
  intro k hk hd
  have hN : 2≤N := le_trans (le_max_left _ _) hlarge
  have hmN : m≤N := le_trans (le_max_right _ _) hlarge
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  by_cases hh : 2*k≤N
  · have hhalf : 2*(k:ℝ)≤N := by exact_mod_cast hh
    exact hcomp k hk ⟨by linarith [(div_le_one hNR).mpr hhalf],hd.2⟩
  · have href : 1-2*((N-k:ℕ):ℝ)/N= -(1-2*(k:ℝ)/N) := by
      rw [Nat.cast_sub hk]
      field_simp
      <;> ring
    have hhalf : (N:ℝ)≤2*k := by exact_mod_cast (show N≤2*k by omega)
    have hdc : (1-2*((N-k:ℕ):ℝ)/N)∈Icc 0 d₀ := by
      rw [href]
      exact ⟨by linarith [(one_le_div hNR).mpr hhalf],by linarith [hd.1]⟩
    have hc := hcomp (N-k) (Nat.sub_le _ _) hdc
    rw [normalizedHypergeomProxy_success_complement N k m hk hmN (by omega),
      normalizedHypergeomProxy_success_complement N k 1 hk (by omega) (by omega)]
    exact ⟨hc.1,hc.2.trans (by omega)⟩

/-- The actual one-draw proxy is the whole-domain Bernoulli sharp proxy. -/
theorem hypergeomOptimalProxy_singleton_bernoulliSharpBeta (N k : ℕ)
    (hN : 0<N) (hk : k≤N) :
    hypergeomOptimalProxy N k 1=bernoulliSharpBeta ((k:ℝ)/N) := by
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hp : 0≤(k:ℝ)/N := by positivity
  have hp1 : (k:ℝ)/N≤1 := (div_le_one hNR).mpr (by exact_mod_cast hk)
  unfold hypergeomOptimalProxy
  rw [hypergeomCenteredLogMGF_singleton N k hk hN]
  exact optimalProxy_eq_of_optimal _ (by simp [bernoulliCenteredLogMGF,bernoulliMGF]) _
    (bernoulli_sharp_quadratic_optimal _ hp hp1)

/-- The manuscript's compact-proportion contraction, obtained from the
joint analytic actual optimum and its strictly positive exact gap factor. -/
theorem hypergeom_compact_bernoulli_envelope_via_analytic_factor
    (m : ℕ) (hm : 2≤m) (η : ℝ) (hη : 0<η) (hηhalf : η<1/2) :
    ∃ N₁ : ℕ,∀ N k : ℕ,N₁≤N→η≤(k:ℝ)/N→(k:ℝ)/N≤1-η→
      hypergeomOptimalProxy N k m≤
        envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/N) ∧
      (hypergeomOptimalProxy N k m=
        envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/N)↔2*k=N) ∧
      (2*k≠N→hypergeomOptimalProxy N k m<
        envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/N)) := by
  have hd₀ : 0≤1-2*η := by linarith
  have hd₁ : 1-2*η<1 := by linarith
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp
    (normalizedHypergeomProxy_eventually_analytic_contraction m hm (1-2*η) hd₀ hd₁)
  refine ⟨max N₁ (m+1),?_⟩
  intro N k hlarge hlo hhi
  have hmN : m<N := by omega
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hNm : 0<(N:ℝ)-m := sub_pos.mpr (by exact_mod_cast hmN)
  have hN1 : 0<(N:ℝ)-1 := by
    have : (2:ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
    linarith
  have hk : k≤N := by
    have hr := (div_le_iff₀ hNR).mp hhi
    exact_mod_cast (show (k:ℝ)≤N by nlinarith)
  have hd : (1-2*(k:ℝ)/N)∈Icc (-(1-2*η)) (1-2*η) := by
    simp only [mul_div_assoc]
    constructor <;> linarith
  obtain ⟨hle,heq⟩ := hN₁ N (by omega) k hk hd
  rw [normalizedHypergeomProxy,normalizedHypergeomProxy,
    hypergeomOptimalProxy_singleton_bernoulliSharpBeta N k (by omega) hk] at hle heq
  norm_num only [Nat.cast_one] at hle heq
  have hscale : (4*(N:ℝ)/((m:ℝ)*((N:ℝ)-m)))*
      (envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/N))=
      (4*(N:ℝ)/((1:ℝ)*((N:ℝ)-1)))*bernoulliSharpBeta ((k:ℝ)/N) := by
    unfold envelopeM
    field_simp
  have hpos : 0<4*(N:ℝ)/((m:ℝ)*((N:ℝ)-m)) := by positivity
  rw [← hscale] at hle heq
  have hle' := (mul_le_mul_iff_right₀ hpos).mp hle
  have heq' : hypergeomOptimalProxy N k m=
      envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/N)↔2*k=N := by
    simpa only [mul_right_inj' hpos.ne'] using heq
  exact ⟨hle',heq',fun hn => lt_of_le_of_ne hle' (fun he => hn (heq'.mp he))⟩

end
end ExactHoeffding
