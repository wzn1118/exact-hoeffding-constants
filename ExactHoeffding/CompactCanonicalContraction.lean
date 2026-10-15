import ExactHoeffding.CanonicalGapPopulationDerivative
import ExactHoeffding.AnalyticPopulationFactor
import ExactHoeffding.CompactContractionStability

/-! # Compact uniform contraction for the actual canonical optimum -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

theorem jointOptimalValue_binomial_axis (m : ℕ) (hm : 0<m)
    (d : ℝ) (hd : d∈Ioo (-1:ℝ) 1) :
    jointOptimalValue m (0,d)=4*bernoulliSharpBeta (jointSuccessFraction d) := by
  have hmax := (jointProxyExtension_binomial_unique_max m hm d
    (jointBinomialTilt d) hd).mpr rfl
  rw [jointOptimalValue_eq_at_global_max m (0,d) (jointBinomialTilt d)
    (fun u => hmax (mem_univ u)),jointProxyExtension_binomial_contact m hm d hd]
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  simp only [mul_zero,sub_zero,mul_one]
  field_simp

theorem canonicalJointGap_population_axis_zero (m : ℕ) (hm : 0<m)
    (d : ℝ) (hd : d∈Ioo (-1:ℝ) 1) : canonicalJointGap m (0,d)=0 := by
  rw [canonicalJointGap,jointOptimalValue_binomial_axis 1 (by omega) d hd,
    jointOptimalValue_binomial_axis m hm d hd,sub_self]

/-- Removing the first coordinate from an actual exact factor preserves the
second-coordinate square, including points on the removed axis. -/
theorem populationSlope_eventually_eq_factor (F B : ℝ×ℝ→ℝ)
    (hF : AnalyticAt ℝ F (0,0)) (hB : Continuous B)
    (hfactor : ∀ᶠ p in 𝓝 ((0:ℝ),0),F p=p.1*p.2^2*B p) :
    ∀ᶠ p in 𝓝 ((0:ℝ),0),populationSlope F p=p.2^2*B p := by
  have hc : Tendsto (fun p : ℝ×ℝ => ((0:ℝ),p.2)) (𝓝 (0,0)) (𝓝 (0,0)) :=
    continuousAt_const.prodMk continuousAt_snd
  filter_upwards [hfactor,hc.eventually hfactor.eventually_nhds,
    hc.eventually hF.eventually_analyticAt] with p hp hloc ha
  by_cases he : p.1=0
  · have hs : ∀ᶠ e in 𝓝 (0:ℝ),F (e,p.2)=e*p.2^2*B (e,p.2) :=
      (continuousAt_id.prodMk continuousAt_const :
        ContinuousAt (fun e : ℝ => (e,p.2)) 0).tendsto.eventually hloc
    have hder : HasDerivAt (fun e : ℝ => F (e,p.2))
        (parameterPartial F (1,0) (0,p.2)) 0 :=
      ha.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0
        ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _)) rfl
    have hid := population_factor_axis_identification F B p.2 _ hB.continuousAt hs hder
    simp only [populationSlope,he,if_pos]
    simpa only [← he] using hid.symm
  · rw [populationSlope,if_neg he,hp]
    field_simp

/-- A single factor represents the actual supremum gap around every interior
binomial-axis point. Its entire boundary is the explicit contraction coefficient. -/
theorem canonicalJointGap_full_axis_factor (m : ℕ) (hm : 2≤m) :
    ∃ B : ℝ×ℝ→ℝ, ∀ d∈Ioo (-1:ℝ) 1,
      ContinuousAt B (0,d) ∧ B (0,d)=compactContractionBoundary m d ∧
      (∀ᶠ p in 𝓝 ((0:ℝ),d),canonicalJointGap m p=p.1*p.2^2*B p) := by
  obtain ⟨B₀,hB₀,hB₀0,hfactor₀⟩ := canonicalJointGap_continuous_factor m (by omega)
  let B : ℝ×ℝ→ℝ := fun p => if p.2=0 then B₀ p else
    populationSlope (canonicalJointGap m) p/p.2^2
  have hG : ∀ d∈Ioo (-1:ℝ) 1,AnalyticAt ℝ (canonicalJointGap m) (0,d) := by
    intro d hd
    exact (jointOptimalValue_analytic_full_axis 1 (by omega) d hd).sub
      (jointOptimalValue_analytic_full_axis m (by omega) d hd)
  have hzero : ∀ d∈Ioo (-1:ℝ) 1,
      ∀ᶠ u in 𝓝 d,canonicalJointGap m (0,u)=0 := by
    intro d hd
    filter_upwards [isOpen_Ioo.mem_nhds hd] with u hu
    exact canonicalJointGap_population_axis_zero m (by omega) u hu
  have heq₀ : B=ᶠ[𝓝 ((0:ℝ),0)] B₀ := by
    filter_upwards [populationSlope_eventually_eq_factor (canonicalJointGap m) B₀
      (hG 0 (by norm_num)) hB₀ hfactor₀] with p hp
    dsimp [B]
    split_ifs with hd
    · rfl
    · rw [hp]
      exact mul_div_cancel_left₀ (B₀ p) (pow_ne_zero 2 hd)
  refine ⟨B,?_⟩
  intro d hd
  by_cases hd0 : d=0
  · subst d
    refine ⟨hB₀.continuousAt.congr_of_eventuallyEq heq₀,?_,?_⟩
    · simpa only [B,if_pos rfl,compactContractionBoundary_zero] using hB₀0
    · filter_upwards [hfactor₀,heq₀] with p hp he
      rw [he]
      exact hp
  · have hne : ∀ᶠ p : ℝ×ℝ in 𝓝 (0,d),p.2≠0 :=
      (continuousAt_snd.tendsto.eventually (eventually_ne_nhds hd0))
    have hcont : ContinuousAt B (0,d) := by
      apply ((populationSlope_continuousAt_axis (canonicalJointGap m) d (hG d hd)
        (hzero d hd)).div (continuousAt_snd.pow 2) (pow_ne_zero 2 hd0)).congr_of_eventuallyEq
      filter_upwards [hne] with p hp
      simp only [B,if_neg hp]
      rfl
    have hfac : ∀ᶠ p : ℝ×ℝ in 𝓝 (0,d),
        canonicalJointGap m p=p.1*p.2^2*B p := by
      have haxis : ∀ᶠ p : ℝ×ℝ in 𝓝 (0,d),canonicalJointGap m (0,p.2)=0 :=
        (continuousAt_snd : ContinuousAt (fun p : ℝ×ℝ => p.2) (0,d)).tendsto.eventually
          (hzero d hd)
      filter_upwards [hne,haxis] with p hpd hz
      dsimp [B]
      rw [if_neg hpd]
      by_cases he : p.1=0
      · have hpz : p=((0:ℝ),p.2) := by ext <;> simp only [he]
        rw [hpz]
        simpa only [zero_mul] using hz
      · rw [populationSlope,if_neg he]
        field_simp
    refine ⟨hcont,?_,hfac⟩
    exact canonicalJointGap_factor_axis_value m hm B d hd hd0 hcont
      ((continuousAt_id.prodMk continuousAt_const :
        ContinuousAt (fun e : ℝ => (e,d)) 0).tendsto.eventually hfac)

/-- The exact two-coordinate gap factor and its positive sign are uniform on
every compact interior imbalance interval, including the balanced point. -/
theorem canonicalJointGap_compact_factor (m : ℕ) (hm : 2≤m)
    (d₀ : ℝ) (hd₀ : 0≤d₀) (hd₁ : d₀<1) :
    ∃ B : ℝ×ℝ→ℝ, (∀ d∈Icc 0 d₀,ContinuousAt B (0,d)) ∧
      (∀ d∈Icc 0 d₀,B (0,d)=compactContractionBoundary m d) ∧
      (∀ᶠ e in 𝓝 (0:ℝ),∀ d∈Icc 0 d₀,
        canonicalJointGap m (e,d)=e*d^2*B (e,d)) ∧
      (∃ c:ℝ,0<c ∧ ∀ᶠ e in 𝓝 (0:ℝ),∀ d∈Icc 0 d₀,c≤B (e,d)) := by
  obtain ⟨B,hB⟩ := canonicalJointGap_full_axis_factor m hm
  have hint : ∀ d∈Icc 0 d₀,d∈Ioo (-1:ℝ) 1 := by
    intro d hd
    constructor <;> linarith [hd.1,hd.2]
  have hc : ∀ d∈Icc 0 d₀,ContinuousAt B (0,d) := fun d hd => (hB d (hint d hd)).1
  have ha : ∀ d∈Icc 0 d₀,B (0,d)=compactContractionBoundary m d :=
    fun d hd => (hB d (hint d hd)).2.1
  refine ⟨B,hc,ha,?_,compactContractionFactor_eventually_uniform_pos m hm d₀ hd₀ hd₁ B hc ha⟩
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro d hd
  exact (hB d (hint d hd)).2.2

/-- Strict contraction of the actual canonical normalized optimum is uniform
on compact imbalance intervals; balance is the only equality case. -/
theorem jointOptimalValue_eventually_uniform_strict_contraction
    (m : ℕ) (hm : 2≤m) (d₀ : ℝ) (hd₀ : 0≤d₀) (hd₁ : d₀<1) :
    ∀ᶠ e in 𝓝 (0:ℝ),0<e→∀ d∈Icc 0 d₀,
      jointOptimalValue m (e,d)≤jointOptimalValue 1 (e,d) ∧
      (jointOptimalValue m (e,d)=jointOptimalValue 1 (e,d)↔d=0) := by
  obtain ⟨B,hB,ha,hfactor,_⟩ := canonicalJointGap_compact_factor m hm d₀ hd₀ hd₁
  exact compactContraction_factorized_strict_comparison m hm d₀ hd₀ hd₁ B
    (jointOptimalValue 1) (jointOptimalValue m) hB ha hfactor

end
end ExactHoeffding
