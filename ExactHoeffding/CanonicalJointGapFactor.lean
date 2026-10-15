import ExactHoeffding.JointOptimizedFactor
import ExactHoeffding.JointFullAxisOptimalValue

/-! # Canonical actual two-parameter optimal-proxy gap factor -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

/-- The gap between actual supremum-defined normalized objectives. -/
def canonicalJointGap (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  jointOptimalValue 1 p-jointOptimalValue m p

/-- Both exact vanishing axes and the imbalance reflection hold for the
canonical actual supremum, independently of the choice of optimizing branch. -/
theorem canonicalJointGap_origin_identities (m : ℕ) (hm : 0<m) :
    AnalyticAt ℝ (canonicalJointGap m) (0,0) ∧
      (∀ᶠ d in 𝓝 (0 : ℝ), canonicalJointGap m (0,d)=0) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), canonicalJointGap m (e,0)=0) ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0,0),
        canonicalJointGap m (p.1,-p.2)=canonicalJointGap m p) := by
  obtain ⟨τ₁,h₁,hz₁,hmax₁,hbal₁,href₁⟩ :=
    jointProxyExtension_analytic_global_optimizer 1 (by omega)
  obtain ⟨τm,hmτ,hzm,hmaxm,hbalm,hrefm⟩ :=
    jointProxyExtension_analytic_global_optimizer m hm
  have heq : canonicalJointGap m =ᶠ[𝓝 (0,0)] jointOptimizedGap m τ₁ τm := by
    filter_upwards [jointOptimalValue_eventually_eq_branch 1 (0,0) τ₁ hmax₁,
      jointOptimalValue_eventually_eq_branch m (0,0) τm hmaxm] with p h1 hm'
    simp only [canonicalJointGap,jointOptimizedGap,h1,hm']
  refine ⟨((jointOptimalValue_analytic_full_axis 1 (by omega) 0 (by norm_num)).sub
    (jointOptimalValue_analytic_full_axis m hm 0 (by norm_num))),?_,?_,?_⟩
  · have hc : Tendsto (fun d : ℝ => ((0 : ℝ),d)) (𝓝 0) (𝓝 (0,0)) :=
      continuousAt_const.prodMk continuousAt_id
    filter_upwards [hc.eventually heq,
      jointOptimizedGap_population_axis_zero m hm τ₁ τm hmax₁ hmaxm] with d hd hz
    exact hd.trans hz
  · have hc : Tendsto (fun e : ℝ => (e,(0 : ℝ))) (𝓝 0) (𝓝 (0,0)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hc.eventually heq,
      jointNormalizedValue_balanced 1 (by omega) τ₁ hbal₁,
      jointNormalizedValue_balanced m hm τm hbalm] with e he h1 hm'
    rw [he,jointOptimizedGap,h1,hm',sub_self]
  · have hc : Tendsto (fun p : ℝ × ℝ => (p.1,-p.2)) (𝓝 (0,0)) (𝓝 (0,0)) := by
      have h : ContinuousAt (fun p : ℝ × ℝ => (p.1,-p.2)) (0,0) := by fun_prop
      simpa only [neg_zero] using h.tendsto
    filter_upwards [heq,hc.eventually heq,
      jointNormalizedValue_reflection 1 (by omega) τ₁ h₁ hz₁ href₁,
      jointNormalizedValue_reflection m hm τm hmτ hzm hrefm] with p hp hr h1 hm'
    rw [hr,hp,jointOptimizedGap,jointOptimizedGap,h1,hm']

/-- The canonical actual gap, for independent real parameters, has an exact
continuous `e*d²` factor near the balanced binomial corner. Its removable
corner value is the sharp coefficient obtained from actual finite laws. -/
theorem canonicalJointGap_continuous_factor (m : ℕ) (hm : 0<m) :
    ∃ B : ℝ × ℝ → ℝ, Continuous B ∧ B (0,0)=2*((m:ℝ)-1)/3 ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), canonicalJointGap m p=p.1*p.2^2*B p) := by
  obtain ⟨ha,hpop,hbal,href⟩ := canonicalJointGap_origin_identities m hm
  obtain ⟨B,hB,hfactor⟩ := analytic_even_coordinate_factor (canonicalJointGap m)
    ha hpop hbal href
  refine ⟨B,hB,?_,hfactor⟩
  apply normalizedHypergeomProxy_joint_gap_factor_origin m hm B hB.continuousAt
  obtain ⟨τ₁,_,_,hmax₁,_,_⟩ := jointProxyExtension_analytic_global_optimizer 1 (by omega)
  obtain ⟨τm,_,_,hmaxm,_,_⟩ := jointProxyExtension_analytic_global_optimizer m hm
  filter_upwards [hfactor,hmax₁,hmaxm] with p hp h1 hm'
  intro N k hN hk hmN he hd
  have hcan1 := jointOptimalValue_eq_at_global_max 1 p (τ₁ p) ((h1 (τ₁ p)).mpr rfl)
  have hcanm := jointOptimalValue_eq_at_global_max m p (τm p) ((hm' (τm p)).mpr rfl)
  change jointOptimalValue 1 p=jointNormalizedValue 1 τ₁ p at hcan1
  change jointOptimalValue m p=jointNormalizedValue m τm p at hcanm
  have hv1 := jointNormalizedValue_physical_of_global 1 (by omega) τ₁ p N k hN hk
    (by omega) he hd ((h1 (τ₁ p)).mpr rfl)
  have hvm := jointNormalizedValue_physical_of_global m hm τm p N k hN hk hmN
    he hd ((hm' (τm p)).mpr rfl)
  simpa only [canonicalJointGap,hcan1,hcanm,hv1,hvm] using hp

end
end ExactHoeffding
