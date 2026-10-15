import ExactHoeffding.CanonicalJointGapFactor
import ExactHoeffding.JointPopulationBoundary

/-! # Actual population derivative and forced boundary of the canonical gap -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

theorem canonicalJointGap_hasDerivAt_population_zero
    (m : ℕ) (hm : 2≤m) (d : ℝ) (hd : d ∈ Ioo (-1 : ℝ) 1) (hd0 : d≠0) :
    HasDerivAt (fun e => canonicalJointGap m (e,d))
      (d^2*compactContractionBoundary m d) 0 := by
  obtain ⟨τ₁,h₁,hz₁,hmax₁⟩ :=
    jointProxyExtension_full_axis_analytic_global_optimizer 1 (by omega) d hd
  obtain ⟨τm,hmτ,hzm,hmaxm⟩ :=
    jointProxyExtension_full_axis_analytic_global_optimizer m (by omega) d hd
  have hQ₁ : AnalyticAt ℝ (jointProxyObjective 1) ((0,d),τ₁ (0,d)) := by
    rw [hz₁]
    exact jointProxyObjective_analytic_full_axis 1 d (jointBinomialTilt d) hd
  have hQm : AnalyticAt ℝ (jointProxyObjective m) ((0,d),τm (0,d)) := by
    rw [hzm]
    exact jointProxyObjective_analytic_full_axis m d (jointBinomialTilt d) hd
  have h₁g := ((hmax₁.self_of_nhds) (τ₁ (0,d))).mpr rfl
  have hmg := ((hmaxm.self_of_nhds) (τm (0,d))).mpr rfl
  have h₁d := jointNormalizedValue_singleton_hasDerivAt_population_zero τ₁ d hd h₁ hQ₁ h₁g
  have hmd := jointNormalizedValue_hasDerivAt_population_zero m hm τm d hd hd0 hmτ hQm hmg
  have heq : (fun e => canonicalJointGap m (e,d)) =ᶠ[𝓝 (0 : ℝ)]
      (fun e => jointNormalizedValue 1 τ₁ (e,d)-jointNormalizedValue m τm (e,d)) := by
    have hc : Tendsto (fun e : ℝ => (e,d)) (𝓝 0) (𝓝 (0,d)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hc.eventually (jointOptimalValue_eventually_eq_branch 1 (0,d) τ₁ hmax₁),
      hc.eventually (jointOptimalValue_eventually_eq_branch m (0,d) τm hmaxm)] with e h1 hm'
    simp only [canonicalJointGap,h1,hm']
  rw [← jointPopulationEnvelope_gap_coefficient m d hd hd0]
  exact (h₁d.sub hmd).congr_of_eventuallyEq heq

/-- Any continuous factor of the canonical actual gap has the stated exact
boundary at every nonzero interior imbalance. -/
theorem canonicalJointGap_factor_axis_value
    (m : ℕ) (hm : 2≤m) (B : ℝ × ℝ → ℝ)
    (d : ℝ) (hd : d ∈ Ioo (-1 : ℝ) 1) (hd0 : d≠0)
    (hB : ContinuousAt B (0,d))
    (hfactor : ∀ᶠ e in 𝓝 (0 : ℝ), canonicalJointGap m (e,d)=e*d^2*B (e,d)) :
    B (0,d)=compactContractionBoundary m d := by
  have h := population_factor_axis_identification (canonicalJointGap m) B d
    (d^2*compactContractionBoundary m d) hB hfactor
    (canonicalJointGap_hasDerivAt_population_zero m hm d hd hd0)
  exact mul_left_cancel₀ (pow_ne_zero 2 hd0) h

end
end ExactHoeffding
