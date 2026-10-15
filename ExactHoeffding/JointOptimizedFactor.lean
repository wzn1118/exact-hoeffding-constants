import ExactHoeffding.JointCoordinateFactor
import ExactHoeffding.OptimalProxyAsymptotics

/-! # Exact two-parameter factor of the actual normalized optimal-proxy gap -/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

theorem jointNormalizedValue_physical_of_global (m : ℕ) (hm : 0 < m)
    (τ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (N k : ℕ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hmN : m ≤ N)
    (he : p.1=1/(N:ℝ)) (hd : p.2=1-2*(k:ℝ)/N)
    (hglobal : ∀ t : ℝ, jointProxyExtension m p.1 p.2 t ≤
      jointProxyExtension m p.1 p.2 (τ p)) :
    jointNormalizedValue m τ p=normalizedHypergeomProxy N k m := by
  have hbridge (u : ℝ) : jointProxyExtension m p.1 p.2 u =
      actualHypergeomProxy N k m u := by
    rw [he,hd]
    exact jointProxyExtension_hypergeom N k m u hN hk hmN hm
  have hopt : hypergeomOptimalProxy N k m =
      jointProxyExtension m p.1 p.2 (τ p) := by
    rw [hbridge]
    exact hypergeomOptimalProxy_eq_actual_global N k m hk hmN (τ p)
      (by simpa only [hbridge] using hglobal)
  have h := jointNormalizedValue_hypergeom m N k τ hN hk hmN hm
  have hp : p=(1/(N:ℝ),1-2*(k:ℝ)/N) := by ext <;> assumption
  rw [hp] at hopt ⊢
  exact h hopt

/-- The factor is constructed from actual jointly analytic global optimizers;
the conclusion identifies the supremum-defined hypergeometric gap itself. -/
theorem normalizedHypergeomProxy_continuous_joint_gap_factor
    (m : ℕ) (hm : 0 < m) :
    ∃ B : ℝ × ℝ → ℝ, Continuous B ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → p.1=1/(N:ℝ) → p.2=1-2*(k:ℝ)/N →
        normalizedHypergeomProxy N k 1 - normalizedHypergeomProxy N k m =
          p.1*p.2^2*B p) := by
  obtain ⟨τ₁,h₁,hz₁,hmax₁,hbal₁,href₁⟩ :=
    jointProxyExtension_analytic_global_optimizer 1 (by omega)
  obtain ⟨τm,hmτ,hzm,hmaxm,hbalm,hrefm⟩ :=
    jointProxyExtension_analytic_global_optimizer m hm
  have hpop := jointOptimizedGap_population_axis_zero m hm τ₁ τm hmax₁ hmaxm
  have hbal : ∀ᶠ e in 𝓝 (0 : ℝ), jointOptimizedGap m τ₁ τm (e,0)=0 := by
    filter_upwards [jointNormalizedValue_balanced 1 (by omega) τ₁ hbal₁,
      jointNormalizedValue_balanced m hm τm hbalm] with e h1 hm'
    simp only [jointOptimizedGap,h1,hm',sub_self]
  have href : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0),
      jointOptimizedGap m τ₁ τm (p.1,-p.2)=jointOptimizedGap m τ₁ τm p := by
    filter_upwards [jointNormalizedValue_reflection 1 (by omega) τ₁ h₁ hz₁ href₁,
      jointNormalizedValue_reflection m hm τm hmτ hzm hrefm] with p h1 hm'
    simp only [jointOptimizedGap,h1,hm']
  obtain ⟨B,hB,hfactor⟩ := analytic_even_coordinate_factor (jointOptimizedGap m τ₁ τm)
    (jointOptimizedGap_analytic m hm τ₁ τm h₁ hmτ hz₁ hzm) hpop hbal href
  refine ⟨B,hB,?_⟩
  filter_upwards [hfactor,hmax₁,hmaxm] with p hp h1 hm'
  intro N k hN hk hmN he hd
  have hv1 := jointNormalizedValue_physical_of_global 1 (by omega) τ₁ p N k
    hN hk (by omega) he hd ((h1 (τ₁ p)).mpr rfl)
  have hvm := jointNormalizedValue_physical_of_global m hm τm p N k
    hN hk hmN he hd ((hm' (τm p)).mpr rfl)
  simpa only [jointOptimizedGap,hv1,hvm] using hp

/-- The value at the removable balanced corner is identified from the actual
odd nearly-balanced laws and their proved cubic optimal-proxy asymptotics. -/
theorem normalizedHypergeomProxy_joint_gap_factor_origin
    (m : ℕ) (hm : 0 < m) (B : ℝ × ℝ → ℝ) (hB : ContinuousAt B (0,0))
    (hfactor : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), ∀ N k : ℕ,
      2 ≤ N → k ≤ N → m ≤ N → p.1=1/(N:ℝ) → p.2=1-2*(k:ℝ)/N →
      normalizedHypergeomProxy N k 1 - normalizedHypergeomProxy N k m =
        p.1*p.2^2*B p) : B (0,0)=2*((m:ℝ)-1)/3 := by
  let N : ℕ → ℕ := fun n => 2*n+1
  let J : ℕ → ℕ := fun n => n
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    dsimp [N]
    omega
  have he : Tendsto (fun n => 1/(N n:ℝ)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hN
  have hp : Tendsto (fun n => (1/(N n:ℝ),1/(N n:ℝ))) atTop (𝓝 (0,0)) :=
    he.prodMk_nhds he
  have hlimit := odd_nearly_balanced_gap_cubic_limit_along m hm N J hN
    (Filter.Eventually.of_forall fun _ => rfl)
  have heq : (fun n => B (1/(N n:ℝ),1/(N n:ℝ))) =ᶠ[atTop]
      (fun n => (oddHypergeomConstant (N n)-normalizedHypergeomProxy (N n) (J n) m)/
        (1/(N n:ℝ))^3) := by
    filter_upwards [hp.eventually hfactor,eventually_ge_atTop (max m 1)] with n hf hn
    have hlarge : 0<n ∧ m≤N n ∧ 2≤N n := by dsimp [N]; omega
    have hNr : (N n:ℝ) ≠ 0 := by exact_mod_cast (show N n≠0 by omega)
    have hd : 1/(N n:ℝ)=1-2*(n:ℝ)/N n := by
      have hcast : (N n:ℝ)=2*(n:ℝ)+1 := by dsimp [N]; push_cast; ring
      rw [hcast]
      field_simp
      ring
    have h := hf (N n) n hlarge.2.2 (by dsimp [N]; omega) hlarge.2.1 rfl hd
    have hs : normalizedHypergeomProxy (N n) n 1=oddHypergeomConstant (N n) := by
      exact (odd_normalized_proxy_all_equality n n 1 hlarge.1 hlarge.1 (by omega)
        (by omega) (by omega)).mpr ⟨Or.inl rfl,Or.inl rfl⟩
    rw [hs] at h
    dsimp [J]
    rw [h]
    have hden : 1/(N n:ℝ) ≠ 0 := one_div_ne_zero hNr
    field_simp [hden]
  exact tendsto_nhds_unique (hB.tendsto.comp hp) (hlimit.congr' heq.symm)

/-- Exact gap factor with its balanced value, proved for actual optimal
proxies throughout a full two-dimensional neighborhood. -/
theorem normalizedHypergeomProxy_joint_gap_factor_with_origin
    (m : ℕ) (hm : 0 < m) :
    ∃ B : ℝ × ℝ → ℝ, Continuous B ∧ B (0,0)=2*((m:ℝ)-1)/3 ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → p.1=1/(N:ℝ) → p.2=1-2*(k:ℝ)/N →
        normalizedHypergeomProxy N k 1 - normalizedHypergeomProxy N k m =
          p.1*p.2^2*B p) := by
  obtain ⟨B,hB,hfactor⟩ := normalizedHypergeomProxy_continuous_joint_gap_factor m hm
  exact ⟨B,hB,normalizedHypergeomProxy_joint_gap_factor_origin m hm B hB.continuousAt
    hfactor,hfactor⟩

end
end ExactHoeffding
