import ExactHoeffding.JointFullAxisGlobalOptimizer
import ExactHoeffding.JointOptimizedValue

/-! # The actual optimized value on the full interior binomial axis -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

/-- The actual normalized supremum of the removable quadratic objective. -/
def jointOptimalValue (m : ℕ) (p : ℝ × ℝ) : ℝ :=
  4*sSup (Set.range (jointProxyExtension m p.1 p.2)) /
    ((m : ℝ)*(1-(m : ℝ)*p.1))

theorem jointOptimalValue_eq_at_global_max (m : ℕ) (p : ℝ × ℝ) (t : ℝ)
    (hmax : ∀ u : ℝ, jointProxyExtension m p.1 p.2 u ≤
      jointProxyExtension m p.1 p.2 t) :
    jointOptimalValue m p =
      4*jointProxyExtension m p.1 p.2 t / ((m : ℝ)*(1-(m : ℝ)*p.1)) := by
  have hg : IsGreatest (Set.range (jointProxyExtension m p.1 p.2))
      (jointProxyExtension m p.1 p.2 t) := by
    refine ⟨⟨t,rfl⟩,?_⟩
    rintro _ ⟨u,rfl⟩
    exact hmax u
  unfold jointOptimalValue
  rw [hg.csSup_eq]

/-- A canonical supremum agrees with every locally constructed analytic
optimizing branch; no choice of a branch enters the definition of the value. -/
theorem jointOptimalValue_eventually_eq_branch (m : ℕ)
    (p₀ : ℝ × ℝ) (τ : ℝ × ℝ → ℝ)
    (hmax : ∀ᶠ p in 𝓝 p₀, ∀ t : ℝ,
      (∀ u : ℝ, jointProxyExtension m p.1 p.2 u ≤
        jointProxyExtension m p.1 p.2 t) ↔ t=τ p) :
    jointOptimalValue m =ᶠ[𝓝 p₀] jointNormalizedValue m τ := by
  filter_upwards [hmax] with p hp
  exact jointOptimalValue_eq_at_global_max m p (τ p) ((hp (τ p)).mpr rfl)

/-- The actual normalized supremum is jointly analytic at every interior
point of the entire limiting binomial axis, including balance. -/
theorem jointOptimalValue_analytic_full_axis (m : ℕ) (hm : 0<m)
    (d : ℝ) (hd : d ∈ Ioo (-1 : ℝ) 1) :
    AnalyticAt ℝ (jointOptimalValue m) (0,d) := by
  obtain ⟨τ,hτ,hτ0,hmax⟩ :=
    jointProxyExtension_full_axis_analytic_global_optimizer m hm d hd
  have ha : AnalyticAt ℝ (fun p : ℝ × ℝ =>
      jointProxyExtension m p.1 p.2 (τ p)) (0,d) :=
    (jointProxyObjective_analytic_full_axis m d (jointBinomialTilt d) hd).comp_of_eq
      (f := fun p : ℝ × ℝ => (p,τ p)) (analyticAt_id.prod hτ) (by rw [hτ0])
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnorm : AnalyticAt ℝ (jointNormalizedValue m τ) (0,d) :=
    (analyticAt_const.mul ha).div
      (analyticAt_const.mul (analyticAt_const.sub (analyticAt_const.mul analyticAt_fst)))
      (by simpa only [mul_zero,sub_zero,mul_one] using hmR)
  exact hnorm.congr (jointOptimalValue_eventually_eq_branch m (0,d) τ hmax).symm

/-- Uniformly over every compact interior imbalance interval, the canonical
analytic supremum is the actual finite hypergeometric optimal proxy. -/
theorem jointOptimalValue_eventually_uniform_hypergeom (m : ℕ) (hm : 0<m)
    (d₀ : ℝ) (_hd₀ : 0≤d₀) (hd₁ : d₀<1) :
    ∀ᶠ e in 𝓝 (0 : ℝ), ∀ d ∈ Icc (-d₀) d₀, ∀ N k : ℕ,
      2≤N → k≤N → m≤N → e=1/(N : ℝ) → d=1-2*(k : ℝ)/N →
      jointOptimalValue m (e,d)=normalizedHypergeomProxy N k m := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro d hd
  have hdi : d ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hd.1], by linarith [hd.2]⟩
  obtain ⟨τ,_,_,hmax⟩ :=
    jointProxyExtension_full_axis_analytic_global_optimizer m hm d hdi
  filter_upwards [hmax] with p hp
  intro N k hN hk hmN he hd'
  have hg := (hp (τ p)).mpr rfl
  have hbridge (u : ℝ) : jointProxyExtension m p.1 p.2 u =
      actualHypergeomProxy N k m u := by
    rw [he,hd']
    exact jointProxyExtension_hypergeom N k m u hN hk hmN hm
  have ho : hypergeomOptimalProxy N k m = jointProxyExtension m p.1 p.2 (τ p) := by
    rw [hbridge]
    exact hypergeomOptimalProxy_eq_actual_global N k m hk hmN (τ p)
      (by simpa only [hbridge] using hg)
  rw [jointOptimalValue_eq_at_global_max m p (τ p) hg]
  change jointNormalizedValue m τ p = _
  have hpEq : p=(1/(N : ℝ),1-2*(k : ℝ)/N) := by ext <;> assumption
  rw [hpEq] at ho ⊢
  exact jointNormalizedValue_hypergeom m N k τ hN hk hmN hm ho

end
end ExactHoeffding
