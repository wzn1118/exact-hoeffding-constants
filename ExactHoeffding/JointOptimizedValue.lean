import ExactHoeffding.JointGlobalOptimizer
import ExactHoeffding.NormalizedProxy

/-! # Actual jointly analytic optimized values and exact symmetry -/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

/-- The normalized value on a constructed joint optimizing branch. -/
def jointNormalizedValue (m : ℕ) (τ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  4*jointProxyExtension m p.1 p.2 (τ p) / ((m : ℝ)*(1-(m : ℝ)*p.1))

theorem jointNormalizedValue_analytic (m : ℕ) (hm : 0 < m)
    (τ : ℝ × ℝ → ℝ) (hτ : AnalyticAt ℝ τ (0, 0)) (hz : τ (0, 0)=0) :
    AnalyticAt ℝ (jointNormalizedValue m τ) (0, 0) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  exact (analyticAt_const.mul (jointProxyExtension_critical_value_analytic m τ hτ hz)).div
    (analyticAt_const.mul (analyticAt_const.sub (analyticAt_const.mul analyticAt_fst)))
    (by simpa only [mul_zero, sub_zero, mul_one] using hmR)

/-- The completed objective at a global maximum is the least quadratic
proxy, including the case in which its maximizing tilt is zero. -/
theorem hypergeomOptimalProxy_eq_actual_global (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ)
    (hmax : ∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) :
    hypergeomOptimalProxy N k m = actualHypergeomProxy N k m t := by
  have hquot (u : ℝ) (hu : u ≠ 0) : actualHypergeomProxy N k m u =
      2*hypergeomCenteredLogMGF N k m u/u^2 := by
    rw [actualHypergeomProxy, if_neg hu, hypergeom_centered_log_identity N k m hk hm]
    rfl
  apply le_antisymm
  · unfold hypergeomOptimalProxy optimalProxy
    apply csSup_le (proxyQuotientSet_nonempty _)
    rintro v ⟨u, hu, rfl⟩
    rw [← hquot u hu]
    exact hmax u
  · by_cases ht : t=0
    · subst t
      rw [actualHypergeomProxy, if_pos rfl, hypergeom_cumulant2_complete N k m hk hm]
      rw [← hypergeomTiltVariance_zero N k m hk hm]
      exact hypergeomOptimalProxy_ge_variance N k m hk hm
    · unfold hypergeomOptimalProxy optimalProxy
      apply le_csSup (proxyQuotientSet_bddAbove _ _
        (hypergeom_uniform_log_laplace_domination N k m hk hm))
      exact ⟨t, ht, hquot t ht⟩

/-- The normalizing convention agrees with the paper's hypergeometric
normalization at each physical parameter. -/
theorem jointNormalizedValue_hypergeom (m N k : ℕ) (τ : ℝ × ℝ → ℝ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hm : m ≤ N) (hmpos : 0 < m)
    (hopt : hypergeomOptimalProxy N k m =
      jointProxyExtension m (1/(N : ℝ)) (1-2*(k : ℝ)/N)
        (τ (1/(N : ℝ), 1-2*(k : ℝ)/N))) :
    jointNormalizedValue m τ (1/(N : ℝ), 1-2*(k : ℝ)/N) =
      normalizedHypergeomProxy N k m := by
  unfold jointNormalizedValue normalizedHypergeomProxy
  rw [← hopt]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  by_cases hNm : (N : ℝ)-(m : ℝ)=0
  · have hmn : 1-(m : ℝ)*(1/(N : ℝ))=0 := by field_simp; linarith
    rw [hNm, hmn]
    simp
  · field_simp [hNr, hNm]

/-- The constructed branch gives the exact balanced normalized value,
not just its asymptotic expansion. -/
theorem jointNormalizedValue_balanced (m : ℕ) (hm : 0 < m)
    (τ : ℝ × ℝ → ℝ) (hbal : ∀ᶠ e in 𝓝 (0 : ℝ), τ (e, 0)=0) :
    ∀ᶠ e in 𝓝 (0 : ℝ), jointNormalizedValue m τ (e, 0)=1/(1-e) := by
  have h1 : ∀ᶠ e in 𝓝 (0 : ℝ), 1-e ≠ 0 :=
    (continuous_const.sub continuous_id).continuousAt.eventually_ne (by norm_num)
  have h2 : ∀ᶠ e in 𝓝 (0 : ℝ), 1-(m : ℝ)*e ≠ 0 :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne
      (by norm_num)
  filter_upwards [hbal, h1, h2] with e he he1 he2
  unfold jointNormalizedValue
  rw [he, jointProxyExtension_zero_tilt_formula m e 0 he1]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  norm_num
  field_simp [hmR, he1, he2]

/-- Exact reflection of the optimized objective follows from reflection of
the law and oddness of its unique maximizing branch. -/
theorem jointNormalizedValue_reflection (m : ℕ) (hm : 0 < m)
    (τ : ℝ × ℝ → ℝ) (hτ : AnalyticAt ℝ τ (0, 0)) (hz : τ (0, 0)=0)
    (href : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), τ (p.1, -p.2) = -τ p) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      jointNormalizedValue m τ (p.1, -p.2) = jointNormalizedValue m τ p := by
  have hc : Tendsto (fun p : ℝ × ℝ => (p, -τ p)) (𝓝 (0, 0))
      (𝓝 ((0, 0), 0)) := by
    have h : ContinuousAt (fun p : ℝ × ℝ => (p, -τ p)) (0, 0) :=
      continuousAt_id.prodMk hτ.continuousAt.neg
    simpa only [hz, neg_zero] using h.tendsto
  filter_upwards [href, hc.eventually (jointProxyExtension_reflection_eventually m hm)]
    with p hp hq
  unfold jointNormalizedValue
  rw [hp]
  rw [show jointProxyExtension m p.1 (-p.2) (-τ p) =
      jointProxyExtension m p.1 p.2 (τ p) by simpa only [neg_neg] using hq]


/-- One analytic normalized germ equals the actual supremum-defined optimal
proxy for every nearby physical law.  Its optimizer is obtained from the joint
implicit theorem and global localization, and is not an input hypothesis. -/
theorem normalizedHypergeomProxy_joint_analytic_value (m : ℕ) (hm : 0 < m) :
    ∃ τ : ℝ × ℝ → ℝ, AnalyticAt ℝ τ (0, 0) ∧ τ (0, 0)=0 ∧
      AnalyticAt ℝ (jointNormalizedValue m τ) (0, 0) ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → p.1=1/(N : ℝ) → p.2=1-2*(k : ℝ)/N →
        jointNormalizedValue m τ p=normalizedHypergeomProxy N k m) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), jointNormalizedValue m τ (e, 0)=1/(1-e)) ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
        jointNormalizedValue m τ (p.1, -p.2)=jointNormalizedValue m τ p) := by
  obtain ⟨τ, hτ, hz, hmax, hbal, href⟩ := jointProxyExtension_analytic_global_optimizer m hm
  refine ⟨τ, hτ, hz, jointNormalizedValue_analytic m hm τ hτ hz, ?_,
    jointNormalizedValue_balanced m hm τ hbal,
    jointNormalizedValue_reflection m hm τ hτ hz href⟩
  filter_upwards [hmax] with p hp
  intro N k hN hk hmN he hd
  have hbridge (u : ℝ) : jointProxyExtension m p.1 p.2 u =
      actualHypergeomProxy N k m u := by
    rw [he, hd]
    exact jointProxyExtension_hypergeom N k m u hN hk hmN hm
  have hglobal := (hp (τ p)).mpr rfl
  have hopt : hypergeomOptimalProxy N k m = jointProxyExtension m p.1 p.2 (τ p) := by
    rw [hbridge]
    exact hypergeomOptimalProxy_eq_actual_global N k m hk hmN (τ p)
      (by simpa only [hbridge] using hglobal)
  have hvalue := jointNormalizedValue_hypergeom m N k τ hN hk hmN hm
  have hpEq : p=(1/(N : ℝ), 1-2*(k : ℝ)/N) := by ext <;> assumption
  rw [hpEq] at hopt ⊢
  exact hvalue hopt

end

end ExactHoeffding
