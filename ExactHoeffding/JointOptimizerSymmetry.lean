import ExactHoeffding.JointParameterSymmetry

/-! # Reflection of the jointly analytic critical tilt -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

/-- The full removable objective has exact reflection symmetry on a
three-variable neighborhood of the balanced limiting point. -/
theorem jointProxyExtension_reflection_eventually (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0),
      jointProxyExtension m u.1.1 (-u.1.2) u.2 =
        jointProxyExtension m u.1.1 u.1.2 (-u.2) := by
  have hden : ∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0),
      scaledFalling 1 u.1.1 m ≠ 0 := by
    have hc : ContinuousAt (fun u : (ℝ × ℝ) × ℝ =>
        scaledFalling 1 u.1.1 m) ((0, 0), 0) :=
      (rescaledPopulationDenom_joint_analytic m (0, 0)).continuousAt.comp_of_eq
        (f := fun u : (ℝ × ℝ) × ℝ => (u.1.1, u.2)) (by fun_prop) rfl
    exact hc.eventually_ne (by simp)
  have he : ∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0), 1-u.1.1 ≠ 0 :=
    (show ContinuousAt (fun u : (ℝ × ℝ) × ℝ => 1-u.1.1) ((0, 0), 0) by
      fun_prop).eventually_ne (by norm_num)
  have hMG : ContinuousAt (fun u : (ℝ × ℝ) × ℝ =>
      jointMGF m u.1.1 u.1.2 (-u.2)) ((0, 0), 0) :=
    (jointMGF_analytic m 0 0).continuousAt.comp_of_eq
      (f := fun u : (ℝ × ℝ) × ℝ => (u.1.1, (u.1.2, -u.2)))
      (by fun_prop) (by simp)
  have hM : ∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0),
      jointMGF m u.1.1 u.1.2 (-u.2) ≠ 0 := hMG.eventually_ne (by simp)
  filter_upwards [hden, he, hM] with u hdu heu hMu
  exact jointProxyExtension_reflection m hm u.1.1 u.1.2 u.2 hdu heu hMu

/-- The critical equation is odd under simultaneous reflection. -/
theorem jointProxyExtension_deriv_reflection_eventually (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0),
      deriv (jointProxyExtension m u.1.1 (-u.1.2)) u.2 =
        -deriv (jointProxyExtension m u.1.1 u.1.2) (-u.2) := by
  filter_upwards [(jointProxyExtension_reflection_eventually m hm).eventually_nhds]
    with u hu
  have hins : ContinuousAt (fun t : ℝ => (u.1, t)) u.2 :=
    continuousAt_const.prodMk continuousAt_id
  have heq : (jointProxyExtension m u.1.1 (-u.1.2)) =ᶠ[𝓝 u.2]
      (fun t => jointProxyExtension m u.1.1 u.1.2 (-t)) := hins.eventually hu
  simpa only [deriv_comp_neg] using heq.deriv_eq

/-- A jointly analytic, locally unique critical branch is odd in the
imbalance coordinate. -/
theorem joint_critical_branch_reflection (m : ℕ) (hm : 0 < m)
    (τ : ℝ × ℝ → ℝ) (hτ : AnalyticAt ℝ τ (0, 0)) (hτzero : τ (0, 0) = 0)
    (heq : ∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0),
      deriv (jointProxyExtension m u.1.1 u.1.2) u.2 = 0 ↔ τ u.1 = u.2) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), τ (p.1, -p.2) = -τ p := by
  have hgraph : ContinuousAt (fun p : ℝ × ℝ => (p, τ p)) (0, 0) :=
    continuousAt_id.prodMk hτ.continuousAt
  have hreflect : ContinuousAt
      (fun p : ℝ × ℝ => ((p.1, -p.2), -τ p)) (0, 0) := by
    exact (continuousAt_fst.prodMk continuousAt_snd.neg).prodMk hτ.continuousAt.neg
  have hgraph' : Tendsto (fun p : ℝ × ℝ => (p, τ p)) (𝓝 (0, 0))
      (𝓝 ((0, 0), 0)) := by simpa only [hτzero] using hgraph.tendsto
  have hreflect' : Tendsto (fun p : ℝ × ℝ => ((p.1, -p.2), -τ p)) (𝓝 (0, 0))
      (𝓝 ((0, 0), 0)) := by simpa only [hτzero, neg_zero] using hreflect.tendsto
  have hnegative : Tendsto (fun p : ℝ × ℝ => (p, -τ p)) (𝓝 (0, 0))
      (𝓝 ((0, 0), 0)) := by
    have hc : ContinuousAt (fun p : ℝ × ℝ => (p, -τ p)) (0, 0) :=
      continuousAt_id.prodMk hτ.continuousAt.neg
    simpa only [hτzero, neg_zero] using hc.tendsto
  filter_upwards [hgraph'.eventually heq, hreflect'.eventually heq,
    hnegative.eventually (jointProxyExtension_deriv_reflection_eventually m hm)]
    with p hp hr hs
  have hc : deriv (jointProxyExtension m p.1 p.2) (τ p) = 0 := hp.mpr rfl
  apply hr.mp
  simpa only [neg_neg, hc, neg_zero] using hs

/-- The joint branch, its local critical-point characterization, its
balanced-axis identity, and its exact imbalance reflection are obtained
together from the actual objective. -/
theorem jointProxyExtension_analytic_critical_branch_symmetric
    (m : ℕ) (hm : 0 < m) :
    ∃ τ : ℝ × ℝ → ℝ, AnalyticAt ℝ τ (0, 0) ∧ τ (0, 0) = 0 ∧
      (∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0),
        deriv (jointProxyExtension m u.1.1 u.1.2) u.2 = 0 ↔ τ u.1 = u.2) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), τ (e, 0) = 0) ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), τ (p.1, -p.2) = -τ p) := by
  obtain ⟨τ, hτ, hz, heq, hbal⟩ :=
    jointProxyExtension_analytic_critical_branch_balanced m hm
  exact ⟨τ, hτ, hz, heq, hbal, joint_critical_branch_reflection m hm τ hτ hz heq⟩

end

end ExactHoeffding
