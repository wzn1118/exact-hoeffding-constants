import ExactHoeffding.JointOptimizerLocalization
import ExactHoeffding.JointOptimizerSymmetry

/-! # The analytic branch is the unique global optimizer of the real law -/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

theorem jointProxyExtension_uniform_strictConcave (m : ℕ) (hm : 0 < m) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      StrictConcaveOn ℝ (Icc (-δ) δ) (jointProxyExtension m p.1 p.2) := by
  let F := jointProxyObjective m
  have hF : AnalyticAt ℝ F ((0, 0), 0) := jointProxyObjective_analytic m
  have h2 : AnalyticAt ℝ (jointTiltPartial (jointTiltPartial F)) ((0, 0), 0) :=
    analyticAt_jointTiltPartial _ _ (analyticAt_jointTiltPartial F _ hF)
  have hneg : jointTiltPartial (jointTiltPartial F) ((0, 0), 0) < 0 := by
    rw [jointProxyObjective_origin_curvature]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    linarith
  have hevent : ∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0),
      AnalyticAt ℝ F u ∧ jointTiltPartial (jointTiltPartial F) u < 0 :=
    hF.eventually_analyticAt.and (h2.continuousAt.eventually_lt continuousAt_const hneg)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r/2, by linarith, ?_⟩
  filter_upwards [Metric.ball_mem_nhds ((0 : ℝ), (0 : ℝ)) (by linarith : 0<r/2)] with p hp
  have hall (t : ℝ) (ht : t ∈ Icc (-(r/2)) (r/2)) :
      AnalyticAt ℝ F (p, t) ∧ jointTiltPartial (jointTiltPartial F) (p, t) < 0 := by
    apply hball
    rw [Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
    constructor
    · have hd : dist p (0, 0) < r/2 := hp
      linarith
    · exact abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcont : ContinuousOn (jointProxyExtension m p.1 p.2) (Icc (-(r/2)) (r/2)) := by
    intro t ht
    exact ((hall t ht).1.comp_of_eq
      (f := fun u : ℝ => (p, u)) (analyticAt_const.prod analyticAt_id) rfl).continuousAt.continuousWithinAt
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hcont
  intro t ht
  have ht' := interior_subset ht
  rw [← iteratedDeriv_eq_iterate]
  change iteratedDeriv 2 (fun u => F (p, u)) t < 0
  rw [← jointTiltPartial2_eq_iteratedDeriv2 F (p, t) (hall t ht').1]
  exact (hall t ht').2

/-- Existence and uniqueness of the global optimum are consequences of the
real finite-support law and the uniform limiting comparison. -/
theorem jointProxyExtension_eventually_exists_unique_global_max (m : ℕ) (hm : 0 < m) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), ∃! t : ℝ, ∀ u : ℝ,
      jointProxyExtension m p.1 p.2 u ≤ jointProxyExtension m p.1 p.2 t := by
  obtain ⟨δ, hδ, hconc⟩ := jointProxyExtension_uniform_strictConcave m hm
  filter_upwards [hconc,
    jointProxyExtension_eventually_outside_lt_zero m hm (δ/2) (by linarith)] with p hc hl
  exact exists_unique_global_max_of_strictConcave_localized _ δ hδ hc hl

/-- A single jointly analytic branch is the actual unique global optimizer
for every nearby real-margin law, with exact balanced and reflection identities. -/
theorem jointProxyExtension_analytic_global_optimizer (m : ℕ) (hm : 0 < m) :
    ∃ τ : ℝ × ℝ → ℝ, AnalyticAt ℝ τ (0, 0) ∧ τ (0, 0) = 0 ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), ∀ t : ℝ,
        (∀ u : ℝ, jointProxyExtension m p.1 p.2 u ≤ jointProxyExtension m p.1 p.2 t) ↔
          t = τ p) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), τ (e, 0) = 0) ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), τ (p.1, -p.2) = -τ p) := by
  obtain ⟨τ, hτ, hz, heq, hbal, href⟩ :=
    jointProxyExtension_analytic_critical_branch_symmetric m hm
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp heq
  refine ⟨τ, hτ, hz, ?_, hbal, href⟩
  filter_upwards [jointProxyExtension_eventually_exists_unique_global_max m hm,
    jointProxyExtension_eventually_outside_lt_zero m hm (r/2) (by linarith),
    Metric.ball_mem_nhds ((0 : ℝ), (0 : ℝ)) (by linarith : 0<r/2)] with p hexists hloc hp
  have hforward (t : ℝ)
      (hmax : ∀ u : ℝ, jointProxyExtension m p.1 p.2 u ≤ jointProxyExtension m p.1 p.2 t) :
      t = τ p := by
    have ht : |t| < r/2 := by
      by_contra hn
      exact (not_lt_of_ge (hmax 0)) (hloc t (le_of_not_gt hn))
    have hdist : dist (p, t) (((0 : ℝ), (0 : ℝ)), (0 : ℝ)) < r := by
      rw [Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
      constructor
      · have hd : dist p (0, 0) < r/2 := hp
        linarith
      · linarith
    have hlocal : IsLocalMax (jointProxyExtension m p.1 p.2) t :=
      Filter.Eventually.of_forall hmax
    exact ((hball hdist).mp hlocal.deriv_eq_zero).symm
  intro t
  refine ⟨hforward t, ?_⟩
  intro ht
  obtain ⟨v, hv, _⟩ := hexists
  have hvτ := hforward v hv
  simpa only [ht, hvτ] using hv

/-- The same jointly analytic optimizer governs every nearby actual
hypergeometric distribution, without fixing the imbalance-to-population ratio. -/
theorem actualHypergeomProxy_joint_analytic_global_optimizer (m : ℕ) (hm : 0 < m) :
    ∃ τ : ℝ × ℝ → ℝ, AnalyticAt ℝ τ (0, 0) ∧ τ (0, 0) = 0 ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → p.1 = 1/(N : ℝ) → p.2 = 1-2*(k : ℝ)/N →
        ∀ t : ℝ, (∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) ↔
          t = τ p) := by
  obtain ⟨τ, hτ, hz, hmax, _, _⟩ := jointProxyExtension_analytic_global_optimizer m hm
  refine ⟨τ, hτ, hz, ?_⟩
  filter_upwards [hmax] with p hp
  intro N k hN hk hmN he hd t
  have hbridge (u : ℝ) : jointProxyExtension m p.1 p.2 u =
      actualHypergeomProxy N k m u := by
    rw [he, hd]
    exact jointProxyExtension_hypergeom N k m u hN hk hmN hm
  simpa only [hbridge] using hp t

end

end ExactHoeffding
