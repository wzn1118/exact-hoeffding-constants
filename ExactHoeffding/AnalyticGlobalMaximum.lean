import ExactHoeffding.JointImplicitTiltAt
import ExactHoeffding.JointGlobalOptimizer

/-! # Analytic global maxima from a strict limiting maximum and uniform tails -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

/-- Uniform tails and a strict unique limiting maximum localize every
competitor, including unbounded real tilts. -/
theorem analytic_family_global_localization
    (F : (ℝ × ℝ) × ℝ → ℝ) (p₀ : ℝ × ℝ) (T C : ℝ)
    (hA : ∀ t, AnalyticAt ℝ F (p₀,t))
    (hstrict : ∀ t, t ≠ T → F (p₀,t) < F (p₀,T))
    (hbase : 0 < F (p₀,T)) (hC : 0 ≤ C)
    (htail : ∀ᶠ p in 𝓝 p₀, ∀ t : ℝ, t ≠ 0 → F (p,t) ≤ C/|t|)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ p in 𝓝 p₀, ∀ t : ℝ, δ ≤ |t-T| → F (p,t) < F (p,T) := by
  let B := F (p₀,T)
  let R : ℝ := 2*C/B+1
  have hB : 0 < B := hbase
  have hR : 0 < R := by dsimp [R]; positivity
  let K : Set ℝ := Icc (-R) R ∩ {t : ℝ | δ ≤ |t-T|}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_id.sub continuous_const).abs)
  have hgap : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ K, F (p,t) < F (p,T) := by
    apply hK.eventually_forall_of_forall_eventually
    intro t ht
    have hc : ContinuousAt (fun u : (ℝ × ℝ) × ℝ => F (u.1,T)) (p₀,t) :=
      (hA T).continuousAt.comp_of_eq
        (continuousAt_fst.prodMk continuousAt_const) rfl
    apply (hA t).continuousAt.eventually_lt hc
    apply hstrict t
    intro hz
    have hx := ht.2
    simp only [mem_ofPred_eq,hz,sub_self,abs_zero] at hx
    linarith
  have hbasep : ∀ᶠ p in 𝓝 p₀, B/2 < F (p,T) := by
    apply continuousAt_const.eventually_lt
      ((hA T).continuousAt.comp_of_eq
        (continuousAt_id.prodMk continuousAt_const) rfl)
    change B/2 < B
    linarith
  filter_upwards [hgap,hbasep,htail] with p hp hb ht
  intro t hdist
  by_cases hsmall : |t| ≤ R
  · exact hp t ⟨abs_le.mp hsmall,hdist⟩
  · have hlarge : R < |t| := lt_of_not_ge hsmall
    have ht0 : t ≠ 0 := by
      intro hz
      simp only [hz,abs_zero] at hlarge
      linarith
    have htailSmall : C/|t| ≤ B/2 := by
      apply (div_le_iff₀ (hR.trans hlarge)).mpr
      have he : R*B=2*C+B := by dsimp [R]; field_simp [hB.ne']
      nlinarith
    exact ((ht t ht0).trans htailSmall).trans_lt hb

/-- A negative limiting tilt Hessian yields one common interval of strict
concavity after translating the limiting optimizer to zero. -/
theorem analytic_family_uniform_strictConcave
    (F : (ℝ × ℝ) × ℝ → ℝ) (p₀ : ℝ × ℝ) (T : ℝ)
    (hA : AnalyticAt ℝ F (p₀,T))
    (hneg : jointTiltPartial (jointTiltPartial F) (p₀,T) < 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ p in 𝓝 p₀,
      StrictConcaveOn ℝ (Icc (-δ) δ) (fun t => F (p,T+t)) := by
  have h2 := analyticAt_jointTiltPartial _ _ (analyticAt_jointTiltPartial F _ hA)
  have hevent : ∀ᶠ u in 𝓝 (p₀,T),
      AnalyticAt ℝ F u ∧ jointTiltPartial (jointTiltPartial F) u < 0 :=
    hA.eventually_analyticAt.and (h2.continuousAt.eventually_lt continuousAt_const hneg)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r/2,by linarith,?_⟩
  filter_upwards [Metric.ball_mem_nhds p₀ (by linarith : 0<r/2)] with p hp
  have hall (t : ℝ) (ht : t ∈ Icc (-(r/2)) (r/2)) :
      AnalyticAt ℝ F (p,T+t) ∧ jointTiltPartial (jointTiltPartial F) (p,T+t) < 0 := by
    apply hball
    rw [Prod.dist_eq,Real.dist_eq,show T+t-T=t by ring,max_lt_iff]
    constructor
    · have hd : dist p p₀ < r/2 := hp
      linarith
    · exact abs_lt.mpr ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hcont : ContinuousOn (fun t => F (p,T+t)) (Icc (-(r/2)) (r/2)) := by
    intro t ht
    exact ((hall t ht).1.comp_of_eq
      (f := fun u : ℝ => (p,T+u))
      (analyticAt_const.prod (analyticAt_const.add analyticAt_id)) rfl).continuousAt.continuousWithinAt
  apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _) hcont
  intro t ht
  have ht' := interior_subset ht
  rw [← iteratedDeriv_eq_iterate]
  change iteratedDeriv 2 ((fun v => F (p,v)) ∘ (fun u => T+u)) t < 0
  rw [show iteratedDeriv 2 ((fun v => F (p,v)) ∘ (fun u => T+u)) t =
      iteratedDeriv 2 (fun v => F (p,v)) (T+t) from
        congrFun (iteratedDeriv_comp_const_add (f := fun v => F (p,v)) (n := 2) (s := T)) t]
  rw [← jointTiltPartial2_eq_iteratedDeriv2 F (p,T+t) (hall t ht').1]
  exact (hall t ht').2

/-- A strict global limiting maximum with negative Hessian continues as
one analytic, uniquely globally optimizing branch. -/
theorem analytic_family_analytic_global_optimizer
    (F : (ℝ × ℝ) × ℝ → ℝ) (p₀ : ℝ × ℝ) (T C : ℝ)
    (hA : ∀ t, AnalyticAt ℝ F (p₀,t))
    (hstrict : ∀ t, t ≠ T → F (p₀,t) < F (p₀,T))
    (hbase : 0 < F (p₀,T)) (hC : 0 ≤ C)
    (htail : ∀ᶠ p in 𝓝 p₀, ∀ t : ℝ, t ≠ 0 → F (p,t) ≤ C/|t|)
    (hneg : jointTiltPartial (jointTiltPartial F) (p₀,T) < 0) :
    ∃ τ : ℝ × ℝ → ℝ, AnalyticAt ℝ τ p₀ ∧ τ p₀=T ∧
      (∀ᶠ p in 𝓝 p₀, ∀ t : ℝ,
        (∀ u : ℝ, F (p,u) ≤ F (p,t)) ↔ t=τ p) := by
  have hmax0 : IsLocalMax (fun t => F (p₀,t)) T := by
    apply Filter.Eventually.of_forall
    intro t
    by_cases ht : t=T
    · rw [ht]
    · exact (hstrict t ht).le
  have hzero : jointTiltPartial F (p₀,T)=0 := by
    rw [jointTiltPartial_eq_deriv F (p₀,T) (hA T)]
    exact hmax0.deriv_eq_zero
  obtain ⟨τ,hτ,hτ0,heq⟩ := analytic_implicit_joint_tilt_at (jointTiltPartial F)
    p₀ T (analyticAt_jointTiltPartial F (p₀,T) (hA T)) hzero (ne_of_lt hneg)
  obtain ⟨δ,hδ,hconc⟩ := analytic_family_uniform_strictConcave F p₀ T (hA T) hneg
  have hex : ∀ᶠ p in 𝓝 p₀, ∃ t : ℝ, ∀ u : ℝ, F (p,u) ≤ F (p,t) := by
    filter_upwards [hconc,
      analytic_family_global_localization F p₀ T C hA hstrict hbase hC htail
        (δ/2) (by linarith)] with p hc hl
    obtain ⟨t,ht,_⟩ := exists_unique_global_max_of_strictConcave_localized
      (fun u => F (p,T+u)) δ hδ hc (by
        intro u hu
        have hu' : δ/2 ≤ |T+u-T| := by
          simpa only [add_sub_cancel_left] using hu
        simpa only [add_zero] using hl (T+u) hu')
    refine ⟨T+t,?_⟩
    intro u
    simpa only [add_sub_cancel] using ht (u-T)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp
    (heq.and (hA T).eventually_analyticAt)
  refine ⟨τ,hτ,hτ0,?_⟩
  filter_upwards [hex,
    analytic_family_global_localization F p₀ T C hA hstrict hbase hC htail
      (r/2) (by linarith),
    Metric.ball_mem_nhds p₀ (by linarith : 0<r/2)] with p hp hl hpn
  have hforward (t : ℝ) (hmax : ∀ u : ℝ, F (p,u) ≤ F (p,t)) : t=τ p := by
    have hdist : |t-T| < r/2 := by
      by_contra hn
      exact (not_lt_of_ge (hmax T)) (hl t (le_of_not_gt hn))
    have hpt : dist (p,t) (p₀,T) < r := by
      rw [Prod.dist_eq,Real.dist_eq,max_lt_iff]
      constructor
      · have hd : dist p p₀ < r/2 := hpn
        linarith
      · linarith
    have ha : AnalyticAt ℝ F (p,t) := (hball hpt).2
    have hlocal : IsLocalMax (fun u => F (p,u)) t := Filter.Eventually.of_forall hmax
    have hcrit : jointTiltPartial F (p,t)=0 := by
      rw [jointTiltPartial_eq_deriv F (p,t) ha]
      exact hlocal.deriv_eq_zero
    exact ((hball hpt).1.mp hcrit).symm
  intro t
  refine ⟨hforward t,?_⟩
  intro ht
  obtain ⟨v,hv⟩ := hp
  have hvτ := hforward v hv
  simpa only [ht,hvτ] using hv

end
end ExactHoeffding
