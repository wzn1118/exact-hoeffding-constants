import ExactHoeffding.RealMarginContinuityTail
import ExactHoeffding.RealMarginFiniteResponse
import ExactHoeffding.RealMarginSmallSupportEquality
import ExactHoeffding.ActualUniqueOptimizer

/-! # Actual global maximizing tilts at every fixed finite population -/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

/-- The balanced removable objective has its sole global maximum at zero. -/
theorem realMarginProxy_balanced_strict (N m : ℕ) (hN : 5 ≤ N) (hm : 0 < m)
    (hNm : 2*m ≤ N) (t : ℝ) (ht : t ≠ 0) :
    realMarginProxy N m 0 t < realMarginProxy N m 0 0 := by
  have hNr : (5:ℝ)≤N := by exact_mod_cast hN
  have hfit : (m:ℝ)≤(N:ℝ)/2 := by
    have : 2*(m:ℝ)≤N := by exact_mod_cast hNm
    linarith
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have hb := realMarginMass_balanced_strict_quadratic m (N:ℝ) t hm hNr hfit ht
  have hc : realMarginCenteredLogMGF N m 0 t <
      ((m:ℝ)*((N:ℝ)-m)/(4*((N:ℝ)-1)))*t^2/2 := by
    have hcenter : realMarginCenteredLogMGF N m 0 t=
        Real.log (finiteMGF (Finset.range (m+1)) (realMarginMass m (1/(N:ℝ)) (1/2))
          (fun i=>(i:ℝ)) t)-(m:ℝ)/2*t := by
      unfold realMarginCenteredLogMGF
      norm_num only [sub_zero]
      ring
    rw [hcenter]
    exact hb
  rw [realMarginProxy_eq_quotient N m 0 t hden ht, realMarginProxy_zero N m 0 hden,
    margin_cumulant2_closed N m hN]
  norm_num only [zero_pow (by omega : (2:ℕ)≠0), sub_zero, mul_one]
  apply (div_lt_iff₀ (sq_pos_of_ne_zero ht)).mpr
  nlinarith

/-- Every compact annulus has a uniform strict gap for nearby actual laws. -/
theorem realMarginProxy_compact_gap (N m : ℕ) (hN : 5 ≤ N) (hm : 0 < m)
    (hNm : 2*m ≤ N) (K : Set ℝ) (hK : IsCompact K)
    (hzero : ∀ t∈K, t ≠ 0) :
    ∀ᶠ d in 𝓝 (0:ℝ), ∀ t∈K,
      realMarginProxy N m d t < realMarginProxy N m d 0 := by
  apply hK.eventually_forall_of_forall_eventually
  intro t ht
  have hbase : ContinuousAt (fun u : ℝ × ℝ => realMarginProxy N m u.1 0) (0,t) :=
    (realMarginProxy_joint_analytic_axis N m hN hNm 0).continuousAt.comp_of_eq
      (f:=fun u:ℝ×ℝ=>(u.1,(0:ℝ))) (continuousAt_fst.prodMk continuousAt_const) rfl
  exact (realMarginProxy_joint_analytic_axis N m hN hNm t).continuousAt.eventually_lt
    hbase (realMarginProxy_balanced_strict N m hN hm hNm t (hzero t ht))

/-- A quantitative positive gap to zero in the true balanced variance. -/
theorem realMarginProxy_balanced_gt_sixteenth (N m:ℕ) (hN:5≤N)
    (hm:0<m) (hNm:2*m≤N) : (m:ℝ)/16<realMarginProxy N m 0 0 := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hNr : (5:ℝ)≤N := by exact_mod_cast hN
  have hNmR : 2*(m:ℝ)≤N := by exact_mod_cast hNm
  rw [realMarginProxy_zero N m 0
    (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne',
    margin_cumulant2_closed N m hN]
  norm_num only [zero_pow (by omega:(2:ℕ)≠0),sub_zero,mul_one]
  apply (lt_div_iff₀ (show 0<4*((N:ℝ)-1) by linarith)).mpr
  nlinarith [mul_pos hmR (show 0<(N:ℝ)-2*m+1 by linarith)]

/-- Global localization is proved from compact gaps and the actual support
bound; no maximizing selection is assumed. -/
theorem realMarginProxy_eventually_outside_lt_zero (N m : ℕ) (hN : 5 ≤ N)
    (hm : 0 < m) (hNm : 2*m ≤ N) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ d in 𝓝 (0:ℝ), ∀ t : ℝ, δ≤|t| →
      realMarginProxy N m d t < realMarginProxy N m d 0 := by
  let K : Set ℝ := Icc (-64) 64 ∩ {t : ℝ | δ≤|t|}
  have hK : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hzero : ∀ t∈K,t≠0 := by
    intro t ht hz
    have h:=ht.2
    simp only [mem_ofPred_eq,hz,abs_zero] at h
    linarith
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hNr : (5:ℝ)≤N := by exact_mod_cast hN
  have hbase : ContinuousAt (fun d=>realMarginProxy N m d 0) 0 :=
    (realMarginProxy_joint_analytic_axis N m hN hNm 0).continuousAt.comp_of_eq
      (f:=fun d:ℝ=>(d,(0:ℝ))) (continuousAt_id.prodMk continuousAt_const) rfl
  have hbase0 : (m:ℝ)/16<realMarginProxy N m 0 0 :=
    realMarginProxy_balanced_gt_sixteenth N m hN hm hNm
  have hbasepos : ∀ᶠ d in 𝓝 (0:ℝ),(m:ℝ)/16<realMarginProxy N m d 0 :=
    continuousAt_const.eventually_lt hbase hbase0
  have hd : ∀ᶠ d in 𝓝 (0:ℝ),|d|<1/(N:ℝ) :=
    continuousAt_id.abs.eventually_lt continuousAt_const (by simpa only [id_eq, abs_zero] using (show (0:ℝ)<1/(N:ℝ) by positivity))
  filter_upwards [realMarginProxy_compact_gap N m hN hm hNm K hK hzero,hbasepos,hd]
    with d hgap hbased hd
  intro t htδ
  by_cases ht64:|t|≤64
  · exact hgap t ⟨abs_le.mp ht64,htδ⟩
  · have habs:64 < |t| := lt_of_not_ge ht64
    have ht:t≠0 := by
      intro hz
      have : (64:ℝ)<0 := by simpa [hz] using habs
      linarith
    have htail:=realMarginProxy_tail_bound N m hN hNm d t hd ht
    have hsmall:4*(m:ℝ)/|t|≤(m:ℝ)/16 := by
      apply (div_le_iff₀ (by linarith : 0 < |t|)).mpr
      nlinarith
    exact (htail.trans hsmall).trans_lt hbased

/-- Every sufficiently small real imbalance has exactly one actual globally
maximizing tilt, also for odd fixed population size. -/
theorem realMarginProxy_eventually_unique_global_max (N m : ℕ) (hN : 5 ≤ N)
    (hm : 0<m) (hNm : 2*m≤N) :
    ∀ᶠ d in 𝓝 (0:ℝ), ∃! t : ℝ, ∀ u : ℝ,
      realMarginProxy N m d u ≤ realMarginProxy N m d t := by
  obtain ⟨δ,hδ,hconc⟩ := realMarginProxy_uniform_strictConcave N m hN hm hNm
  filter_upwards [hconc,
    realMarginProxy_eventually_outside_lt_zero N m hN hm hNm (δ/2) (by linarith)]
    with d hc hl
  exact exists_unique_global_max_of_strictConcave_localized _ δ hδ hc hl

/-- The local implicit critical branch is the unique actual global optimizer
for every sufficiently small real imbalance. -/
theorem realMarginProxy_analytic_global_optimizer (N m : ℕ) (hN : 5 ≤ N)
    (hm : 0<m) (hNm : 2*m≤N) :
    ∃ τ : ℝ→ℝ, AnalyticAt ℝ τ 0 ∧ τ 0=0 ∧
      (∀ᶠ u : ℝ×ℝ in 𝓝 (0,0),
        deriv (realMarginProxy N m u.1) u.2=0 ↔ τ u.1=u.2) ∧
      (∀ᶠ d in 𝓝 (0:ℝ), ∀ t : ℝ,
        (∀ u : ℝ, realMarginProxy N m d u ≤ realMarginProxy N m d t) ↔ t=τ d) := by
  obtain ⟨τ,hτ,hτ0,heq⟩ := realMarginProxy_analytic_critical_branch N m hN hm hNm
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp heq
  refine ⟨τ,hτ,hτ0,heq,?_⟩
  filter_upwards [realMarginProxy_eventually_unique_global_max N m hN hm hNm,
    realMarginProxy_eventually_outside_lt_zero N m hN hm hNm (r/2) (by linarith),
    isOpen_Ioo.mem_nhds (show (0:ℝ)∈Ioo (-r/2) (r/2) by constructor <;> linarith)]
    with d hex hl hd
  have hforward (t:ℝ) (hmax : ∀u:ℝ, realMarginProxy N m d u ≤ realMarginProxy N m d t) :
      t=τ d := by
    have ht : |t|<r/2 := by
      by_contra hn
      exact (not_lt_of_ge (hmax 0)) (hl t (le_of_not_gt hn))
    have hdist : dist (d,t) ((0:ℝ),(0:ℝ))<r := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, max_lt_iff]
      constructor
      · exact abs_lt.mpr ⟨by linarith [hd.1],by linarith [hd.2]⟩
      · linarith
    have hlocal : IsLocalMax (realMarginProxy N m d) t := Filter.Eventually.of_forall hmax
    exact ((hball hdist).mp hlocal.deriv_eq_zero).symm
  intro t
  refine ⟨hforward t,?_⟩
  intro ht
  obtain ⟨v,hv,_⟩ := hex
  have hvτ := hforward v hv
  simpa only [ht,hvτ] using hv

end
end ExactHoeffding
