import ExactHoeffding.RealMarginOptimizedSecond
import ExactHoeffding.RealMarginResponseSymmetry
import ExactHoeffding.RealMarginEvenOddTaylor
import ExactHoeffding.RealMarginOptimalProxyValue

/-! # Exact finite-population imbalance response of the actual global optimum -/
namespace ExactHoeffding
noncomputable section
open Filter Asymptotics
open scoped Topology

/-- The complete actual fixed-population response: the global optimizer is
analytic and unique, odd in imbalance, with slope `T`; its normalized value
is even with quadratic coefficient `-A`. Both remainders are analytic. -/
theorem realMargin_exact_imbalance (N m:ℕ) (hN:5≤N) (hm:0<m) (hNm:2*m≤N) :
    ∃τ U V:ℝ→ℝ, AnalyticAt ℝ τ 0 ∧ AnalyticAt ℝ U 0 ∧ AnalyticAt ℝ V 0 ∧
      τ 0=0 ∧ HasDerivAt τ (imbalanceT N m) 0 ∧
      (∀ᶠ d in 𝓝 (0:ℝ),∀t:ℝ,
        (∀u:ℝ,realMarginProxy N m d u≤realMarginProxy N m d t) ↔ t=τ d) ∧
      (∀ᶠ d in 𝓝 (0:ℝ),τ (-d)= -τ d) ∧
      (∀ᶠ d in 𝓝 (0:ℝ),IsOptimalQuadraticProxy (realMarginCenteredLogMGF N m d)
        (realMarginProxy N m d (τ d)) ∧
        optimalProxy (realMarginCenteredLogMGF N m d)=realMarginProxy N m d (τ d)) ∧
      (∀ᶠ d in 𝓝 (0:ℝ),
        (∀i∈Finset.range (m+1),0<realMarginMass m (1/(N:ℝ)) ((1-d)/2) i) ∧
          ∑i∈Finset.range (m+1),realMarginMass m (1/(N:ℝ)) ((1-d)/2) i=1) ∧
      (∀d:ℝ,τ d=imbalanceT N m*d+d^3*U d) ∧
      (∀d:ℝ,4*(N:ℝ)*realMarginProxy N m d (τ d)/((m:ℝ)*((N:ℝ)-m))=
        (N:ℝ)/((N:ℝ)-1)-imbalanceA N m*d^2+d^4*V d) ∧
      (fun d=>τ d-imbalanceT N m*d) =O[𝓝 0] (fun d=>d^3) ∧
      (fun d=>4*(N:ℝ)*realMarginProxy N m d (τ d)/((m:ℝ)*((N:ℝ)-m))-
        (N:ℝ)/((N:ℝ)-1)+imbalanceA N m*d^2) =O[𝓝 0] (fun d=>d^4) := by
  obtain ⟨τ,hτ,hz,hcrit,hglobal⟩ := realMarginProxy_analytic_global_optimizer N m hN hm hNm
  have hT := realMarginProxy_critical_branch_hasDerivAt N m hN hm hNm τ hτ hz hcrit
  have hodd := realMarginProxy_global_branch_odd N m hN hNm τ hglobal
  obtain ⟨U,hU,hUeq,hUO⟩ := analytic_odd_linear_cubic_remainder τ hτ hz hodd
  let R:ℝ→ℝ := fun d=>4*(N:ℝ)*realMarginProxy N m d (τ d)/((m:ℝ)*((N:ℝ)-m))
  have hQ := realMarginProxy_joint_analytic N m
    (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have hR : AnalyticAt ℝ R 0 :=
    (analyticAt_const.mul (hQ.comp_of_eq
      (f:=fun d:ℝ=>(d,τ d)) (analyticAt_id.prod hτ) (by simp only [hz]))).div_const
  have hNr:(5:ℝ)≤N := by exact_mod_cast hN
  have hmR:(0:ℝ)<m := by exact_mod_cast hm
  have hNmR:2*(m:ℝ)≤N := by exact_mod_cast hNm
  have hR0:R 0=(N:ℝ)/((N:ℝ)-1) := by
    dsimp [R]
    rw [hz,realMarginProxy_zero N m 0
      (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne',
      margin_cumulant2_closed N m hN]
    norm_num only [zero_pow (by omega:(2:ℕ)≠0),sub_zero,mul_one]
    field_simp [show (m:ℝ)≠0 by linarith,show (N:ℝ)-m≠0 by linarith,
      show (N:ℝ)-1≠0 by linarith]
  have heven:∀ᶠ d in 𝓝 (0:ℝ),R (-d)=R d := by
    filter_upwards [realMarginProxy_optimized_value_even N m hN hNm τ hodd] with d hd
    dsimp [R]
    rw [hd]
  have hR2:iteratedDeriv 2 R 0/2= -imbalanceA N m := by
    rw [realMarginProxy_normalized_value_deriv2 N m hN hm hNm τ hτ hz hT.deriv]
    ring
  obtain ⟨V,hV,hVeq,hVO⟩ := analytic_even_quadratic_quartic_remainder R hR heven
  have hprob : ∀ᶠ d in 𝓝 (0:ℝ),
      (∀i∈Finset.range (m+1),0<realMarginMass m (1/(N:ℝ)) ((1-d)/2) i) ∧
        ∑i∈Finset.range (m+1),realMarginMass m (1/(N:ℝ)) ((1-d)/2) i=1 := by
    have hd : ∀ᶠ d in 𝓝 (0:ℝ),|d|<1/(N:ℝ) :=
      continuousAt_id.abs.eventually_lt continuousAt_const (by simpa only [id_eq, abs_zero] using (show (0:ℝ)<1/(N:ℝ) by positivity))
    filter_upwards [hd] with d hd
    refine ⟨?_,(realMarginMass_near_balanced_probability N m (by omega) hNm d hd).2⟩
    intro i hi
    exact realMarginMass_pos_near_balanced N m (by omega) hNm d hd i
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
  refine ⟨τ,U,V,hτ,hU,hV,hz,hT,hglobal,hodd,
    realMarginProxy_optimal_value_eventually N m hN hNm τ hglobal,hprob,?_,?_,?_,?_⟩
  · simpa only [hT.deriv] using hUeq
  · change ∀d:ℝ,R d=(N:ℝ)/((N:ℝ)-1)-imbalanceA N m*d^2+d^4*V d
    simpa only [hR0,hR2,neg_mul,sub_eq_add_neg] using hVeq
  · simpa only [hT.deriv] using hUO
  · change (fun d=>R d-(N:ℝ)/((N:ℝ)-1)+imbalanceA N m*d^2) =O[𝓝 0] (fun d=>d^4)
    simpa only [hR0,hR2,neg_mul,sub_neg_eq_add] using hVO

/-- The one-draw quadratic imbalance coefficient is the scaled Bernoulli
coefficient exactly. -/
theorem imbalanceA_singleton (N:ℕ) :
    imbalanceA N 1=(N:ℝ)/(3*((N:ℝ)-1)) := by
  simp [imbalanceA]

/-- The exact actual finite-population response separates every multi-draw
law from the one-draw law at quadratic order. -/
theorem realMargin_exact_imbalance_strict_coefficient (N m:ℕ) (hN:5≤N)
    (hm:2≤m) (hNm:2*m≤N) : imbalanceA N 1 < imbalanceA N m := by
  rw [imbalanceA_singleton]
  linarith [imbalanceA_strict N m hN hm hNm]

/-- The strict coefficient difference gives actual Bernoulli domination for
all sufficiently small nonzero real imbalances at each fixed finite N. -/
theorem realMargin_optimal_proxy_eventually_lt_singleton (N m:ℕ) (hN:5≤N)
    (hm:2≤m) (hNm:2*m≤N) :
    ∀ᶠ d in 𝓝 (0:ℝ),d≠0 →
      4*(N:ℝ)*optimalProxy (realMarginCenteredLogMGF N m d)/((m:ℝ)*((N:ℝ)-m)) <
        4*(N:ℝ)*optimalProxy (realMarginCenteredLogMGF N 1 d)/((N:ℝ)-1) := by
  obtain ⟨τm,Um,Vm,hτm,hUm,hVm,hzm,hTm,hgm,hom,hopm,hpm,htm,hvm,hum,hvmO⟩ :=
    realMargin_exact_imbalance N m hN (by omega) hNm
  obtain ⟨τ1,U1,V1,hτ1,hU1,hV1,hz1,hT1,hg1,ho1,hop1,hp1,ht1,hv1,hu1,hv1O⟩ :=
    realMargin_exact_imbalance N 1 hN (by omega) (by omega)
  let G:ℝ→ℝ := fun d=>imbalanceA N m-imbalanceA N 1+d^2*(V1 d-Vm d)
  have hG:ContinuousAt G 0 :=
    continuousAt_const.add ((continuousAt_id.pow 2).mul (hV1.continuousAt.sub hVm.continuousAt))
  have hg0:0<G 0 := by
    dsimp [G]
    norm_num only [zero_pow (by omega:(2:ℕ)≠0),zero_mul,add_zero]
    exact sub_pos.mpr (realMargin_exact_imbalance_strict_coefficient N m hN hm hNm)
  filter_upwards [hopm,hop1,continuousAt_const.eventually_lt hG hg0] with d hpm hp1 hgd
  intro hd
  rw [hpm.2,hp1.2]
  have hM:=hvm d
  have h1:=hv1 d
  norm_num only [Nat.cast_one,one_mul] at h1
  have hg:=mul_pos (sq_pos_of_ne_zero hd) hgd
  dsimp [G] at hg
  nlinarith [sq_nonneg d]

end
end ExactHoeffding
