import ExactHoeffding.JointCoordinateFactor
import ExactHoeffding.JointContactFirstCorrection
import ExactHoeffding.CompactContractionBoundary
import ExactHoeffding.RealMarginEvenOddTaylor
import Mathlib.Analysis.Convex.Deriv

/-! # Uniform strict local decrease of the actual jointly optimized value -/
namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

/-- The actual binomial sharp coefficient has quadratic correction -1/3. -/
theorem binomial_proxy_ratio_quadratic_limit :
    Tendsto (fun d:ℝ => (d/Real.artanh d-1)/d^2)
      (𝓝[≠] 0) (𝓝 (-1/3:ℝ)) := by
  have h := (artanh_contraction_numerator_cubic_limit.div artanh_ratio_limit_zero
    (by norm_num)).sub_const 1
  have hconst : (2/3:ℝ)/1-1= -1/3 := by norm_num
  rw [hconst] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (isOpen_Ioo.mem_nhds (show (0:ℝ)∈Ioo (-1:ℝ) 1 by norm_num))] with d hd hs
  have hart : Real.artanh d≠0 := by
    intro hz
    rcases Real.artanh_eq_zero_iff.mp hz with hleft | hzero | hright
    · linarith [hs.1]
    · exact hd hzero
    · linarith [hs.2]
  dsimp only [Pi.div_apply] 
  field_simp [show d≠0 from hd,hart]
  ring

/-- An analytic even germ's genuine quadratic quotient fixes its Hessian. -/
theorem analytic_even_deriv2_of_quadratic_limit (f:ℝ→ℝ)
    (hf:AnalyticAt ℝ f 0) (heven:∀ᶠ d in 𝓝 (0:ℝ),f (-d)=f d)
    (c:ℝ) (hlim:Tendsto (fun d=>(f d-f 0)/d^2) (𝓝[≠] 0) (𝓝 c)) :
    iteratedDeriv 2 f 0=2*c := by
  obtain ⟨U,hU,heq,_⟩ := analytic_linear_remainder f hf
  have hd := (analytic_even_germ_odd_derivatives f heven).1
  have hquot : (fun d=>(f d-f 0)/d^2) =ᶠ[𝓝[≠] 0] U := by
    filter_upwards [self_mem_nhdsWithin] with d hd0
    rw [heq d,hd]
    field_simp [show d≠0 from hd0]
    ring
  have hU0 : U 0=c := tendsto_nhds_unique
    (hU.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (hlim.congr' hquot)
  have hfEq : f=(fun d=>f 0+d^2*U d) := by
    funext d
    simpa only [hd,zero_mul,add_zero] using heq d
  rw [hfEq,iteratedDeriv_fun_add (f:=fun _:ℝ=>f 0) (g:=fun d:ℝ=>d^2*U d)
    (by fun_prop) ((analyticAt_id.pow 2).mul hU).contDiffAt,iteratedDeriv_const,
    iteratedDeriv2_quadratic_factor U hU,hU0]
  norm_num

/-- The normalized actual binomial optimum on every constructed global
branch has its true imbalance Hessian equal to -2/3 at balance. -/
theorem jointNormalizedValue_binomial_deriv2 (m:ℕ) (hm:0<m)
    (τ:ℝ×ℝ→ℝ) (hτ:AnalyticAt ℝ τ (0,0)) (hz:τ (0,0)=0)
    (hmax:∀ᶠ p:ℝ×ℝ in 𝓝 (0,0),∀t:ℝ,
      (∀u:ℝ,jointProxyExtension m p.1 p.2 u≤jointProxyExtension m p.1 p.2 t) ↔ t=τ p)
    (hbal:∀ᶠ e in 𝓝 (0:ℝ),τ (e,0)=0)
    (href:∀ᶠ p:ℝ×ℝ in 𝓝 (0,0),τ (p.1,-p.2)= -τ p) :
    iteratedDeriv 2 (fun d=>jointNormalizedValue m τ (0,d)) 0= -2/3 := by
  let f:ℝ→ℝ := fun d=>jointNormalizedValue m τ (0,d)
  have hR := jointNormalizedValue_analytic m hm τ hτ hz
  have hf : AnalyticAt ℝ f 0 := hR.comp_of_eq
    (f:=fun d:ℝ=>((0:ℝ),d)) (analyticAt_const.prod analyticAt_id) rfl
  have hc : Tendsto (fun d:ℝ=>((0:ℝ),d)) (𝓝 0) (𝓝 (0,0)) :=
    continuousAt_const.prodMk continuousAt_id
  have heven:∀ᶠ d in 𝓝 (0:ℝ),f (-d)=f d :=
    hc.eventually (jointNormalizedValue_reflection m hm τ hτ hz href)
  have hf0:f 0=1 := by
    have hb := (jointNormalizedValue_balanced m hm τ hbal).self_of_nhds
    simpa only [f,sub_zero,div_one] using hb
  have hcontact:∀ᶠ d in 𝓝[>] (0:ℝ),f d=d/Real.artanh d := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hc.eventually hmax),
      self_mem_nhdsWithin,eventually_nhdsWithin_of_eventually_nhds
        (isOpen_Iio.mem_nhds (show (0:ℝ)<1 by norm_num))] with d hg hd hd1
    have hbin := (jointProxyExtension_binomial_unique_max m hm d (jointBinomialTilt d)
      ⟨by have : (0:ℝ)<d := hd; linarith,hd1⟩).mpr rfl
    have hbest:jointProxyExtension m 0 d (τ (0,d))=
        jointProxyExtension m 0 d (jointBinomialTilt d) :=
      le_antisymm (hbin (mem_univ _)) (((hg (τ (0,d))).mpr rfl) _)
    dsimp [f,jointNormalizedValue]
    rw [hbest]
    simpa only [mul_zero,sub_zero,mul_one] using
      jointProxyExtension_normalized_contact_zero m hm d hd hd1
  have hright:Tendsto (fun d=>(f d-f 0)/d^2) (𝓝[>] 0) (𝓝 (-1/3:ℝ)) := by
    have h := binomial_proxy_ratio_quadratic_limit.mono_left (nhdsGT_le_nhdsNE 0)
    apply h.congr'
    filter_upwards [hcontact] with d hd
    rw [hd,hf0]
  obtain ⟨U,hU,heq,_⟩ := analytic_linear_remainder f hf
  have hd := (analytic_even_germ_odd_derivatives f heven).1
  have hquot : (fun d=>(f d-f 0)/d^2) =ᶠ[𝓝[>] 0] U := by
    filter_upwards [self_mem_nhdsWithin] with d hd0
    rw [heq d,hd]
    field_simp [ne_of_gt (show 0<d from hd0)]
    ring
  have hU0:U 0= -1/3 := tendsto_nhds_unique
    (hU.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (hright.congr' hquot)
  have hlim:Tendsto (fun d=>(f d-f 0)/d^2) (𝓝[≠] 0) (𝓝 (-1/3:ℝ)) := by
    have h: Tendsto U (𝓝[≠] (0:ℝ)) (𝓝 (U 0)) :=
      hU.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    rw [hU0] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with d hd0
    rw [heq d,hd]
    field_simp [show d≠0 from hd0]
    ring
  have hs := analytic_even_deriv2_of_quadratic_limit f hf heven (-1/3) hlim
  convert hs using 1
  ring

/-- A negative imbalance Hessian persists uniformly in both independent
parameters. Evenness then makes every positive nearby imbalance strictly
lower as the imbalance increases. -/
theorem jointNormalizedValue_uniform_local_strictAnti (m:ℕ) (hm:0<m) :
    ∃τ:ℝ×ℝ→ℝ, AnalyticAt ℝ τ (0,0) ∧ τ (0,0)=0 ∧
      AnalyticAt ℝ (jointNormalizedValue m τ) (0,0) ∧
      (∀ᶠ p:ℝ×ℝ in 𝓝 (0,0),∀t:ℝ,
        (∀u:ℝ,jointProxyExtension m p.1 p.2 u≤jointProxyExtension m p.1 p.2 t) ↔ t=τ p) ∧
      ∃δ:ℝ,0<δ ∧ ∀ᶠ e in 𝓝 (0:ℝ),
        StrictAntiOn (fun d=>jointNormalizedValue m τ (e,d)) (Icc 0 δ) := by
  obtain ⟨τ,hτ,hz,hmax,hbal,href⟩ := jointProxyExtension_analytic_global_optimizer m hm
  let R:=jointNormalizedValue m τ
  have hR:AnalyticAt ℝ R (0,0) := jointNormalizedValue_analytic m hm τ hτ hz
  have hsecond:=jointNormalizedValue_binomial_deriv2 m hm τ hτ hz hmax hbal href
  have h2 : AnalyticAt ℝ (parameterSecondImbalance R) (0,0) :=
    parameterSecondImbalance_analytic R _ hR
  have h2zero:parameterSecondImbalance R (0,0)= -2/3 := by
    change tiltPartial (tiltPartial R) (0,0)=_
    rw [tiltPartial2_eq_iteratedDeriv2 R (0,0) hR]
    exact hsecond
  have hevent:∀ᶠ p:ℝ×ℝ in 𝓝 (0,0),
      AnalyticAt ℝ R p ∧ parameterSecondImbalance R p<0 :=
    hR.eventually_analyticAt.and (h2.continuousAt.eventually_lt continuousAt_const (by rw [h2zero]; norm_num))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨τ,hτ,hz,hR,hmax,r/2,by linarith,?_⟩
  have heven:=jointNormalizedValue_reflection m hm τ hτ hz href
  filter_upwards [isOpen_Ioo.mem_nhds (show (0:ℝ)∈Ioo (-r/2) (r/2) by constructor <;> linarith),
    parameterPartial_balanced_zero R hR heven] with e he hd0
  have hall (d:ℝ) (hd:d∈Icc (-(r/2)) (r/2)) :
      AnalyticAt ℝ R (e,d) ∧ parameterSecondImbalance R (e,d)<0 := by
    apply hball
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,max_lt_iff]
    constructor
    · exact abs_lt.mpr ⟨by linarith [he.1],by linarith [he.2]⟩
    · exact abs_lt.mpr ⟨by linarith [hd.1],by linarith [hd.2]⟩
  have ha (d:ℝ) (hd:d∈Icc (-(r/2)) (r/2)) : AnalyticAt ℝ (fun d=>R (e,d)) d :=
    (hall d hd).1.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hconc:StrictConcaveOn ℝ (Icc (-(r/2)) (r/2)) (fun d=>R (e,d)) := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc _ _)
      (fun d hd=>(ha d hd).continuousAt.continuousWithinAt)
    intro d hd
    rw [←iteratedDeriv_eq_iterate]
    rw [←tiltPartial2_eq_iteratedDeriv2 R (e,d) (hall d (interior_subset hd)).1]
    exact (hall d (interior_subset hd)).2
  have hderivanti:=hconc.strictAntiOn_deriv (fun d hd=>(ha d hd).differentiableAt)
  have hdz:deriv (fun d=>R (e,d)) 0=0 := by
    rw [←parameterPartial_snd_eq_deriv R (e,0) (hall 0 (by constructor <;> linarith)).1.differentiableAt]
    exact hd0
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (fun d hd=>(ha d ⟨by linarith [hd.1],hd.2⟩).continuousAt.continuousWithinAt)
  intro d hd
  rw [interior_Icc] at hd
  have hlt:=hderivanti (show (0:ℝ)∈Icc (-(r/2)) (r/2) by constructor <;> linarith)
    ⟨by linarith [hd.1],hd.2.le⟩ hd.1
  rwa [hdz] at hlt

end
end ExactHoeffding
