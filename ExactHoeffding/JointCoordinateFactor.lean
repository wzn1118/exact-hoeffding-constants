import ExactHoeffding.JointOptimizedGap
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.TietzeExtension

/-! # Continuous coordinate factorization of a jointly analytic even germ -/

namespace ExactHoeffding

noncomputable section

open Set Filter Metric
open scoped Topology

/-- A fixed-direction derivative of a function of the independent parameters. -/
def parameterPartial (F : ℝ × ℝ → ℝ) (v p : ℝ × ℝ) : ℝ :=
  fderiv ℝ F p v

theorem parameterPartial_analytic (F : ℝ × ℝ → ℝ) (v p : ℝ × ℝ)
    (hF : AnalyticAt ℝ F p) : AnalyticAt ℝ (parameterPartial F v) p := by
  exact (ContinuousLinearMap.apply ℝ ℝ v).analyticAt _ |>.comp_of_eq hF.fderiv rfl

theorem parameterPartial_snd_eq_deriv (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F p) :
    parameterPartial F (0,1) p = deriv (fun d => F (p.1,d)) p.2 := by
  have hi : HasDerivAt (fun d : ℝ => (p.1,d)) (0,1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (hF.hasFDerivAt.comp_hasDerivAt_of_eq p.2 hi rfl).deriv.symm

theorem parameterPartial_fst_eq_deriv (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hF : DifferentiableAt ℝ F p) :
    parameterPartial F (1,0) p = deriv (fun e => F (e,p.2)) p.1 := by
  have hi : HasDerivAt (fun e : ℝ => (e,p.2)) (1,0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact (hF.hasFDerivAt.comp_hasDerivAt_of_eq p.1 hi rfl).deriv.symm

/-- Every continuous germ on the parameter plane has a globally continuous
representative agreeing with it in a neighborhood of the origin. -/
theorem continuous_germ_extension (G : ℝ × ℝ → ℝ)
    (hG : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), ContinuousAt G p) :
    ∃ g : ℝ × ℝ → ℝ, Continuous g ∧ g =ᶠ[𝓝 (0,0)] G := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hG
  let K : Set (ℝ × ℝ) := closedBall (0,0) (r/2)
  have hK : ∀ p ∈ K, ContinuousAt G p := by
    intro p hp
    apply hball
    exact lt_of_le_of_lt hp (half_lt_self hr)
  let f : C(K,ℝ) := ⟨fun p => G p, continuousOn_iff_continuous_domRestrict.mp
    (fun p hp => (hK p hp).continuousWithinAt)⟩
  obtain ⟨g,hg⟩ := f.exists_restrict_eq isClosed_closedBall
  refine ⟨g,g.continuous,?_⟩
  filter_upwards [closedBall_mem_nhds (0,0) (half_pos hr)] with p hp
  exact congrArg (fun h : C(K,ℝ) => h ⟨p,hp⟩) hg

/-- The twice differentiated imbalance coordinate. -/
def parameterSecondImbalance (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  parameterPartial (parameterPartial F (0,1)) (0,1)

/-- The mixed population derivative of the imbalance curvature. -/
def parameterMixedThird (F : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  parameterPartial (parameterSecondImbalance F) (1,0)

theorem parameterSecondImbalance_analytic (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hF : AnalyticAt ℝ F p) : AnalyticAt ℝ (parameterSecondImbalance F) p :=
  parameterPartial_analytic _ _ p (parameterPartial_analytic F _ p hF)

theorem parameterMixedThird_analytic (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hF : AnalyticAt ℝ F p) : AnalyticAt ℝ (parameterMixedThird F) p :=
  parameterPartial_analytic _ _ p (parameterSecondImbalance_analytic F p hF)

/-- The second imbalance derivative is the corresponding iterated Fréchet
coefficient, with no univariate regularity assumption hidden in the notation. -/
theorem parameterSecondImbalance_eq_iterated (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hF : AnalyticAt ℝ F p) :
    parameterSecondImbalance F p = iteratedFDeriv ℝ 2 F p (fun _ => (0,1)) := by
  rw [iteratedFDeriv_two_apply]
  unfold parameterSecondImbalance parameterPartial
  have h := (ContinuousLinearMap.apply ℝ ℝ ((0,1) : ℝ × ℝ)).hasFDerivAt.comp p
    hF.fderiv.differentiableAt.hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    using congrArg (fun A : (ℝ × ℝ) →L[ℝ] ℝ => A (0,1)) h.fderiv

/-- Reflection forces the first imbalance derivative to vanish on the
balanced axis throughout a neighborhood, not merely at the origin. -/
theorem parameterPartial_balanced_zero (F : ℝ × ℝ → ℝ)
    (hF : AnalyticAt ℝ F (0,0))
    (heven : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), F (p.1,-p.2)=F p) :
    ∀ᶠ e in 𝓝 (0 : ℝ), parameterPartial F (0,1) (e,0)=0 := by
  have hc : Tendsto (fun e : ℝ => (e,(0 : ℝ))) (𝓝 0) (𝓝 (0,0)) :=
    continuousAt_id.prodMk continuousAt_const
  filter_upwards [hc.eventually hF.eventually_analyticAt,
    hc.eventually heven.eventually_nhds] with e ha hr
  have hs : (fun d : ℝ => F (e,-d)) =ᶠ[𝓝 0] (fun d => F (e,d)) := by
    exact (continuousAt_const.prodMk continuousAt_id).tendsto.eventually hr
  have hder := hs.deriv_eq
  have hn := deriv_comp_neg (f := fun d : ℝ => F (e,d)) (x := (0 : ℝ))
  change deriv (fun d : ℝ => F (e,-d)) 0 = -deriv (fun d : ℝ => F (e,d)) (-0) at hn
  rw [hn] at hder
  simp only [neg_zero] at hder
  rw [parameterPartial_snd_eq_deriv F (e,0) ha.differentiableAt]
  linarith

/-- Exact zero of the original population axis implies exact zero of its
imbalance curvature on that axis. -/
theorem parameterSecondImbalance_population_zero (F : ℝ × ℝ → ℝ)
    (hF : AnalyticAt ℝ F (0,0))
    (hzero : ∀ᶠ d in 𝓝 (0 : ℝ), F (0,d)=0) :
    ∀ᶠ d in 𝓝 (0 : ℝ), parameterSecondImbalance F (0,d)=0 := by
  have hc : Tendsto (fun d : ℝ => ((0 : ℝ),d)) (𝓝 0) (𝓝 (0,0)) :=
    continuousAt_const.prodMk continuousAt_id
  have hfirst : (fun d : ℝ => parameterPartial F (0,1) (0,d)) =ᶠ[𝓝 0]
      (fun _ => (0 : ℝ)) := by
    filter_upwards [hc.eventually hF.eventually_analyticAt,
      hzero.eventually_nhds] with d ha hz
    have heq : (fun x : ℝ => F (0,x)) =ᶠ[𝓝 d] (fun _ => (0 : ℝ)) := hz
    rw [parameterPartial_snd_eq_deriv F (0,d) ha.differentiableAt, heq.deriv_eq]
    simp
  filter_upwards [hc.eventually hF.eventually_analyticAt,
    hfirst.eventually_nhds] with d ha hz
  have heq : (fun x : ℝ => parameterPartial F (0,1) (0,x)) =ᶠ[𝓝 d]
      (fun _ => (0 : ℝ)) := hz
  rw [parameterSecondImbalance,
    parameterPartial_snd_eq_deriv _ (0,d)
      (parameterPartial_analytic F _ _ ha).differentiableAt, heq.deriv_eq]
  simp

/-- A neighborhood is stable uniformly under independent contractions of
both coordinates by numbers in the unit interval. -/
theorem parameter_grid_eventually (P : ℝ × ℝ → Prop)
    (hP : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), P p) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), ∀ r ∈ Icc (0 : ℝ) 1,
      ∀ s ∈ Icc (0 : ℝ) 1, P (r*p.1,s*p.2) := by
  have h : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0),
      ∀ q ∈ (Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1),
        P (q.1*p.1,q.2*p.2) := by
    apply (isCompact_Icc.prod isCompact_Icc).eventually_forall_of_forall_eventually
    intro q hq
    have hc : ContinuousAt (fun u : (ℝ × ℝ) × (ℝ × ℝ) =>
      (u.2.1*u.1.1,u.2.2*u.1.2)) ((0,0),q) := by fun_prop
    have hc' : Tendsto (fun u : (ℝ × ℝ) × (ℝ × ℝ) =>
        (u.2.1*u.1.1,u.2.2*u.1.2)) (𝓝 ((0,0),q)) (𝓝 (0,0)) := by
      convert hc.tendsto using 1 <;> simp
    exact hc'.eventually hP
  filter_upwards [h] with p hp
  exact fun r hr s hs => hp (r,s) ⟨hr,hs⟩

/-- An explicit globally continuous extension of the mixed Taylor
coefficient, integrated over the two independent contraction parameters. -/
def parameterIntegralFactor (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, (1-s)*(∫ r in (0 : ℝ)..1, g (r*p.1,s*p.2))

theorem parameterIntegralFactor_continuous (g : ℝ × ℝ → ℝ) (hg : Continuous g) :
    Continuous (parameterIntegralFactor g) := by
  have hi : Continuous (fun u : (ℝ × ℝ) × ℝ =>
      ∫ r in (0 : ℝ)..1, g (r*u.1.1,u.2*u.1.2)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hg.comp (by fun_prop)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (continuous_const.sub continuous_snd).mul hi

theorem parameterSecondImbalance_scaled (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (d : ℝ)
    (hF : AnalyticAt ℝ F p) :
    iteratedFDeriv ℝ 2 F p (fun _ => (0,d)) =
      d^2*parameterSecondImbalance F p := by
  rw [parameterSecondImbalance_eq_iterated F p hF]
  have h := (iteratedFDeriv ℝ 2 F p).map_smul_univ (fun _ => d)
    (fun _ => ((0,1) : ℝ × ℝ))
  simpa [Fin.prod_univ_two, smul_eq_mul, pow_two] using h

/-- The fundamental theorem and quadratic Taylor formula give the exact
coordinate factor, including points on either zero axis. -/
theorem parameterIntegralFactor_identity (F g : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (hF : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      AnalyticAt ℝ F (r*p.1,s*p.2))
    (hbal : F (p.1,0)=0)
    (hfirst : parameterPartial F (0,1) (p.1,0)=0)
    (hsecond : ∀ s ∈ Icc (0 : ℝ) 1, parameterSecondImbalance F (0,s*p.2)=0)
    (hg : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      g (r*p.1,s*p.2)=parameterMixedThird F (r*p.1,s*p.2)) :
    F p=p.1*p.2^2*parameterIntegralFactor g p := by
  have hcurv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      parameterSecondImbalance F (p.1,s*p.2) =
        p.1*(∫ r in (0 : ℝ)..1, g (r*p.1,s*p.2)) := by
    have hcont : ContinuousOn (fun r : ℝ =>
        parameterMixedThird F (r*p.1,s*p.2)) (Icc (0 : ℝ) 1) := by
      intro r hr
      have hc : ContinuousAt (fun x : ℝ => (x*p.1,s*p.2)) r := by fun_prop
      exact ((parameterMixedThird_analytic F _ (hF r hr s hs)).continuousAt.comp_of_eq hc rfl).continuousWithinAt
    have hder : ∀ r ∈ Icc (0 : ℝ) 1,
        HasDerivAt (fun e : ℝ => parameterSecondImbalance F (e,s*p.2))
          (parameterMixedThird F (r*p.1,s*p.2)) (r*p.1) := by
      intro r hr
      have ha := (parameterSecondImbalance_analytic F _ (hF r hr s hs)).differentiableAt
      have hi : HasDerivAt (fun e : ℝ => (e,s*p.2)) (1,0) (r*p.1) :=
        (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
      exact ha.hasFDerivAt.comp_hasDerivAt_of_eq _ hi rfl
    have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
      (z₀ := (0 : ℝ)) (z₁ := p.1) (f := fun e => parameterSecondImbalance F (e,s*p.2))
      (f' := fun e => parameterMixedThird F (e,s*p.2))
      (by simpa only [zero_add, smul_eq_mul] using hcont)
      (by simpa only [zero_add, smul_eq_mul] using hder)
    simp only [zero_add, hsecond s hs, sub_zero, smul_eq_mul] at h
    rw [← h]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    exact (hg r (by simpa only [uIcc_of_le zero_le_one] using hr) s hs).symm
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := F) (x := (p.1,(0 : ℝ))) (y := ((0 : ℝ),p.2)) (n := 1)
    (fun s hs => by simpa using (hF 1 (by simp) s hs).contDiffAt)
  simp only [Prod.mk_add_mk, Prod.smul_mk, smul_eq_mul, mul_zero, zero_add, add_zero,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.factorial_zero,
    Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply,
    Nat.factorial_one, iteratedFDeriv_one_apply, pow_one] at ht
  have hlinear : fderiv ℝ F (p.1,0) (0,p.2)=0 := by
    rw [show ((0,p.2) : ℝ × ℝ)=p.2 • ((0,1) : ℝ × ℝ) by ext <;> simp,
      map_smul, smul_eq_mul]
    change p.2*parameterPartial F (0,1) (p.1,0)=0
    rw [hfirst,mul_zero]
  simp only [hbal,hlinear,mul_zero,zero_add,one_mul] at ht
  change F (p.1,p.2)=_
  rw [ht]
  unfold parameterIntegralFactor
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hs
  change (1-s)*iteratedFDeriv ℝ 2 F (p.1,s*p.2) (fun _ => (0,p.2)) = _
  rw [parameterSecondImbalance_scaled F _ p.2 (by simpa using hF 1 (by simp) s hs'),
    hcurv s hs']
  ring

/-- A jointly analytic germ, even in imbalance and zero on both axes,
has an exact continuous `e*d²` factor in a full two-dimensional neighborhood. -/
theorem analytic_even_coordinate_factor (F : ℝ × ℝ → ℝ)
    (hF : AnalyticAt ℝ F (0,0))
    (hpop : ∀ᶠ d in 𝓝 (0 : ℝ), F (0,d)=0)
    (hbal : ∀ᶠ e in 𝓝 (0 : ℝ), F (e,0)=0)
    (heven : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), F (p.1,-p.2)=F p) :
    ∃ B : ℝ × ℝ → ℝ, Continuous B ∧
      (∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), F p=p.1*p.2^2*B p) := by
  obtain ⟨g,hg,hgerm⟩ := continuous_germ_extension (parameterMixedThird F)
    (hF.eventually_analyticAt.mono fun p hp =>
      (parameterMixedThird_analytic F p hp).continuousAt)
  refine ⟨parameterIntegralFactor g,parameterIntegralFactor_continuous g hg,?_⟩
  have hP := parameter_grid_eventually _ hF.eventually_analyticAt
  have hG := parameter_grid_eventually _ hgerm
  have hB : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), F (p.1,0)=0 :=
    (continuousAt_fst : ContinuousAt (fun p : ℝ × ℝ => p.1) (0,0)).tendsto.eventually hbal
  have hD : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), parameterPartial F (0,1) (p.1,0)=0 :=
    (continuousAt_fst : ContinuousAt (fun p : ℝ × ℝ => p.1) (0,0)).tendsto.eventually (parameterPartial_balanced_zero F hF heven)
  have hS : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), ∀ s ∈ Icc (0 : ℝ) 1,
      parameterSecondImbalance F (0,s*p.2)=0 := by
    have hh : ∀ᶠ p : ℝ × ℝ in 𝓝 (0,0), parameterSecondImbalance F (0,p.2)=0 :=
      (continuousAt_snd : ContinuousAt (fun p : ℝ × ℝ => p.2) (0,0)).tendsto.eventually (parameterSecondImbalance_population_zero F hF hpop)
    filter_upwards [parameter_grid_eventually _ hh] with p hp
    exact fun s hs => hp 0 (by simp) s hs
  filter_upwards [hP,hG,hB,hD,hS] with p hp hgp hb hd hs
  exact parameterIntegralFactor_identity F g p hp hb hd hs hgp

end
end ExactHoeffding
