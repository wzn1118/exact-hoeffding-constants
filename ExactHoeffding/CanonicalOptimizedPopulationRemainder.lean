import ExactHoeffding.CompactCanonicalContraction
import ExactHoeffding.JointOptimizedFirstCorrection
import ExactHoeffding.ActualAnalyticAsymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Uniform second-order population control of the actual canonical optimum -/

namespace ExactHoeffding
noncomputable section
open Filter Set Asymptotics
open scoped Topology

def parameterSecondPopulation (F : ℝ×ℝ→ℝ) : ℝ×ℝ→ℝ :=
  parameterPartial (parameterPartial F (1,0)) (1,0)

def populationQuadraticRemainder (F : ℝ×ℝ→ℝ) (p : ℝ×ℝ) : ℝ :=
  if p.1=0 then parameterSecondPopulation F p/2 else
    (F p-F (0,p.2)-p.1*parameterPartial F (1,0) (0,p.2))/p.1^2

theorem parameterSecondPopulation_eq_iterated (F : ℝ×ℝ→ℝ) (p : ℝ×ℝ)
    (hF : AnalyticAt ℝ F p) :
    parameterSecondPopulation F p=iteratedFDeriv ℝ 2 F p (fun _ => (1,0)) := by
  rw [iteratedFDeriv_two_apply]
  unfold parameterSecondPopulation parameterPartial
  have h := (ContinuousLinearMap.apply ℝ ℝ ((1,0) : ℝ×ℝ)).hasFDerivAt.comp p
    hF.fderiv.differentiableAt.hasFDerivAt
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply]
    using congrArg (fun A : (ℝ×ℝ)→L[ℝ] ℝ => A (1,0)) h.fderiv

/-- The exact second population quotient extends continuously while imbalance
varies; its axis value is one half of the actual second directional derivative. -/
theorem populationQuadraticRemainder_continuousAt_axis (F : ℝ×ℝ→ℝ) (d₀ : ℝ)
    (hF : AnalyticAt ℝ F (0,d₀)) :
    ContinuousAt (populationQuadraticRemainder F) (0,d₀) := by
  have hsecond : ∀ᶠ p in 𝓝 ((0:ℝ),d₀),ContinuousAt (parameterSecondPopulation F) p :=
    hF.eventually_analyticAt.mono fun p hp =>
      (parameterPartial_analytic _ _ p (parameterPartial_analytic F _ p hp)).continuousAt
  obtain ⟨g,hg,hgerm⟩ := continuous_germ_extension_at (parameterSecondPopulation F) (0,d₀) hsecond
  let J : ℝ×ℝ→ℝ := fun p => ∫ r in (0:ℝ)..1,(1-r)*g (r*p.1,p.2)
  have hJ : Continuous J := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact (continuous_const.sub continuous_snd).mul (hg.comp (by fun_prop))
  apply hJ.continuousAt.congr_of_eventuallyEq
  filter_upwards [population_grid_eventually _ d₀ hF.eventually_analyticAt,
    population_grid_eventually _ d₀ hgerm] with p hp hgp
  have hid : F p=F (0,p.2)+p.1*parameterPartial F (1,0) (0,p.2)+p.1^2*J p := by
    have ht := map_add_eq_sum_add_integral_iteratedFDeriv
      (f:=F) (x:=((0:ℝ),p.2)) (y:=(p.1,(0:ℝ))) (n:=1)
      (fun r hr => by simpa using (hp r hr).contDiffAt)
    simp only [Prod.mk_add_mk,Prod.smul_mk,smul_eq_mul,mul_zero,zero_add,add_zero,
      Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.factorial_zero,
      Nat.cast_one,inv_one,one_smul,iteratedFDeriv_zero_apply,
      Nat.factorial_one,iteratedFDeriv_one_apply,pow_one,one_mul] at ht
    have hlinear : fderiv ℝ F (0,p.2) (p.1,0)=p.1*parameterPartial F (1,0) (0,p.2) := by
      rw [show ((p.1,0):ℝ×ℝ)=p.1 • ((1,0):ℝ×ℝ) by ext <;> simp,map_smul]
      rfl
    rw [hlinear] at ht
    change F (p.1,p.2)=_
    rw [ht]
    congr 1
    unfold J
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hr
    change (1-r)*iteratedFDeriv ℝ 2 F (r*p.1,p.2) (fun _ => (p.1,0))=_
    have hscale := (iteratedFDeriv ℝ 2 F (r*p.1,p.2)).map_smul_univ
      (fun _ => p.1) (fun _ => ((1,0):ℝ×ℝ))
    have hs : iteratedFDeriv ℝ 2 F (r*p.1,p.2) (fun _ => (p.1,0))=
        p.1^2*parameterSecondPopulation F (r*p.1,p.2) := by
      rw [parameterSecondPopulation_eq_iterated F _ (hp r hr')]
      simpa [Fin.prod_univ_two,smul_eq_mul,pow_two] using hscale
    rw [hs,← hgp r hr']
    ring
  unfold populationQuadraticRemainder
  split_ifs with he
  · have hc : (fun r:ℝ => (1-r)*g (r*p.1,p.2))=
        fun r:ℝ => (1-r)*parameterSecondPopulation F p := by
      funext r
      have hpz : p=((0:ℝ),p.2) := by ext <;> simp only [he]
      rw [he,mul_zero,hpz]
      have hh := hgp 0 (by simp)
      simpa only [zero_mul] using congrArg (fun v:ℝ => (1-r)*v) hh
    dsimp [J]
    rw [hc,intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (f:=fun _:ℝ => (1:ℝ)) (g:=fun x:ℝ => x)
        intervalIntegrable_const (continuous_id.intervalIntegrable 0 1),
      intervalIntegral.integral_const,integral_id]
    norm_num
    ring
  · exact (div_eq_iff (pow_ne_zero 2 he)).mpr (by nlinarith [hid])

/-- The quotient identity is exact for all real parameters, including the
zero population axis. -/
theorem populationQuadraticRemainder_identity (F : ℝ×ℝ→ℝ) (p : ℝ×ℝ) :
    F p=F (0,p.2)+p.1*parameterPartial F (1,0) (0,p.2)+
      p.1^2*populationQuadraticRemainder F p := by
  unfold populationQuadraticRemainder
  split_ifs with he
  · have hpz : p=((0:ℝ),p.2) := by ext <;> simp only [he]
    rw [hpz]
    simp
  · field_simp
    <;> ring

/-- The second-order remainder of the actual optimized value is uniformly
bounded on every compact interior imbalance interval. -/
theorem jointOptimalValue_uniform_population_remainder (m : ℕ) (hm : 0<m)
    (d₀ : ℝ) (hd₀ : 0≤d₀) (hd₁ : d₀<1) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ e in 𝓝 (0:ℝ),∀ d∈Icc 0 d₀,
      |jointOptimalValue m (e,d)-4*bernoulliSharpBeta (jointSuccessFraction d)-
        e*parameterPartial (jointOptimalValue m) (1,0) (0,d)|≤C*e^2 := by
  let R := populationQuadraticRemainder (jointOptimalValue m)
  have hint : ∀ d∈Icc 0 d₀,d∈Ioo (-1:ℝ) 1 := by
    intro d hd
    constructor <;> linarith [hd.1,hd.2]
  have hc : ∀ d∈Icc 0 d₀,ContinuousAt R (0,d) := fun d hd =>
    populationQuadraticRemainder_continuousAt_axis _ d
      (jointOptimalValue_analytic_full_axis m hm d (hint d hd))
  have haxis : ContinuousOn (fun d:ℝ => |R (0,d)|) (Icc 0 d₀) := by
    intro d hd
    exact ((hc d hd).comp_of_eq (continuousAt_const.prodMk continuousAt_id) rfl).abs.continuousWithinAt
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image haxis
  refine ⟨max M 0+1,by positivity,?_⟩
  have hb : ∀ᶠ e in 𝓝 (0:ℝ),∀ d∈Icc 0 d₀,|R (e,d)|≤max M 0+1 := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro d hd
    have hx : |R (0,d)|<max M 0+1 := by
      have hle := hM (mem_image_of_mem (fun d:ℝ => |R (0,d)|) hd)
      linarith [le_max_left M 0]
    exact (((hc d hd).abs.eventually_lt continuousAt_const hx).mono fun p hp => hp.le)
  filter_upwards [hb] with e he
  intro d hd
  have hi := populationQuadraticRemainder_identity (jointOptimalValue m) (e,d)
  rw [jointOptimalValue_binomial_axis m hm d (hint d hd)] at hi
  have hid : jointOptimalValue m (e,d)-4*bernoulliSharpBeta (jointSuccessFraction d)-
      e*parameterPartial (jointOptimalValue m) (1,0) (0,d)=e^2*R (e,d) := by
    dsimp [R]
    linarith [hi]
  rw [hid,abs_mul,abs_of_nonneg (sq_nonneg e)]
  nlinarith [he d hd,sq_nonneg e]

/-- At each positive interior imbalance the actual optimum has the explicit
first population coefficient and an analytic second-order remainder. -/
theorem jointOptimalValue_first_population_analytic_expansion
    (m : ℕ) (hm : 2≤m) (d : ℝ) (hd₀ : 0<d) (hd₁ : d<1) :
    ∃ R:ℝ→ℝ,AnalyticAt ℝ R 0 ∧
      (∀ e:ℝ,jointOptimalValue m (e,d)=4*bernoulliSharpBeta (jointSuccessFraction d)+
        (((m:ℝ)*(d/Real.artanh d)-((m:ℝ)-1)*d^2/
          ((2*Real.artanh d)^2*jointSuccessFraction d*(1-jointSuccessFraction d))))*e+
          e^2*R e) ∧
      (fun e:ℝ => jointOptimalValue m (e,d)-4*bernoulliSharpBeta (jointSuccessFraction d)-
        (((m:ℝ)*(d/Real.artanh d)-((m:ℝ)-1)*d^2/
          ((2*Real.artanh d)^2*jointSuccessFraction d*(1-jointSuccessFraction d))))*e)
          =O[𝓝 0] (fun e=>e^2) := by
  have hd : d∈Ioo (-1:ℝ) 1 := ⟨by linarith,hd₁⟩
  have ha : AnalyticAt ℝ (fun e:ℝ => jointOptimalValue m (e,d)) 0 :=
    (jointOptimalValue_analytic_full_axis m (by omega) d hd).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  obtain ⟨R,hR,heq,hO⟩ := analytic_linear_remainder _ ha
  have hv := jointOptimalValue_binomial_axis m (by omega) d hd
  have hvd := (jointOptimalValue_hasDerivAt_population_zero m hm d hd₀ hd₁).deriv
  exact ⟨R,hR,by simpa only [hv,hvd] using heq,by simpa only [hv,hvd] using hO⟩

end
end ExactHoeffding
