import ExactHoeffding.AuxiliaryCurvature
import Mathlib.Probability.Moments.MGFAnalytic

/-! # Integrated curvature of the actual cumulant-generating function

The domain hypotheses specify exponential integrability on a neighborhood
of the whole tilt segment. No finite-support assumption is used.
-/
namespace ExactHoeffding
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology

/-- The actual CGF of a centered random variable is twice continuously
differentiable near every point of its open exponential-integrability domain. -/
theorem centered_cgf_local_regular {Ω:Type*} [MeasurableSpace Ω]
    (X:Ω→ℝ) (μ:Measure Ω) [IsProbabilityMeasure μ]
    (hmean:(∫ω,X ω ∂μ)=0)
    (hzero:0∈interior (integrableExpSet X μ)) :
    cgf X μ 0=0 ∧ deriv (cgf X μ) 0=0 ∧
      ∀s∈interior (integrableExpSet X μ),ContDiffAt ℝ 2 (cgf X μ) s := by
  refine ⟨cgf_zero,?_,fun s hs=>(analyticAt_cgf hs).contDiffAt⟩
  rw [deriv_cgf_zero hzero,hmean,zero_div]

/-- Integrated curvature for an actual centered random variable, whenever
the full segment from zero to the selected tilt lies in the interior of
the exponential-integrability domain. Both signs of the tilt are included. -/
theorem cgf_centered_integrated_curvature_of_segment {Ω:Type*} [MeasurableSpace Ω]
    (X:Ω→ℝ) (μ:Measure Ω) [IsProbabilityMeasure μ]
    (hmean:(∫ω,X ω ∂μ)=0) (t:ℝ) (ht:t≠0)
    (hsegment:uIcc (0:ℝ) t⊆interior (integrableExpSet X μ)) :
    2*cgf X μ t/t^2=
      2*∫u:ℝ in (0:ℝ)..1,(1-u)*deriv (deriv (cgf X μ)) (u*t) := by
  let ψ:=cgf X μ
  have hmem (u:ℝ) (hu:u∈uIcc (0:ℝ) 1):
      u*t∈interior (integrableExpSet X μ) := by
    apply hsegment
    rw [uIcc_of_le (by norm_num : (0:ℝ)≤1)] at hu
    rcases le_total 0 t with hp | hn
    · rw [uIcc_of_le hp]
      exact ⟨mul_nonneg hu.1 hp,by nlinarith [hu.2]⟩
    · rw [uIcc_of_ge hn]
      exact ⟨by nlinarith [hu.2],mul_nonpos_of_nonneg_of_nonpos hu.1 hn⟩
  have hzero:0∈interior (integrableExpSet X μ):=hsegment (left_mem_uIcc)
  have hz:ψ 0=0:=cgf_zero
  have hdz:deriv ψ 0=0:=by
    dsimp [ψ]
    rw [deriv_cgf_zero hzero,hmean,zero_div]
  let F:ℝ→ℝ:=fun u=>ψ (u*t)+(1-u)*t*deriv ψ (u*t)
  have hF (u:ℝ) (hu:u∈uIcc (0:ℝ) 1):
      HasDerivAt F (t^2*((1-u)*deriv (deriv ψ) (u*t))) u := by
    have ha:AnalyticAt ℝ ψ (u*t):=analyticAt_cgf (hmem u hu)
    have hd:=(hasDerivAt_id u).mul_const t
    have h₁:=ha.differentiableAt.hasDerivAt.comp u hd
    have h₂:=ha.deriv.differentiableAt.hasDerivAt.comp u hd
    have h₃:=(((hasDerivAt_id u).const_sub 1).mul_const t).mul h₂
    apply (h₁.add h₃).congr_deriv
    dsimp
    ring
  have hint:IntervalIntegrable
      (fun u:ℝ=>t^2*((1-u)*deriv (deriv ψ) (u*t))) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have ha:AnalyticAt ℝ ψ (u*t):=analyticAt_cgf (hmem u hu)
    have hmul : ContinuousAt (fun z : ℝ => z * t) u := by
      fun_prop
    have hcomp : ContinuousAt (fun z : ℝ => deriv (deriv ψ) (z * t)) u := by
      exact (ha.deriv.deriv.continuousAt.comp_of_eq
        (f := fun z : ℝ => z * t) (x := u) (y := u*t) hmul rfl)
    exact (continuousAt_const.mul ((continuousAt_const.sub continuousAt_id).mul
      hcomp)).continuousWithinAt
  have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint
  rw [intervalIntegral.integral_const_mul] at hi
  dsimp [F] at hi
  simp only [one_mul,zero_mul,sub_self,mul_zero,add_zero,sub_zero,hz,hdz] at hi
  have hfinal : 2*ψ t/t^2 =
      2*∫u:ℝ in (0:ℝ)..1,(1-u)*deriv (deriv ψ) (u*t) := by
    rw [←hi]
    field_simp
  simpa [ψ] using hfinal

/-- A concrete open interval of finite exponential moments around the
whole tilt segment supplies the intrinsic domain hypothesis. -/
theorem cgf_centered_integrated_curvature_of_neighborhood {Ω:Type*} [MeasurableSpace Ω]
    (X:Ω→ℝ) (μ:Measure Ω) [IsProbabilityMeasure μ]
    (hmean:(∫ω,X ω ∂μ)=0) (t:ℝ) (ht:t≠0) (ε:ℝ) (hε:0<ε)
    (hexp:∀s∈Ioo (min 0 t-ε) (max 0 t+ε),
      Integrable (fun ω=>Real.exp (s*X ω)) μ) :
    2*cgf X μ t/t^2=
      2*∫u:ℝ in (0:ℝ)..1,(1-u)*deriv (deriv (cgf X μ)) (u*t) := by
  apply cgf_centered_integrated_curvature_of_segment X μ hmean t ht
  intro s hs
  apply mem_interior_iff_mem_nhds.mpr
  have hm:s∈Ioo (min 0 t-ε) (max 0 t+ε):=by
    exact ⟨by linarith [hs.1],by linarith [hs.2]⟩
  exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hm) (fun y hy=>hexp y hy)

/-- The full-domain finite-MGF version of the integrated-curvature identity.
Analyticity, C² regularity and both centering identities are derived from
the actual probability law and exponential moments. -/
theorem cgf_centered_integrated_curvature {Ω:Type*} [MeasurableSpace Ω]
    (X:Ω→ℝ) (μ:Measure Ω) [IsProbabilityMeasure μ]
    (hmean:(∫ω,X ω ∂μ)=0)
    (hexp:∀s:ℝ,Integrable (fun ω=>Real.exp (s*X ω)) μ)
    (t:ℝ) (ht:t≠0) :
    2*cgf X μ t/t^2=
      2*∫u:ℝ in (0:ℝ)..1,(1-u)*deriv (deriv (cgf X μ)) (u*t) := by
  have hdom:integrableExpSet X μ=univ:=Set.eq_univ_iff_forall.mpr hexp
  have ha (s:ℝ):AnalyticAt ℝ (cgf X μ) s:=analyticAt_cgf (by simp [hdom])
  have hc:ContDiff ℝ 2 (cgf X μ):=contDiff_iff_contDiffAt.mpr (fun s=>(ha s).contDiffAt)
  apply centered_integrated_curvature _ hc cgf_zero _ t ht
  rw [deriv_cgf_zero (by simp [hdom]),hmean,zero_div]

end
end ExactHoeffding
