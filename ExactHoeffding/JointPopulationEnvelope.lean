import ExactHoeffding.JointCoordinateFactor
import ExactHoeffding.JointMGFFirstCorrection
import ExactHoeffding.JointBinomialOptimizer
import ExactHoeffding.CompactContractionBoundary

/-! # First population correction of the actual optimized objective -/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

/-- Closed first population derivative of the actual removable objective
at every nonzero tilt and every interior success proportion. -/
theorem jointProxyExtension_hasDerivAt_population_zero (m : ℕ) (hm : 2 ≤ m)
    (d t : ℝ) (hd : d ∈ Ioo (-1 : ℝ) 1) (ht : t ≠ 0) :
    HasDerivAt (fun e => jointProxyExtension m e d t)
      (((m:ℝ)*((m:ℝ)-1)/t^2) *
        (1-(jointSuccessFraction d*Real.exp (2*t)+(1-jointSuccessFraction d))/
          (1-jointSuccessFraction d+jointSuccessFraction d*Real.exp t)^2)) 0 := by
  have hp : 0 < jointSuccessFraction d := by unfold jointSuccessFraction; linarith [hd.2]
  have hp1 : jointSuccessFraction d < 1 := by unfold jointSuccessFraction; linarith [hd.1]
  have heq : (fun e => jointProxyExtension m e d t) =ᶠ[𝓝 (0 : ℝ)]
      (fun e => 2*(Real.log (finiteMGF (Finset.range (m+1))
        (realMarginMass m e (jointSuccessFraction d)) (fun i => (i:ℝ)) t) -
          (m:ℝ)*jointSuccessFraction d*t)/t^2) := by
    have hden : ∀ᶠ e in 𝓝 (0 : ℝ), scaledFalling 1 e m ≠ 0 :=
      ((rescaledPopulationDenom_joint_analytic m (0,0)).comp_of_eq
        (f := fun e : ℝ => (e,(0 : ℝ)))
        (analyticAt_id.prod analyticAt_const) rfl).continuousAt.eventually_ne (by simp)
    filter_upwards [hden] with e he
    rw [jointProxyExtension_eq_quotient m (by omega) e d t ht,
      jointMGF_realMargin m e d t he]
    rfl
  have h := ((realMarginCenteredLogMGF_hasDerivAt_population_zero m hm
    (jointSuccessFraction d) t hp hp1).const_mul 2).div_const (t^2)
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  ring

/-- The envelope derivative: movement of an actual maximizing tilt contributes
zero, so the derivative of the optimized value is the population partial. -/
theorem jointProxyObjective_envelope_deriv (m : ℕ) (τ : ℝ × ℝ → ℝ)
    (d : ℝ) (hτ : AnalyticAt ℝ τ (0,d))
    (hQ : AnalyticAt ℝ (jointProxyObjective m) ((0,d),τ (0,d)))
    (hmax : ∀ t : ℝ, jointProxyExtension m 0 d t ≤
      jointProxyExtension m 0 d (τ (0,d))) :
    deriv (fun e => jointProxyExtension m e d (τ (e,d))) 0 =
      deriv (fun e => jointProxyExtension m e d (τ (0,d))) 0 := by
  have ht : IsLocalMax (fun t => jointProxyExtension m 0 d t) (τ (0,d)) :=
    Filter.Eventually.of_forall hmax
  have htilt : jointTiltPartial (jointProxyObjective m) ((0,d),τ (0,d))=0 := by
    rw [jointTiltPartial_eq_deriv _ _ hQ]
    exact ht.deriv_eq_zero
  have hi : HasDerivAt (fun e : ℝ => (e,d)) (1,0) 0 :=
    (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
  have hτd := hτ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hi rfl
  have hinner := hi.prodMk hτd
  have houter := hQ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hinner rfl
  have hfixed := hQ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (hi.prodMk (hasDerivAt_const 0 (τ (0,d)))) rfl
  change HasDerivAt (fun e => jointProxyExtension m e d (τ (e,d))) _ 0 at houter
  change HasDerivAt (fun e => jointProxyExtension m e d (τ (0,d))) _ 0 at hfixed
  rw [houter.deriv,hfixed.deriv]
  change fderiv ℝ (jointProxyObjective m) ((0,d),τ (0,d))
    ((1,0), fderiv ℝ τ (0,d) (1,0)) =
      fderiv ℝ (jointProxyObjective m) ((0,d),τ (0,d)) ((1,0),0)
  rw [show (((1,0), fderiv ℝ τ (0,d) (1,0)) : (ℝ × ℝ) × ℝ) =
      ((1,0),0) + (fderiv ℝ τ (0,d) (1,0)) • ((0,0),1) by ext <;> simp,
    map_add,map_smul,smul_eq_mul]
  change _ + _*jointTiltPartial (jointProxyObjective m) ((0,d),τ (0,d)) = _
  rw [htilt,mul_zero,add_zero]

/-- An actual global maximizing branch has the explicit binomial contact
value at zero inverse population. -/
theorem joint_global_branch_at_population_zero (m : ℕ) (hm : 0 < m)
    (τ : ℝ × ℝ → ℝ) (d : ℝ) (hd : d ∈ Ioo (-1 : ℝ) 1)
    (hmax : ∀ t : ℝ, jointProxyExtension m 0 d t ≤
      jointProxyExtension m 0 d (τ (0,d))) : τ (0,d)=jointBinomialTilt d := by
  exact (jointProxyExtension_binomial_unique_max m hm d (τ (0,d)) hd).mp
    (fun t _ => hmax t)

/-- The scalar coefficient furnished by differentiating the true optimized
objective.  This form retains the actual contact tilt and binomial variance. -/
def jointPopulationEnvelopeCoefficient (m : ℕ) (d : ℝ) : ℝ :=
  (m:ℝ)*4*bernoulliSharpBeta (jointSuccessFraction d) +
    4*((m:ℝ)-1)/(jointBinomialTilt d)^2 *
      (1-(jointSuccessFraction d*Real.exp (2*jointBinomialTilt d)+(1-jointSuccessFraction d))/
        (1-jointSuccessFraction d+jointSuccessFraction d*Real.exp (jointBinomialTilt d))^2)

/-- The first inverse-population derivative of the actual jointly optimized
normalized value, with the optimizer-motion term rigorously eliminated. -/
theorem jointNormalizedValue_hasDerivAt_population_zero (m : ℕ) (hm : 2 ≤ m)
    (τ : ℝ × ℝ → ℝ) (d : ℝ) (hd : d ∈ Ioo (-1 : ℝ) 1) (hd0 : d ≠ 0)
    (hτ : AnalyticAt ℝ τ (0,d))
    (hQ : AnalyticAt ℝ (jointProxyObjective m) ((0,d),τ (0,d)))
    (hmax : ∀ t : ℝ, jointProxyExtension m 0 d t ≤
      jointProxyExtension m 0 d (τ (0,d))) :
    HasDerivAt (fun e => jointNormalizedValue m τ (e,d))
      (jointPopulationEnvelopeCoefficient m d) 0 := by
  have ht := joint_global_branch_at_population_zero m (by omega) τ d hd hmax
  have hne := jointBinomialTilt_ne_zero d hd hd0
  have he := jointProxyObjective_envelope_deriv m τ d hτ hQ hmax
  have hfixed := jointProxyExtension_hasDerivAt_population_zero m hm d (jointBinomialTilt d) hd hne
  have hval : HasDerivAt (fun e => jointProxyExtension m e d (τ (e,d)))
      (deriv (fun e => jointProxyExtension m e d (τ (0,d))) 0) 0 := by
    have hi : AnalyticAt ℝ (fun e : ℝ => ((e,d),τ (e,d))) 0 :=
      (analyticAt_id.prod analyticAt_const).prod
        (hτ.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl)
    have ha := hQ.comp_of_eq hi rfl
    rw [← he]
    exact ha.differentiableAt.hasDerivAt
  rw [ht,hfixed.deriv] at hval
  have hden : HasDerivAt (fun e : ℝ => (m:ℝ)*(1-(m:ℝ)*e)) (-(m:ℝ)^2) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).const_mul (m:ℝ)).const_sub 1).const_mul (m:ℝ) using 1 <;> try rfl
    ring
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (show m≠0 by omega)
  have h := (hval.const_mul 4).div hden (by simpa using hmR)
  change HasDerivAt (fun e => jointNormalizedValue m τ (e,d)) _ 0 at h
  apply h.congr_deriv
  rw [ht,jointProxyExtension_binomial_contact m (by omega) d hd]
  unfold jointPopulationEnvelopeCoefficient
  field_simp [hmR]
  <;> ring

/-- For a continuous exact population factor, its boundary value is uniquely
fixed by the derivative of the actual gap. -/
theorem population_factor_axis_identification (F B : ℝ × ℝ → ℝ) (d c : ℝ)
    (hB : ContinuousAt B (0,d))
    (hfactor : ∀ᶠ e in 𝓝 (0 : ℝ), F (e,d)=e*d^2*B (e,d))
    (hder : HasDerivAt (fun e => F (e,d)) c 0) : d^2*B (0,d)=c := by
  have hz : F (0,d)=0 := by simpa using hfactor.self_of_nhds
  have hquot : Tendsto (fun e : ℝ => F (e,d)/e) (𝓝[≠] 0) (𝓝 c) := by
    have h := hder.tendsto_slope_zero
    simpa only [zero_add,hz,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using h
  have hc : ContinuousAt (fun e : ℝ => d^2*B (e,d)) 0 :=
    continuousAt_const.mul (hB.comp_of_eq (continuousAt_id.prodMk continuousAt_const) rfl)
  have heq : (fun e : ℝ => F (e,d)/e) =ᶠ[𝓝[≠] 0] (fun e => d^2*B (e,d)) := by
    filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with e he hne
    have he0 : e≠0 := hne
    rw [he]
    field_simp
  exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds)
    (hquot.congr' heq)

/-- The first-draw objective has no inverse-population dependence before
normalization. -/
theorem jointProxyExtension_single_draw_independent (e d t : ℝ) :
    jointProxyExtension 1 e d t=jointProxyExtension 1 0 d t := by
  simp [jointProxyExtension,jointMGFSlope,jointMGFQuadratic,jointMean]

/-- The actual singleton optimal value has the elementary first population
correction, for any analytic branch representing its global maximum. -/
theorem jointNormalizedValue_singleton_hasDerivAt_population_zero
    (τ : ℝ × ℝ → ℝ) (d : ℝ) (hd : d ∈ Ioo (-1 : ℝ) 1)
    (hτ : AnalyticAt ℝ τ (0,d))
    (hQ : AnalyticAt ℝ (jointProxyObjective 1) ((0,d),τ (0,d)))
    (hmax : ∀ t : ℝ, jointProxyExtension 1 0 d t ≤
      jointProxyExtension 1 0 d (τ (0,d))) :
    HasDerivAt (fun e => jointNormalizedValue 1 τ (e,d))
      (4*bernoulliSharpBeta (jointSuccessFraction d)) 0 := by
  have ht := joint_global_branch_at_population_zero 1 (by omega) τ d hd hmax
  have he := jointProxyObjective_envelope_deriv 1 τ d hτ hQ hmax
  have hfixed : deriv (fun e => jointProxyExtension 1 e d (τ (0,d))) 0=0 := by
    have heq : (fun e => jointProxyExtension 1 e d (τ (0,d))) =
        (fun _ : ℝ => jointProxyExtension 1 0 d (τ (0,d))) := by
      funext e
      exact jointProxyExtension_single_draw_independent e d _
    rw [heq,deriv_const]
  have hval : HasDerivAt (fun e => jointProxyExtension 1 e d (τ (e,d))) 0 0 := by
    have hi : AnalyticAt ℝ (fun e : ℝ => ((e,d),τ (e,d))) 0 :=
      (analyticAt_id.prod analyticAt_const).prod
        (hτ.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl)
    have ha := hQ.comp_of_eq hi rfl
    have h := ha.differentiableAt.hasDerivAt
    change HasDerivAt (fun e => jointProxyExtension 1 e d (τ (e,d)))
      (deriv (fun e => jointProxyExtension 1 e d (τ (e,d))) 0) 0 at h
    rw [he,hfixed] at h
    exact h
  have hden : HasDerivAt (fun e : ℝ => 1-e) (-1) 0 :=
    (hasDerivAt_id (0 : ℝ)).const_sub 1
  have h := (hval.const_mul 4).div hden (by norm_num)
  have hfun : ((fun y => 4*jointProxyExtension 1 y d (τ (y,d))) /
      (fun e : ℝ => 1-e)) = (fun e => jointNormalizedValue 1 τ (e,d)) := by
    funext e
    simp only [Pi.div_apply,jointNormalizedValue,Nat.cast_one,one_mul]
  rw [hfun] at h
  apply h.congr_deriv
  rw [ht,jointProxyExtension_binomial_contact 1 (by omega) d hd]
  norm_num

end
end ExactHoeffding
