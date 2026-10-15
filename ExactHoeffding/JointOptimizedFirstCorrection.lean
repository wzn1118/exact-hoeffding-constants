import ExactHoeffding.JointFullAxisOptimalValue
import ExactHoeffding.JointContactFirstCorrection
import ExactHoeffding.CompactContractionBoundary

/-! # First population derivative of the canonical optimized supremum -/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

private theorem optimized_contact_envelope_deriv (m : ℕ) (τ : ℝ × ℝ → ℝ)
    (d : ℝ) (hτ : AnalyticAt ℝ τ (0,d))
    (hQ : AnalyticAt ℝ (jointProxyObjective m) ((0,d),τ (0,d)))
    (hmax : ∀ t : ℝ, jointProxyExtension m 0 d t ≤
      jointProxyExtension m 0 d (τ (0,d))) :
    deriv (fun e => jointProxyExtension m e d (τ (e,d))) 0 =
      deriv (fun e => jointProxyExtension m e d (τ (0,d))) 0 := by
  have hlocal : IsLocalMax (fun t => jointProxyExtension m 0 d t) (τ (0,d)) :=
    Filter.Eventually.of_forall hmax
  have htilt : jointTiltPartial (jointProxyObjective m) ((0,d),τ (0,d))=0 := by
    rw [jointTiltPartial_eq_deriv _ _ hQ]
    exact hlocal.deriv_eq_zero
  have hi : HasDerivAt (fun e : ℝ => (e,d)) (1,0) 0 :=
    (hasDerivAt_id _).prodMk (hasDerivAt_const _ _)
  have hτd := hτ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hi rfl
  have houter := hQ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (hi.prodMk hτd) rfl
  have hfixed := hQ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (hi.prodMk (hasDerivAt_const 0 (τ (0,d)))) rfl
  change HasDerivAt (fun e => jointProxyExtension m e d (τ (e,d))) _ 0 at houter
  change HasDerivAt (fun e => jointProxyExtension m e d (τ (0,d))) _ 0 at hfixed
  rw [houter.deriv,hfixed.deriv]
  change fderiv ℝ (jointProxyObjective m) ((0,d),τ (0,d))
    ((1,0),fderiv ℝ τ (0,d) (1,0)) =
      fderiv ℝ (jointProxyObjective m) ((0,d),τ (0,d)) ((1,0),0)
  rw [show (((1,0),fderiv ℝ τ (0,d) (1,0)) : (ℝ × ℝ) × ℝ) =
      ((1,0),0) + (fderiv ℝ τ (0,d) (1,0)) • ((0,0),1) by ext <;> simp,
    map_add,map_smul,smul_eq_mul]
  change _ + _*jointTiltPartial (jointProxyObjective m) ((0,d),τ (0,d)) = _
  rw [htilt,mul_zero,add_zero]

/-- The first correction of the actual optimized supremum is the explicit
contact partial: motion of its constructed maximizing branch contributes zero. -/
theorem jointOptimalValue_hasDerivAt_population_zero (m : ℕ) (hm : 2 ≤ m)
    (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    HasDerivAt (fun e => jointOptimalValue m (e,d))
      ((m:ℝ)*(d/Real.artanh d) - ((m:ℝ)-1)*d^2/
        ((2*Real.artanh d)^2*jointSuccessFraction d*(1-jointSuccessFraction d))) 0 := by
  have hd : d ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hd1⟩
  obtain ⟨τ,hτ,hτ0,hmax⟩ :=
    jointProxyExtension_full_axis_analytic_global_optimizer m (by omega) d hd
  have hQ : AnalyticAt ℝ (jointProxyObjective m) ((0,d),τ (0,d)) := by
    rw [hτ0]
    exact jointProxyObjective_analytic_full_axis m d (jointBinomialTilt d) hd
  have henv := optimized_contact_envelope_deriv m τ d hτ hQ
    (((hmax.self_of_nhds) (τ (0,d))).mpr rfl)
  have ha : AnalyticAt ℝ (fun e => jointProxyExtension m e d (τ (e,d))) 0 :=
    hQ.comp_of_eq ((analyticAt_id.prod analyticAt_const).prod
      (hτ.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl)) rfl
  have hpartial := jointProxyExtension_contact_hasDerivAt_population_zero m hm d hd0 hd1
  have hmov := ha.differentiableAt.hasDerivAt
  rw [henv,hτ0,hpartial.deriv] at hmov
  have hden : HasDerivAt (fun e:ℝ => (m:ℝ)*(1-(m:ℝ)*e)) (-(m:ℝ)^2) 0 := by
    have hi : HasDerivAt (fun e:ℝ => 1-(m:ℝ)*e) (-(m:ℝ)) 0 := by
      simpa only [id_eq,mul_one] using
        (((hasDerivAt_id (0:ℝ)).const_mul (m:ℝ)).const_sub 1)
    apply (hi.const_mul (m:ℝ)).congr_deriv
    ring
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (show m≠0 by omega)
  have hnorm := (hmov.const_mul 4).div hden (by simpa using hmR)
  have hfixnorm := (hpartial.const_mul 4).div hden (by simpa using hmR)
  change HasDerivAt (fun e => 4*jointProxyExtension m e d (τ (e,d))/
    ((m:ℝ)*(1-(m:ℝ)*e))) _ 0 at hnorm
  change HasDerivAt (fun e => 4*jointProxyExtension m e d (jointBinomialTilt d)/
    ((m:ℝ)*(1-(m:ℝ)*e))) _ 0 at hfixnorm
  have hformula :=
    (jointProxyExtension_normalized_contact_hasDerivAt_population_zero m hm d hd0 hd1).deriv
  rw [hfixnorm.deriv] at hformula
  have hbranch : HasDerivAt (fun e => jointNormalizedValue m τ (e,d))
      ((m:ℝ)*(d/Real.artanh d) - ((m:ℝ)-1)*d^2/
        ((2*Real.artanh d)^2*jointSuccessFraction d*(1-jointSuccessFraction d))) 0 := by
    apply hnorm.congr_deriv
    simpa only [hτ0] using hformula
  apply hbranch.congr_of_eventuallyEq
  have heq := jointOptimalValue_eventually_eq_branch m (0,d) τ hmax
  exact (continuousAt_id.prodMk continuousAt_const).tendsto.eventually heq

private theorem single_draw_proxy_population_independent (e d t : ℝ) :
    jointProxyExtension 1 e d t=jointProxyExtension 1 0 d t := by
  simp [jointProxyExtension,jointMGFSlope,jointMGFQuadratic,jointMean]

/-- The canonical singleton supremum has its exact population factor on the
whole interior imbalance interval. -/
theorem jointOptimalValue_singleton_closed (e d : ℝ) (hd : d ∈ Ioo (-1:ℝ) 1) :
    jointOptimalValue 1 (e,d) = 4*bernoulliSharpBeta (jointSuccessFraction d)/(1-e) := by
  have hmax : ∀ t, jointProxyExtension 1 e d t ≤
      jointProxyExtension 1 e d (jointBinomialTilt d) := by
    intro t
    rw [single_draw_proxy_population_independent,single_draw_proxy_population_independent]
    exact ((jointProxyExtension_binomial_unique_max 1 (by omega) d (jointBinomialTilt d) hd).mpr rfl) (mem_univ t)
  rw [jointOptimalValue_eq_at_global_max 1 (e,d) _ hmax,
    single_draw_proxy_population_independent,jointProxyExtension_binomial_contact 1 (by omega) d hd]
  norm_num

/-- The canonical singleton first population correction equals its binomial
value, with no chosen optimizing branch in the statement. -/
theorem jointOptimalValue_singleton_hasDerivAt_population_zero (d : ℝ)
    (hd0 : 0 < d) (hd1 : d < 1) :
    HasDerivAt (fun e => jointOptimalValue 1 (e,d)) (d/Real.artanh d) 0 := by
  have hd : d ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hd1⟩
  have hval := jointProxyExtension_normalized_contact_zero 1 (by omega) d hd0 hd1
  rw [jointProxyExtension_binomial_contact 1 (by omega) d hd] at hval
  norm_num only [Nat.cast_one,mul_one,one_mul,div_one] at hval
  have heq : (fun e => jointOptimalValue 1 (e,d)) =
      (fun e => (d/Real.artanh d)/(1-e)) := by
    funext e
    rw [jointOptimalValue_singleton_closed e d hd,hval]
  rw [heq]
  have h := (hasDerivAt_const (0:ℝ) (d/Real.artanh d)).div
    ((hasDerivAt_id (0:ℝ)).const_sub 1) (by norm_num)
  simpa only [id_eq,mul_zero,sub_zero,one_pow,div_one,zero_mul,mul_neg_one,sub_neg_eq_add,
    zero_add,Pi.div_apply] using! h

/-- The explicit first-correction difference divided by squared imbalance is
exactly the continuous coefficient used in the compact contraction argument. -/
theorem joint_contact_first_gap_coefficient (m : ℕ) (d : ℝ)
    (hd0 : 0 < d) (hd1 : d < 1) :
    ((d/Real.artanh d) - ((m:ℝ)*(d/Real.artanh d) - ((m:ℝ)-1)*d^2/
      ((2*Real.artanh d)^2*jointSuccessFraction d*(1-jointSuccessFraction d))))/d^2 =
        compactContractionBoundary m d := by
  have hd : d ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hd1⟩
  have hart : Real.artanh d ≠ 0 := by
    intro hz
    apply jointBinomialTilt_ne_zero d hd hd0.ne'
    simp [jointBinomialTilt,hz]
  have hsq : 1-d^2 ≠ 0 := by nlinarith [hd1]
  have hpq : jointSuccessFraction d*(1-jointSuccessFraction d)=(1-d^2)/4 := by
    unfold jointSuccessFraction
    ring
  rw [show (2*Real.artanh d)^2*jointSuccessFraction d*(1-jointSuccessFraction d) =
      (2*Real.artanh d)^2*(jointSuccessFraction d*(1-jointSuccessFraction d)) by ring,hpq]
  rw [compactContractionBoundary,if_neg hd0.ne']
  unfold artanhContractionFactor
  field_simp [hd0.ne',hart,hsq]
  ring

/-- The actual canonical optimized gap has the manuscript's population
boundary derivative at every positive interior imbalance. -/
theorem jointOptimalValue_gap_hasDerivAt_population_zero (m : ℕ) (hm : 2 ≤ m)
    (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    HasDerivAt (fun e => (jointOptimalValue 1 (e,d)-jointOptimalValue m (e,d))/d^2)
      (compactContractionBoundary m d) 0 := by
  have h := ((jointOptimalValue_singleton_hasDerivAt_population_zero d hd0 hd1).sub
    (jointOptimalValue_hasDerivAt_population_zero m hm d hd0 hd1)).div_const (d^2)
  exact h.congr_deriv (joint_contact_first_gap_coefficient m d hd0 hd1)

/-- A derivative-only form for the continuous factorization of the canonical gap. -/
theorem jointOptimalValue_gap_population_deriv_div_sq (m : ℕ) (hm : 2 ≤ m)
    (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    deriv (fun e => jointOptimalValue 1 (e,d)-jointOptimalValue m (e,d)) 0 / d^2 =
      compactContractionBoundary m d := by
  have h := (jointOptimalValue_singleton_hasDerivAt_population_zero d hd0 hd1).sub
    (jointOptimalValue_hasDerivAt_population_zero m hm d hd0 hd1)
  change HasDerivAt (fun e => jointOptimalValue 1 (e,d)-jointOptimalValue m (e,d)) _ 0 at h
  rw [h.deriv]
  exact joint_contact_first_gap_coefficient m d hd0 hd1

end
end ExactHoeffding
