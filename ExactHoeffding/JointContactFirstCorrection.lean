import ExactHoeffding.JointBinomialOptimizer
import ExactHoeffding.JointMGFFirstCorrection

/-! # Actual first population correction at the free binomial contact -/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

/-- The binomial contact exponential is the squared odds. -/
theorem jointBinomialTilt_exp (d : ℝ) (hd : d ∈ Ioo (-1:ℝ) 1) :
    Real.exp (jointBinomialTilt d) =
      ((1-jointSuccessFraction d)/jointSuccessFraction d)^2 := by
  have hp : 0 < jointSuccessFraction d := by unfold jointSuccessFraction; linarith [hd.2]
  have hq : 0 < 1-jointSuccessFraction d := by unfold jointSuccessFraction; linarith [hd.1]
  rw [jointBinomialTilt_eq_log d hd,two_mul,Real.exp_add,
    Real.exp_log (div_pos hq hp)]
  ring

/-- The logarithmic population correction simplifies exactly at the contact. -/
theorem jointBinomial_contact_population_factor (d : ℝ)
    (hd : d ∈ Ioo (-1:ℝ) 1) :
    1-(jointSuccessFraction d*Real.exp (2*jointBinomialTilt d)+(1-jointSuccessFraction d))/
        (1-jointSuccessFraction d+jointSuccessFraction d*Real.exp (jointBinomialTilt d))^2 =
      -d^2/(jointSuccessFraction d*(1-jointSuccessFraction d)) := by
  let p := jointSuccessFraction d
  have hp : 0 < p := by dsimp [p,jointSuccessFraction]; linarith [hd.2]
  have hq : 0 < 1-p := by dsimp [p,jointSuccessFraction]; linarith [hd.1]
  have he := jointBinomialTilt_exp d hd
  have he2 : Real.exp (2*jointBinomialTilt d) = ((1-p)/p)^4 := by
    rw [two_mul,Real.exp_add,he]
    dsimp [p]
    ring
  rw [he2,he]
  change 1-(p*((1-p)/p)^4+(1-p))/(1-p+p*((1-p)/p)^2)^2 =
    -d^2/(p*(1-p))
  have hZ : 1-p+p*((1-p)/p)^2 = (1-p)/p := by field_simp [hp.ne']; ring
  rw [hZ]
  have hrel : 1-2*p=d := by dsimp [p,jointSuccessFraction]; ring
  rw [← hrel]
  field_simp [hp.ne',hq.ne']
  ring

/-- Identification with the real-margin finite law holds on a full population
neighborhood of the binomial axis. -/
theorem jointMGF_realMargin_eventually_population (m : ℕ) (d t : ℝ) :
    (fun e => jointMGF m e d t) =ᶠ[𝓝 (0:ℝ)]
      (fun e => finiteMGF (Finset.range (m+1))
        (realMarginMass m e (jointSuccessFraction d)) (fun i => (i:ℝ)) t) := by
  have hden : ∀ᶠ e in 𝓝 (0:ℝ), scaledFalling 1 e m ≠ 0 :=
    ((rescaledPopulationDenom_joint_analytic m (0,0)).comp_of_eq
      (f := fun e : ℝ => (e,(0:ℝ)))
      (analyticAt_id.prod analyticAt_const) rfl).continuousAt.eventually_ne (by simp)
  filter_upwards [hden] with e he
  exact jointMGF_realMargin m e d t he

/-- This is the actual log-MGF population partial at the binomial optimizer. -/
theorem jointCenteredLogMGF_contact_hasDerivAt_population_zero (m : ℕ)
    (hm : 2 ≤ m) (d : ℝ) (hd : d ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun e => Real.log (jointMGF m e d (jointBinomialTilt d)) -
      jointMean m e d*jointBinomialTilt d)
      (-((m:ℝ)*((m:ℝ)-1)/2)*d^2/
        (jointSuccessFraction d*(1-jointSuccessFraction d))) 0 := by
  have hp : 0 < jointSuccessFraction d := by unfold jointSuccessFraction; linarith [hd.2]
  have hp1 : jointSuccessFraction d < 1 := by unfold jointSuccessFraction; linarith [hd.1]
  have h := realMarginCenteredLogMGF_hasDerivAt_population_zero m hm
    (jointSuccessFraction d) (jointBinomialTilt d) hp hp1
  have heq : (fun e => Real.log (jointMGF m e d (jointBinomialTilt d)) -
      jointMean m e d*jointBinomialTilt d) =ᶠ[𝓝 (0:ℝ)]
      (fun e => Real.log (finiteMGF (Finset.range (m+1))
        (realMarginMass m e (jointSuccessFraction d)) (fun i => (i:ℝ))
          (jointBinomialTilt d)) - (m:ℝ)*jointSuccessFraction d*jointBinomialTilt d) := by
    filter_upwards [jointMGF_realMargin_eventually_population m d (jointBinomialTilt d)]
      with e he
    rw [he]
    rfl
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  rw [jointBinomial_contact_population_factor d hd]
  ring

/-- The actual unnormalized proxy population partial at its nonzero limiting
optimizer. No derivative of a moving optimizer is assumed. -/
theorem jointProxyExtension_contact_hasDerivAt_population_zero (m : ℕ)
    (hm : 2 ≤ m) (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    HasDerivAt (fun e => jointProxyExtension m e d (jointBinomialTilt d))
      (-((m:ℝ)*((m:ℝ)-1))*d^2/
        ((jointBinomialTilt d)^2*jointSuccessFraction d*(1-jointSuccessFraction d))) 0 := by
  have hd : d ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hd1⟩
  have ht := jointBinomialTilt_ne_zero d hd hd0.ne'
  have h := ((jointCenteredLogMGF_contact_hasDerivAt_population_zero m hm d hd).const_mul 2).div_const ((jointBinomialTilt d)^2)
  have heq : (fun e => jointProxyExtension m e d (jointBinomialTilt d)) =
      (fun e => 2*(Real.log (jointMGF m e d (jointBinomialTilt d)) -
        jointMean m e d*jointBinomialTilt d)/(jointBinomialTilt d)^2) := by
    funext e
    exact jointProxyExtension_eq_quotient m (by omega) e d _ ht
  rw [heq]
  apply h.congr_deriv
  have hp : jointSuccessFraction d ≠ 0 := by
    unfold jointSuccessFraction
    intro hz
    linarith
  have hq : 1-jointSuccessFraction d ≠ 0 := by
    unfold jointSuccessFraction
    intro hz
    linarith
  field_simp [ht,hp,hq]

/-- The exact normalized contact value on the binomial axis is g(d). -/
theorem jointProxyExtension_normalized_contact_zero (m : ℕ) (hm : 0 < m)
    (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    4*jointProxyExtension m 0 d (jointBinomialTilt d)/(m:ℝ) = d/Real.artanh d := by
  have hd : d ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hd1⟩
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hpne : jointSuccessFraction d ≠ 1/2 := by
    unfold jointSuccessFraction
    intro h
    linarith
  rw [jointProxyExtension_binomial_contact m hm d hd,
    bernoulliSharpBeta_eq_formula _ hpne]
  have hlog : Real.log ((1-jointSuccessFraction d)/jointSuccessFraction d) =
      2*Real.artanh d := by
    have h := jointBinomialTilt_eq_log d hd
    unfold jointBinomialTilt at h
    linarith
  rw [hlog]
  unfold jointSuccessFraction
  field_simp [hmR]
  ring

/-- Differentiating the actual normalized objective at the fixed limiting
contact gives the manuscript's closed first inverse-population coefficient. -/
theorem jointProxyExtension_normalized_contact_hasDerivAt_population_zero
    (m : ℕ) (hm : 2 ≤ m) (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    HasDerivAt
      (fun e => 4*jointProxyExtension m e d (jointBinomialTilt d)/
        ((m:ℝ)*(1-(m:ℝ)*e)))
      ((m:ℝ)*(d/Real.artanh d) - ((m:ℝ)-1)*d^2/
        ((2*Real.artanh d)^2*jointSuccessFraction d*(1-jointSuccessFraction d))) 0 := by
  have hQ := jointProxyExtension_contact_hasDerivAt_population_zero m hm d hd0 hd1
  have hden : HasDerivAt (fun e:ℝ => (m:ℝ)*(1-(m:ℝ)*e)) (-(m:ℝ)^2) 0 := by
    have hi : HasDerivAt (fun e:ℝ => 1-(m:ℝ)*e) (-(m:ℝ)) 0 := by
      simpa only [id_eq,mul_one] using
        (((hasDerivAt_id (0:ℝ)).const_mul (m:ℝ)).const_sub 1)
    apply (hi.const_mul (m:ℝ)).congr_deriv
    ring
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (show m≠0 by omega)
  have h := (hQ.const_mul 4).div hden (by simpa using hmR)
  apply h.congr_deriv
  have hval := jointProxyExtension_normalized_contact_zero m (by omega) d hd0 hd1
  have hd : d ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hd1⟩
  have hart : Real.artanh d ≠ 0 := by
    have ht := jointBinomialTilt_ne_zero d hd hd0.ne'
    intro hz
    apply ht
    simp [jointBinomialTilt,hz]
  have hp : jointSuccessFraction d ≠ 0 := by
    unfold jointSuccessFraction
    intro hz
    linarith
  have hq : 1-jointSuccessFraction d ≠ 0 := by
    unfold jointSuccessFraction
    intro hz
    linarith
  have hval' : 4*jointProxyExtension m 0 d (jointBinomialTilt d) =
      (m:ℝ)*(d/Real.artanh d) := by
    simpa only [mul_comm] using (div_eq_iff hmR).mp hval
  simp only [mul_zero,sub_zero,mul_one]
  have hQval : jointProxyExtension m 0 d (jointBinomialTilt d) =
      (m:ℝ)*(d/Real.artanh d)/4 := by linarith only [hval']
  rw [hQval]
  unfold jointBinomialTilt
  field_simp [hmR,hart,hp,hq]
  ring

end
end ExactHoeffding
