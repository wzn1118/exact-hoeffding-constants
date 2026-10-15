import ExactHoeffding.RealMarginResponseCoefficient

/-! # The exact quadratic imbalance coefficient of the actual optimized value -/
namespace ExactHoeffding
noncomputable section
open Filter
open scoped Topology

/-- The margin slice at zero tilt is the true variance polynomial. -/
theorem realMarginProxy_zero_tilt_deriv2 (N m:ℕ) (hN:5≤N) (hNm:2*m≤N) :
    iteratedDeriv 2 (fun d=>realMarginProxy N m d 0) 0 =
      -(m:ℝ)*((N:ℝ)-m)/(2*((N:ℝ)-1)) := by
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have heq : (fun d=>realMarginProxy N m d 0) =
      fun d=> (m:ℝ)*((N:ℝ)-m)/(4*((N:ℝ)-1))*(1-d^2) := by
    funext d
    rw [realMarginProxy_zero N m d hden,margin_cumulant2_closed N m hN]
    ring
  rw [heq,iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_sub (by fun_prop) (by fun_prop)]
  rw [iteratedDeriv_const]
  norm_num [iteratedDeriv_fun_pow_zero]
  have hNr : (5:ℝ)≤N := by exact_mod_cast hN
  field_simp [show (N:ℝ)-1≠0 by linarith]
  ring

/-- The Hessian on the actual analytic critical curve contains its actual
margin, mixed and tilt derivatives. -/
theorem realMarginProxy_optimized_value_deriv2 (N m:ℕ) (hN:5≤N)
    (hm:0<m) (hNm:2*m≤N) (τ:ℝ→ℝ) (hτ:AnalyticAt ℝ τ 0) (hz:τ 0=0)
    (hdτ:deriv τ 0=imbalanceT N m) :
    iteratedDeriv 2 (fun d=>realMarginProxy N m d (τ d)) 0 =
      -(m:ℝ)*((N:ℝ)-m)/(2*((N:ℝ)-1)) +
      2*imbalanceT N m*((m:ℝ)*((N:ℝ)-m)*((N:ℝ)-2*m)/
        (12*(((N:ℝ)-2)*((N:ℝ)-1)))) +
      (imbalanceT N m)^2*(marginCumulant4 N m 0/6) := by
  let Q : ℝ×ℝ→ℝ := fun u=>realMarginProxy N m u.1 u.2
  let D := fderiv ℝ (fderiv ℝ Q) (0,0)
  have hQ : AnalyticAt ℝ Q (0,0) := realMarginProxy_joint_analytic N m
    (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have hy : fderiv ℝ Q (0,0) (0,1)=0 := by
    change tiltPartial Q (0,0)=_
    rw [tiltPartial_eq_deriv Q (0,0) hQ]
    exact (realMarginProxy_tilt_derivatives N m hN hNm).1
  have hxx : D (1,0) (1,0)= -(m:ℝ)*((N:ℝ)-m)/(2*((N:ℝ)-1)) := by
    have h := analytic_curve_iteratedDeriv2 Q (fun _=>0) hQ analyticAt_const rfl hy
    simp only [deriv_const] at h
    exact h.symm.trans (realMarginProxy_zero_tilt_deriv2 N m hN hNm)
  have hyx : D (1,0) (0,1)=
      (m:ℝ)*((N:ℝ)-m)*((N:ℝ)-2*m)/(12*(((N:ℝ)-2)*((N:ℝ)-1))) := by
    have hins : HasDerivAt (fun d:ℝ=>(d,(0:ℝ))) (1,0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
    have hfirst := (analyticAt_tiltPartial Q _ hQ).differentiableAt.hasFDerivAt
      |>.comp_hasDerivAt_of_eq 0 hins rfl
    have hslice : (fun d=>tiltPartial Q (d,0)) =ᶠ[𝓝 0]
        (fun d=>deriv (realMarginProxy N m d) 0) := by
      filter_upwards [hins.continuousAt.eventually hQ.eventually_analyticAt] with d hd
      exact tiltPartial_eq_deriv Q (d,0) hd
    rw [← analytic_directional_fderiv Q (0,0) (1,0) (0,1) hQ]
    exact hfirst.deriv.symm.trans (hslice.deriv_eq.trans (realMarginProxy_mixed_hasDerivAt N m hN hNm).deriv)
  have hxy : D (0,1) (1,0)=
      (m:ℝ)*((N:ℝ)-m)*((N:ℝ)-2*m)/(12*(((N:ℝ)-2)*((N:ℝ)-1))) := by
    have hsymm := (hQ.contDiffAt : ContDiffAt ℝ ⊤ Q (0,0)).isSymmSndFDerivAt (by simp)
    exact (hsymm (0,1) (1,0)).trans hyx
  have hyy : D (0,1) (0,1)=marginCumulant4 N m 0/6 := by
    rw [← analytic_directional_fderiv Q (0,0) (0,1) (0,1) hQ]
    change tiltPartial (tiltPartial Q) (0,0)=_
    rw [tiltPartial2_eq_iteratedDeriv2 Q (0,0) hQ]
    exact (realMarginProxy_tilt_derivatives N m hN hNm).2
  rw [analytic_curve_iteratedDeriv2 Q τ hQ hτ hz hy,hdτ]
  change D (1,imbalanceT N m) (1,imbalanceT N m)=_
  rw [show ((1,imbalanceT N m):ℝ×ℝ)=(1,0)+imbalanceT N m • ((0,1):ℝ×ℝ) by ext <;> simp]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [hxx,hyx,hxy,hyy]
  ring

/-- Normalizing the actual critical value gives exactly the manuscript's
coefficient `A`, including one-draw laws. -/
theorem realMarginProxy_normalized_value_deriv2 (N m:ℕ) (hN:5≤N)
    (hm:0<m) (hNm:2*m≤N) (τ:ℝ→ℝ) (hτ:AnalyticAt ℝ τ 0) (hz:τ 0=0)
    (hdτ:deriv τ 0=imbalanceT N m) :
    iteratedDeriv 2 (fun d=>4*(N:ℝ)*realMarginProxy N m d (τ d)/
      ((m:ℝ)*((N:ℝ)-m))) 0 = -2*imbalanceA N m := by
  rw [show (fun d=>4*(N:ℝ)*realMarginProxy N m d (τ d)/((m:ℝ)*((N:ℝ)-m)))=
      fun d=>(4*(N:ℝ)/((m:ℝ)*((N:ℝ)-m)))*realMarginProxy N m d (τ d) by funext d; ring,
    iteratedDeriv_const_mul_field,realMarginProxy_optimized_value_deriv2 N m hN hm hNm τ hτ hz hdτ,
    margin_cumulant4_zero N m hN]
  have hNr : (5:ℝ)≤N := by exact_mod_cast hN
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hNmR : 2*(m:ℝ)≤N := by exact_mod_cast hNm
  have hD : imbalanceD N m≠0 := by
    unfold imbalanceD
    have hprod : (m:ℝ)*((N:ℝ)-m) ≤ (N:ℝ)^2/4 := by
      nlinarith [sq_nonneg ((N:ℝ)-2*m)]
    nlinarith
  unfold imbalanceT imbalanceA
  field_simp [hD,show (m:ℝ)≠0 by linarith,show (N:ℝ)-m≠0 by linarith,
    show (N:ℝ)-1≠0 by linarith,show (N:ℝ)-2≠0 by linarith,
    show (N:ℝ)-3≠0 by linarith]
  unfold imbalanceD
  ring

end
end ExactHoeffding
