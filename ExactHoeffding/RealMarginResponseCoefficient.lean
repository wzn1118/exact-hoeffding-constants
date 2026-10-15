import ExactHoeffding.RealMarginFiniteResponse
import ExactHoeffding.AnalyticCurveSecondDerivative

/-! # Exact linear response of the actual finite-population optimizing tilt -/

namespace ExactHoeffding
noncomputable section
open Filter
open scoped Topology

/-- The first tilt derivative is the actual third cumulant divided by three
on a full real-margin neighborhood. -/
theorem realMarginProxy_deriv_tilt_zero_eventually (N m : ℕ) (hN : 5≤N)
    (hm : 2*m≤N) :
    ∀ᶠ d in 𝓝 (0:ℝ), deriv (realMarginProxy N m d) 0 =
      (m:ℝ)*((N:ℝ)-m)*((N:ℝ)-2*m)*d*(1-d^2)/
        (12*(((N:ℝ)-2)*((N:ℝ)-1))) := by
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have hQ := realMarginProxy_joint_analytic N m hden
  have hins : ContinuousAt (fun d:ℝ => (d,(0:ℝ))) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have hd : ∀ᶠ d in 𝓝 (0:ℝ), |d|<1/(N:ℝ) :=
    continuousAt_id.abs.eventually_lt continuousAt_const (by
      have : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
      simpa only [id_eq, abs_zero] using (show (0:ℝ)<1/(N:ℝ) by positivity))
  filter_upwards [hins.eventually hQ.eventually_analyticAt,hd] with d hQd hd
  have hq : AnalyticAt ℝ (realMarginProxy N m d) 0 :=
    hQd.comp_of_eq (f := fun t:ℝ => (d,t)) (analyticAt_const.prod analyticAt_id) rfl
  have hf : realMarginCenteredLogMGF N m d = fun t => t^2*realMarginProxy N m d t/2 := by
    funext t; exact realMarginProxy_factor N m d t hden
  rw [(analytic_proxy_factor_derivatives _ _ hq hf).1,
    (realMarginCenteredLogMGF_cumulants N m hN hm d hd).1,
    margin_cumulant3_closed N m hN]
  have hNr : (5:ℝ)≤N := by exact_mod_cast hN
  field_simp [show (N:ℝ)-2≠0 by linarith,show (N:ℝ)-1≠0 by linarith]
  ring

/-- The mixed margin--tilt derivative comes from differentiating the actual
third cumulant, rather than postulating a response coefficient. -/
theorem realMarginProxy_mixed_hasDerivAt (N m : ℕ) (hN : 5≤N) (hm : 2*m≤N) :
    HasDerivAt (fun d => deriv (realMarginProxy N m d) 0)
      ((m:ℝ)*((N:ℝ)-m)*((N:ℝ)-2*m)/(12*(((N:ℝ)-2)*((N:ℝ)-1)))) 0 := by
  let b : ℝ := (m:ℝ)*((N:ℝ)-m)*((N:ℝ)-2*m)
  let c : ℝ := 12*(((N:ℝ)-2)*((N:ℝ)-1))
  have hp : HasDerivAt (fun d:ℝ => b*d*(1-d^2)/c) (b/c) 0 := by
    simpa using ((((hasDerivAt_const (0:ℝ) b).mul (hasDerivAt_id 0)).mul
      ((hasDerivAt_const 0 1).sub ((hasDerivAt_id 0).pow 2))).div_const c)
  apply hp.congr_of_eventuallyEq
  exact realMarginProxy_deriv_tilt_zero_eventually N m hN hm

/-- The analytic critical branch has the manuscript's exact finite-N slope. -/
theorem realMarginProxy_critical_branch_hasDerivAt (N m : ℕ) (hN : 5≤N)
    (hm : 0<m) (hNm : 2*m≤N) (τ:ℝ→ℝ) (hτ:AnalyticAt ℝ τ 0)
    (hz:τ 0=0) (heq:∀ᶠ u:ℝ×ℝ in 𝓝 (0,0),
      deriv (realMarginProxy N m u.1) u.2=0 ↔ τ u.1=u.2) :
    HasDerivAt τ (imbalanceT N m) 0 := by
  let Q : ℝ×ℝ→ℝ := fun u => realMarginProxy N m u.1 u.2
  let F := tiltPartial Q
  have hQ : AnalyticAt ℝ Q (0,0) := realMarginProxy_joint_analytic N m
    (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have hF : AnalyticAt ℝ F (0,0) := analyticAt_tiltPartial Q _ hQ
  have hins : HasDerivAt (fun d:ℝ => (d,(0:ℝ))) (1,0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have hfirst := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hins rfl
  have hslice : (fun d:ℝ => F (d,0)) =ᶠ[𝓝 0]
      (fun d => deriv (realMarginProxy N m d) 0) := by
    filter_upwards [hins.continuousAt.eventually hQ.eventually_analyticAt] with d hd
    exact tiltPartial_eq_deriv Q (d,0) hd
  have hx : fderiv ℝ F (0,0) (1,0) =
      (m:ℝ)*((N:ℝ)-m)*((N:ℝ)-2*m)/(12*(((N:ℝ)-2)*((N:ℝ)-1))) :=
    hfirst.deriv.symm.trans (hslice.deriv_eq.trans (realMarginProxy_mixed_hasDerivAt N m hN hNm).deriv)
  have hy : fderiv ℝ F (0,0) (0,1) = marginCumulant4 N m 0/6 := by
    change tiltPartial (tiltPartial Q) (0,0)=_
    rw [tiltPartial2_eq_iteratedDeriv2 Q (0,0) hQ]
    exact (realMarginProxy_tilt_derivatives N m hN hNm).2
  have hpath : HasDerivAt (fun d:ℝ => (d,τ d)) (1,deriv τ 0) 0 :=
    (hasDerivAt_id 0).prodMk hτ.differentiableAt.hasDerivAt
  have hcomp := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath (by simp only [hz])
  have hpathzero : (fun d:ℝ => F (d,τ d)) =ᶠ[𝓝 0] (fun _=>0) := by
    have hc : Tendsto (fun d:ℝ => (d,τ d)) (𝓝 0) (𝓝 (0,0)) := by
      have hc' := hpath.continuousAt
      rw [ContinuousAt,hz] at hc'
      exact hc'
    filter_upwards [hc.eventually heq,hc.eventually hQ.eventually_analyticAt] with d hd ha
    rw [show F (d,τ d)=deriv (realMarginProxy N m d) (τ d) from
      tiltPartial_eq_deriv Q (d,τ d) ha]
    exact hd.mpr rfl
  have hlin : fderiv ℝ F (0,0) (1,deriv τ 0)=0 :=
    hcomp.deriv.symm.trans (hpathzero.deriv_eq.trans (deriv_const _ _))
  rw [show ((1,deriv τ 0):ℝ×ℝ)=(1,0)+deriv τ 0 • ((0,1):ℝ×ℝ) by ext <;> simp,
    map_add,map_smul,hx,hy,smul_eq_mul] at hlin
  have hcurv : marginCumulant4 N m 0/6<0 := by
    rw [← (realMarginProxy_tilt_derivatives N m hN hNm).2]
    exact realMarginProxy_balanced_deriv2_neg N m hN hm hNm
  have hNr : (5:ℝ)≤N := by exact_mod_cast hN
  have hD : imbalanceD N m≠0 := by
    intro hh
    rw [margin_cumulant4_zero N m hN,hh] at hcurv
    norm_num at hcurv
  have hT : (m:ℝ)*((N:ℝ)-m)*((N:ℝ)-2*m)/(12*(((N:ℝ)-2)*((N:ℝ)-1))) +
      imbalanceT N m*(marginCumulant4 N m 0/6)=0 := by
    rw [margin_cumulant4_zero N m hN]
    unfold imbalanceT
    field_simp [hD,show (N:ℝ)-1≠0 by linarith,
      show (N:ℝ)-2≠0 by linarith,show (N:ℝ)-3≠0 by linarith]
    ring
  apply hτ.differentiableAt.hasDerivAt.congr_deriv
  nlinarith

end
end ExactHoeffding
