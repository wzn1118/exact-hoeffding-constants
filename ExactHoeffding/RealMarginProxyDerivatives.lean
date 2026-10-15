import ExactHoeffding.RealMarginActualProxy

namespace ExactHoeffding
noncomputable section
open Filter Finset
open scoped Topology

set_option maxHeartbeats 400000

/-- The cubic derivative of a genuine quadratic factor is six times its slope. -/
theorem analytic_quadratic_factor_deriv3 (q : ℝ → ℝ) (hq : AnalyticAt ℝ q 0) :
    iteratedDeriv 3 (fun t => t^2*q t) 0 = 6*deriv q 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hq.contDiffAt]
  norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, Nat.choose]

/-- The quartic derivative of a quadratic factor is twelve times its Hessian. -/
theorem analytic_quadratic_factor_deriv4 (q : ℝ → ℝ) (hq : AnalyticAt ℝ q 0) :
    iteratedDeriv 4 (fun t => t^2*q t) 0 = 12*iteratedDeriv 2 q 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hq.contDiffAt]
  norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, Nat.choose]

/-- Centering changes only the first logarithmic derivative. -/
theorem finiteCenteredLogMGF_iteratedDeriv {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι→ℝ) (μ:ℝ)
    (hw : ∀i∈s, 0≤w i) (hs : ∑i∈s, w i=1) (n:ℕ) (hn:2≤n) :
    iteratedDeriv n (fun t => Real.log (finiteMGF s w x t)-μ*t) 0 =
      iteratedDeriv n (fun t => Real.log (finiteMGF s w x t)) 0 := by
  have hlin : iteratedDeriv n (fun t:ℝ => μ*t) 0=0 := by
    change iteratedDeriv n (fun t:ℝ => μ*(fun x:ℝ => x) t) 0=0
    rw [iteratedDeriv_const_mul_field]
    simp only [iteratedDeriv_fun_id_zero,show n≠1 by omega,if_false,mul_zero]
  rw [iteratedDeriv_fun_sub (finiteLogMGF_contDiff s w x hw hs n).contDiffAt (by fun_prop),hlin,sub_zero]

/-- The factor identity identifies the slope and Hessian of a removable proxy. -/
theorem analytic_proxy_factor_derivatives (L q : ℝ→ℝ) (hq : AnalyticAt ℝ q 0)
    (hfactor : L = fun t => t^2*q t/2) :
    deriv q 0 = iteratedDeriv 3 L 0 /3 ∧
      iteratedDeriv 2 q 0 = iteratedDeriv 4 L 0/6 := by
  have h3 := congrArg (fun f : ℝ→ℝ => iteratedDeriv 3 f 0) hfactor
  have h4 := congrArg (fun f : ℝ→ℝ => iteratedDeriv 4 f 0) hfactor
  rw [iteratedDeriv_div_const, analytic_quadratic_factor_deriv3 q hq] at h3
  rw [iteratedDeriv_div_const, analytic_quadratic_factor_deriv4 q hq] at h4
  constructor <;> linarith

/-- Centered logarithmic derivatives agree with the actual cumulants. -/
theorem realMarginCenteredLogMGF_cumulants (N m : ℕ) (hN : 5≤N) (hm : 2*m≤N)
    (d:ℝ) (hd:|d|<1/(N:ℝ)) :
    iteratedDeriv 3 (realMarginCenteredLogMGF N m d) 0=marginCumulant3 N m d ∧
    iteratedDeriv 4 (realMarginCenteredLogMGF N m d) 0=marginCumulant4 N m d := by
  obtain ⟨hw,hs⟩ := realMarginMass_near_balanced_probability N m (by omega) hm d hd
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  constructor
  · unfold realMarginCenteredLogMGF
    rw [finiteCenteredLogMGF_iteratedDeriv _ _ _ _ hw hs 3 (by omega),
      finiteLogMGF_deriv3_zero_cumulant _ _ _ hw hs, realMarginMass_cumulant3 N m d hden]
  · unfold realMarginCenteredLogMGF
    rw [finiteCenteredLogMGF_iteratedDeriv _ _ _ _ hw hs 4 (by omega),
      finiteLogMGF_deriv4_zero_cumulant _ _ _ hw hs, realMarginMass_cumulant4 N m d hden]

/-- The actual removable objective has the true fourth cumulant as Hessian. -/
theorem realMarginProxy_tilt_derivatives (N m : ℕ) (hN : 5≤N) (hm : 2*m≤N) :
    deriv (realMarginProxy N m 0) 0=0 ∧
    iteratedDeriv 2 (realMarginProxy N m 0) 0=marginCumulant4 N m 0/6 := by
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have hq : AnalyticAt ℝ (realMarginProxy N m 0) 0 :=
    (realMarginProxy_joint_analytic N m hden).comp_of_eq
      (f := fun t:ℝ => ((0:ℝ),t)) (analyticAt_const.prod analyticAt_id) rfl
  have hf : realMarginCenteredLogMGF N m 0 = fun t => t^2*realMarginProxy N m 0 t/2 := by
    funext t; exact realMarginProxy_factor N m 0 t hden
  have h := analytic_proxy_factor_derivatives _ _ hq hf
  have hd : |(0:ℝ)|<1/(N:ℝ) := by
    simp only [abs_zero]
    have : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    positivity
  have hc := realMarginCenteredLogMGF_cumulants N m hN hm 0 hd
  rw [hc.1,hc.2] at h
  have hk : marginCumulant3 N m 0=0 := by
    rw [margin_cumulant3_closed N m hN]; ring
  simpa only [hk,zero_div] using h

end
end ExactHoeffding
