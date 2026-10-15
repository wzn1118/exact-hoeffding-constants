import ExactHoeffding.ActualNormalizedThirdCoefficient

/-! # Fourth-order analytic Taylor expansion with an analytic fifth-order remainder -/

namespace ExactHoeffding

noncomputable section

open Filter Asymptotics
open scoped Topology

theorem analytic_quartic_remainder (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      (∀ e : ℝ, f e = f 0 + deriv f 0 * e + iteratedDeriv 2 f 0 / 2 * e ^ 2 +
        iteratedDeriv 3 f 0 / 6 * e ^ 3 + iteratedDeriv 4 f 0 / 24 * e ^ 4 +
          e ^ 5 * R e) ∧
      (fun e => f e - f 0 - deriv f 0 * e - iteratedDeriv 2 f 0 / 2 * e ^ 2 -
        iteratedDeriv 3 f 0 / 6 * e ^ 3 - iteratedDeriv 4 f 0 / 24 * e ^ 4)
          =O[𝓝 0] (fun e => e ^ 5) := by
  obtain ⟨T, hT, hTeq, _⟩ := analytic_cubic_remainder f hf
  have hfun : f = (fun e => f 0 + deriv f 0 * e + iteratedDeriv 2 f 0 / 2 * e ^ 2 +
      iteratedDeriv 3 f 0 / 6 * e ^ 3 + e ^ 4 * T e) := funext hTeq
  have hfactor : iteratedDeriv 4 (fun e => e ^ 4 * T e) 0 = 24 * T 0 := by
    rw [iteratedDeriv_fun_mul (by fun_prop) hT.contDiffAt]
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, Nat.choose]
  have h4 := congrArg (fun g : ℝ → ℝ => iteratedDeriv 4 g 0) hfun
  rw [iteratedDeriv_fun_add
    (f := fun e : ℝ => f 0 + deriv f 0 * e + iteratedDeriv 2 f 0 / 2 * e ^ 2 +
      iteratedDeriv 3 f 0 / 6 * e ^ 3)
    (g := fun e : ℝ => e ^ 4 * T e) (by fun_prop)
    (by exact (by fun_prop : AnalyticAt ℝ (fun e : ℝ => e ^ 4 * T e) 0).contDiffAt),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_const, iteratedDeriv_const_mul_field, iteratedDeriv_fun_id,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, hfactor] at h4
  norm_num at h4
  have hT0 : T 0 = iteratedDeriv 4 f 0 / 24 := by linarith
  let R := dslope T 0
  have hR : AnalyticAt ℝ R 0 := analyticAt_dslope_zero hT
  have hReq (e : ℝ) : f e = f 0 + deriv f 0 * e + iteratedDeriv 2 f 0 / 2 * e ^ 2 +
      iteratedDeriv 3 f 0 / 6 * e ^ 3 + iteratedDeriv 4 f 0 / 24 * e ^ 4 +
        e ^ 5 * R e := by
    have hs := sub_smul_dslope T 0 e
    simp only [sub_zero, smul_eq_mul, hT0] at hs
    rw [hTeq e]
    dsimp [R]
    nlinarith [congrArg (fun x : ℝ => e ^ 4 * x) hs]
  refine ⟨R, hR, hReq, ?_⟩
  have hb := (isBigO_refl (fun e : ℝ => e ^ 5) (𝓝 0)).mul
    (hR.continuousAt.isBigO_one ℝ)
  have heq : (fun e => f e - f 0 - deriv f 0 * e - iteratedDeriv 2 f 0 / 2 * e ^ 2 -
      iteratedDeriv 3 f 0 / 6 * e ^ 3 - iteratedDeriv 4 f 0 / 24 * e ^ 4) =
        (fun e => e ^ 5 * R e) := by
    funext e
    rw [hReq e]
    ring
  rw [heq]
  simpa only [mul_one] using hb

end

end ExactHoeffding
