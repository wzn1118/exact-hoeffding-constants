import ExactHoeffding.RescaledCompactConvergence
import ExactHoeffding.MGFDerivatives
import ExactHoeffding.Sampling
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Actual negative limiting curvature of the removable proxy -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

private theorem iteratedDeriv4_quadratic_factor (g : ℝ → ℝ)
    (hg : AnalyticAt ℝ g 0) :
    iteratedDeriv 4 (fun t => t ^ 2 * g t / 2) 0 =
      6 * iteratedDeriv 2 g 0 := by
  rw [iteratedDeriv_div_const]
  rw [iteratedDeriv_fun_mul (by fun_prop) hg.contDiffAt]
  norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, Nat.choose]
  ring

private theorem rescaled_limit_log_deriv4 (m : ℕ) (s : ℝ) :
    iteratedDeriv 4 (fun t => Real.log (rescaledMGF m s 0 t)) 0 = -(m : ℝ) / 8 := by
  have hfun : (fun t => Real.log (rescaledMGF m s 0 t)) =
      (fun t => (m : ℝ) * Real.log (hypergeomMGF 2 1 1 t)) := by
    funext t
    rw [rescaledMGF_at_zero, Real.log_pow, hypergeomMGF_singleton 2 1 (by omega)
      (by omega)]
    congr 2
    unfold bernoulliMGF
    norm_num
    ring
  rw [hfun, iteratedDeriv_const_mul_field,
    hypergeom_logMGF_deriv4_zero 2 1 1 (by omega) (by omega)]
  norm_num [hypergeomCumulant4, finiteCumulant4, finiteRawMoment,
    Finset.sum_range_succ, hypergeomMass, hypergeomCount]
  ring

/-- The limiting proxy has the nonzero Hessian required for local uniqueness. -/
theorem rescaledProxyExtension_limit_deriv2 (m : ℕ) (s : ℝ) :
    iteratedDeriv 2 (rescaledProxyExtension m s 0) 0 = -(m : ℝ) / 48 := by
  by_cases hm0 : m = 0
  · subst m
    have hz : rescaledProxyExtension 0 s 0 = (fun _ : ℝ => (0 : ℝ)) := by
      funext t
      simp [rescaledProxyExtension, rescaledMGFQuadratic, rescaledMGFSlope, rescaledMean]
    rw [hz, iteratedDeriv_const]
    norm_num
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hQ : AnalyticAt ℝ (rescaledProxyExtension m s 0) 0 :=
    (rescaledProxyExtension_joint_analytic m s).comp_of_eq
      (f := fun t : ℝ => ((0 : ℝ), t))
      (analyticAt_const.prod analyticAt_id) rfl
  have hM : AnalyticAt ℝ (fun t => Real.log (rescaledMGF m s 0 t)) 0 := by
    have ha : AnalyticAt ℝ (rescaledMGF m s 0) 0 :=
      (rescaledMGF_joint_analytic m s 0).comp_of_eq
        (f := fun t : ℝ => ((0 : ℝ), t))
        (analyticAt_const.prod analyticAt_id) rfl
    exact ha.log (by simp)
  have heq :
      (fun t => Real.log (rescaledMGF m s 0 t) - rescaledMean m s 0 * t) =
        (fun t => t ^ 2 * rescaledProxyExtension m s 0 t / 2) := by
    funext t
    exact rescaled_logMGF_quadratic_factor m hm s 0 t
  have hderiv := congrArg (fun f : ℝ → ℝ => iteratedDeriv 4 f 0) heq
  rw [iteratedDeriv_fun_sub hM.contDiffAt (by fun_prop),
    rescaled_limit_log_deriv4,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_id,
    iteratedDeriv4_quadratic_factor _ hQ] at hderiv
  norm_num at hderiv
  linarith

theorem rescaledProxyExtension_limit_deriv2_neg (m : ℕ) (hm : 0 < m) (s : ℝ) :
    iteratedDeriv 2 (rescaledProxyExtension m s 0) 0 < 0 := by
  rw [rescaledProxyExtension_limit_deriv2]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  linarith

end

end ExactHoeffding
