import ExactHoeffding.AnalyticTiltPartial
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! # Second derivatives of analytic scalar functions along analytic curves -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem analytic_curve_iteratedDeriv2 (Q : ℝ × ℝ → ℝ) (τ : ℝ → ℝ)
    (hQ : AnalyticAt ℝ Q (0, 0)) (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0)
    (hy : fderiv ℝ Q (0, 0) (0, 1) = 0) :
    iteratedDeriv 2 (fun e => Q (e, τ e)) 0 =
      fderiv ℝ (fderiv ℝ Q) (0, 0) (1, deriv τ 0) (1, deriv τ 0) := by
  let c : ℝ → ℝ × ℝ := fun e => (e, τ e)
  let v : ℝ → ℝ × ℝ := fun e => (1, deriv τ e)
  have hc : HasDerivAt c (1, deriv τ 0) 0 :=
    (hasDerivAt_id 0).prodMk hτ.differentiableAt.hasDerivAt
  have hc0 : c 0 = (0, 0) := by simp [c, hτzero]
  have hderiv : deriv (fun e => Q (c e)) =ᶠ[𝓝 0]
      (fun e => fderiv ℝ Q (c e) (v e)) := by
    have hct : Tendsto c (𝓝 0) (𝓝 (0, 0)) := hc0 ▸ hc.continuousAt
    filter_upwards [hct.eventually hQ.eventually_analyticAt,
      hτ.eventually_analyticAt] with e he heτ
    have hce : HasDerivAt c (v e) e :=
      (hasDerivAt_id e).prodMk heτ.differentiableAt.hasDerivAt
    exact (he.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq e hce rfl).deriv
  have hDQ := hQ.fderiv.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc hc0.symm
  have hv : HasDerivAt v (0, deriv (deriv τ) 0) 0 :=
    (hasDerivAt_const 0 1).prodMk hτ.deriv.differentiableAt.hasDerivAt
  have hsecond := hDQ.clm_apply hv
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hderiv.deriv_eq]
  calc
    deriv (fun e => fderiv ℝ Q (c e) (v e)) 0 =
        fderiv ℝ (fderiv ℝ Q) (0, 0) (1, deriv τ 0) (1, deriv τ 0) +
          fderiv ℝ Q (0, 0) (0, deriv (deriv τ) 0) := by
      simpa only [Function.comp_apply, hc0, v] using hsecond.deriv
    _ = _ := ?_
  have hz : fderiv ℝ Q (0, 0) (0, deriv (deriv τ) 0) = 0 := by
    rw [show ((0, deriv (deriv τ) 0) : ℝ × ℝ) =
      deriv (deriv τ) 0 • ((0, 1) : ℝ × ℝ) by ext <;> simp, map_smul, hy, smul_zero]
  rw [hz, add_zero]

theorem analytic_directional_fderiv (Q : ℝ × ℝ → ℝ) (u v w : ℝ × ℝ)
    (hQ : AnalyticAt ℝ Q u) :
    fderiv ℝ (fun x => fderiv ℝ Q x w) u v =
      fderiv ℝ (fderiv ℝ Q) u v w := by
  let A : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ w
  have hd := A.hasFDerivAt.comp u hQ.fderiv.differentiableAt.hasFDerivAt
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L v) hd.fderiv

end

end ExactHoeffding
