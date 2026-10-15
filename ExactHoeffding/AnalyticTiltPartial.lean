import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Analytic partial derivatives in the tilt coordinate -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

def tiltPartial (F : ℝ × ℝ → ℝ) (u : ℝ × ℝ) : ℝ :=
  fderiv ℝ F u (0, 1)

theorem analyticAt_tiltPartial (F : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (hF : AnalyticAt ℝ F u) : AnalyticAt ℝ (tiltPartial F) u := by
  exact (ContinuousLinearMap.apply ℝ ℝ (0, 1)).analyticAt _ |>.comp_of_eq hF.fderiv rfl

theorem tiltPartial_eq_deriv (F : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (hF : AnalyticAt ℝ F u) :
    tiltPartial F u = deriv (fun t => F (u.1, t)) u.2 := by
  have hins : HasDerivAt (fun t : ℝ => (u.1, t)) (0, 1) u.2 :=
    (hasDerivAt_const u.2 u.1).prodMk (hasDerivAt_id u.2)
  have hcomp := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq u.2 hins
    (show u = (u.1, u.2) by rfl)
  exact hcomp.deriv.symm

theorem tiltPartial2_eq_iteratedDeriv2 (F : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (hF : AnalyticAt ℝ F u) :
    tiltPartial (tiltPartial F) u = iteratedDeriv 2 (fun t => F (u.1, t)) u.2 := by
  have hins : ContinuousAt (fun t : ℝ => (u.1, t)) u.2 :=
    continuousAt_const.prodMk continuousAt_id
  have heq : (fun t => tiltPartial F (u.1, t)) =ᶠ[𝓝 u.2]
      deriv (fun t => F (u.1, t)) := by
    filter_upwards [hins.eventually hF.eventually_analyticAt] with t ht
    exact tiltPartial_eq_deriv F (u.1, t) ht
  rw [tiltPartial_eq_deriv (tiltPartial F) u (analyticAt_tiltPartial F u hF),
    heq.deriv_eq, show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]

end

end ExactHoeffding
