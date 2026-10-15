import ExactHoeffding.AnalyticCoordinateJets
import ExactHoeffding.AnalyticCurveThirdDerivative

/-! # Fourth derivative of an analytic stationary value

The envelope identity eliminates the fourth derivative of the optimizing
curve. All remaining terms are actual coordinate jets of the objective.
-/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem analytic_stationary_value_deriv4 (Q : ℝ × ℝ → ℝ) (τ : ℝ → ℝ)
    (hQ : AnalyticAt ℝ Q (0, 0)) (hτ : AnalyticAt ℝ τ 0) (hz : τ 0 = 0)
    (hcritical : (fun e => tiltPartial Q (e, τ e)) =ᶠ[𝓝 0] (fun _ => 0)) :
    iteratedDeriv 4 (fun e => Q (e, τ e)) 0 =
      populationPartial (populationPartial (populationPartial (populationPartial Q))) (0, 0) +
        3 * deriv τ 0 * populationPartial (populationPartial (populationPartial (tiltPartial Q))) (0, 0) +
        3 * deriv τ 0 ^ 2 * populationPartial (populationPartial (tiltPartial (tiltPartial Q))) (0, 0) +
        deriv τ 0 ^ 3 * populationPartial (tiltPartial (tiltPartial (tiltPartial Q))) (0, 0) +
        3 * iteratedDeriv 2 τ 0 * populationPartial (populationPartial (tiltPartial Q)) (0, 0) +
        3 * deriv τ 0 * iteratedDeriv 2 τ 0 * populationPartial (tiltPartial (tiltPartial Q)) (0, 0) +
        iteratedDeriv 3 τ 0 * populationPartial (tiltPartial Q) (0, 0) := by
  have henv : deriv (fun e => Q (e, τ e)) =ᶠ[𝓝 0]
      (fun e => populationPartial Q (e, τ e)) := by
    apply (analytic_curve_deriv_split Q τ hQ hτ hz).trans
    filter_upwards [hcritical] with e he
    rw [he, zero_mul, add_zero]
  have h1 := iterate_tiltPartial_population_commute 1 Q (0, 0) hQ
  have h2 := iterate_tiltPartial_population_commute 2 Q (0, 0) hQ
  have h3 := iterate_tiltPartial_population_commute 3 Q (0, 0) hQ
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at h1 h2 h3
  have hPP := populationPartial_congr_germ _ _ (0, 0)
    (populationPartial_congr_germ _ _ (0, 0) h1)
  have hPT := populationPartial_congr_germ _ _ (0, 0) h2
  have hP := populationPartial_congr_germ _ _ (0, 0) h1
  rw [show (4 : ℕ) = 3 + 1 by rfl, iteratedDeriv_succ', henv.iteratedDeriv_eq,
    analytic_curve_deriv3_partials (populationPartial Q) τ
      (analyticAt_populationPartial Q _ hQ) hτ hz,
    hPP.eq_of_nhds, hPT.eq_of_nhds, h3.eq_of_nhds,
    hP.eq_of_nhds, h2.eq_of_nhds, h1.eq_of_nhds]

end

end ExactHoeffding
