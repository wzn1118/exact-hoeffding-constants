import ExactHoeffding.RescaledOptimumThird

/-! # Third derivatives along analytic population--tilt curves

The chain rule is expressed in the two coordinate partial derivatives,
so actual mixed derivatives can be substituted directly.
-/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem analytic_curve_deriv_split (Q : ℝ × ℝ → ℝ) (τ : ℝ → ℝ)
    (hQ : AnalyticAt ℝ Q (0, 0)) (hτ : AnalyticAt ℝ τ 0) (hz : τ 0 = 0) :
    deriv (fun e => Q (e, τ e)) =ᶠ[𝓝 0]
      (fun e => populationPartial Q (e, τ e) + tiltPartial Q (e, τ e) * deriv τ e) := by
  have hc : ContinuousAt (fun e : ℝ => (e, τ e)) 0 :=
    continuousAt_id.prodMk hτ.continuousAt
  have ht : Tendsto (fun e : ℝ => (e, τ e)) (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [ContinuousAt, hz] using hc
  filter_upwards [ht.eventually hQ.eventually_analyticAt, hτ.eventually_analyticAt]
    with e he heτ
  have hce : HasDerivAt (fun e : ℝ => (e, τ e)) (1, deriv τ e) e :=
    (hasDerivAt_id e).prodMk heτ.differentiableAt.hasDerivAt
  have hd := he.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq e hce rfl
  change HasDerivAt (fun e => Q (e, τ e)) _ e at hd
  rw [hd.deriv]
  rw [show ((1, deriv τ e) : ℝ × ℝ) =
    (1, 0) + deriv τ e • ((0, 1) : ℝ × ℝ) by ext <;> simp]
  simp only [map_add, map_smul, smul_eq_mul, populationPartial, tiltPartial]
  ring

theorem analytic_curve_deriv_split_zero (Q : ℝ × ℝ → ℝ) (τ : ℝ → ℝ)
    (hQ : AnalyticAt ℝ Q (0, 0)) (hτ : AnalyticAt ℝ τ 0) (hz : τ 0 = 0) :
    deriv (fun e => Q (e, τ e)) 0 =
      populationPartial Q (0, 0) + tiltPartial Q (0, 0) * deriv τ 0 := by
  simpa only [hz] using (analytic_curve_deriv_split Q τ hQ hτ hz).eq_of_nhds

theorem analytic_curve_deriv2_partials (Q : ℝ × ℝ → ℝ) (τ : ℝ → ℝ)
    (hQ : AnalyticAt ℝ Q (0, 0)) (hτ : AnalyticAt ℝ τ 0) (hz : τ 0 = 0) :
    iteratedDeriv 2 (fun e => Q (e, τ e)) 0 =
      populationPartial (populationPartial Q) (0, 0) +
        2 * deriv τ 0 * populationPartial (tiltPartial Q) (0, 0) +
        deriv τ 0 ^ 2 * tiltPartial (tiltPartial Q) (0, 0) +
        iteratedDeriv 2 τ 0 * tiltPartial Q (0, 0) := by
  let c : ℝ → ℝ × ℝ := fun e => (e, τ e)
  have hc : AnalyticAt ℝ c 0 := analyticAt_id.prod hτ
  have hc0 : c 0 = (0, 0) := by simp [c, hz]
  have hP := analyticAt_populationPartial Q (0, 0) hQ
  have hT := analyticAt_tiltPartial Q (0, 0) hQ
  have hPc : AnalyticAt ℝ (fun e => populationPartial Q (c e)) 0 :=
    hP.comp_of_eq hc hc0
  have hTc : AnalyticAt ℝ (fun e => tiltPartial Q (c e)) 0 :=
    hT.comp_of_eq hc hc0
  have hd := hTc.differentiableAt.hasDerivAt.mul hτ.deriv.differentiableAt.hasDerivAt
  change HasDerivAt (fun e => tiltPartial Q (c e) * deriv τ e) _ 0 at hd
  have hs := hPc.differentiableAt.hasDerivAt.add hd
  change HasDerivAt (fun e => populationPartial Q (e, τ e) +
    tiltPartial Q (e, τ e) * deriv τ e) _ 0 at hs
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ', iteratedDeriv_one,
    (analytic_curve_deriv_split Q τ hQ hτ hz).deriv_eq, hs.deriv]
  dsimp only [c]
  rw [analytic_curve_deriv_split_zero (populationPartial Q) τ hP hτ hz,
    analytic_curve_deriv_split_zero (tiltPartial Q) τ hT hτ hz,
    analytic_partials_commute Q (0, 0) hQ]
  simp only [hz, show deriv (deriv τ) 0 = iteratedDeriv 2 τ 0 by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
  ring

theorem analytic_curve_deriv3_partials (Q : ℝ × ℝ → ℝ) (τ : ℝ → ℝ)
    (hQ : AnalyticAt ℝ Q (0, 0)) (hτ : AnalyticAt ℝ τ 0) (hz : τ 0 = 0) :
    iteratedDeriv 3 (fun e => Q (e, τ e)) 0 =
      populationPartial (populationPartial (populationPartial Q)) (0, 0) +
        3 * deriv τ 0 * populationPartial (populationPartial (tiltPartial Q)) (0, 0) +
        3 * deriv τ 0 ^ 2 * populationPartial (tiltPartial (tiltPartial Q)) (0, 0) +
        deriv τ 0 ^ 3 * tiltPartial (tiltPartial (tiltPartial Q)) (0, 0) +
        3 * iteratedDeriv 2 τ 0 * populationPartial (tiltPartial Q) (0, 0) +
        3 * deriv τ 0 * iteratedDeriv 2 τ 0 * tiltPartial (tiltPartial Q) (0, 0) +
        iteratedDeriv 3 τ 0 * tiltPartial Q (0, 0) := by
  let c : ℝ → ℝ × ℝ := fun e => (e, τ e)
  have hc : AnalyticAt ℝ c 0 := analyticAt_id.prod hτ
  have hc0 : c 0 = (0, 0) := by simp [c, hz]
  have hP := analyticAt_populationPartial Q (0, 0) hQ
  have hT := analyticAt_tiltPartial Q (0, 0) hQ
  have hPc : AnalyticAt ℝ (fun e => populationPartial Q (c e)) 0 := hP.comp_of_eq hc hc0
  have hTc : AnalyticAt ℝ (fun e => tiltPartial Q (c e)) 0 := hT.comp_of_eq hc hc0
  have hcomm : tiltPartial (populationPartial Q) =ᶠ[𝓝 (0, 0)]
      populationPartial (tiltPartial Q) := by
    filter_upwards [hQ.eventually_analyticAt] with u hu
    exact analytic_partials_commute Q u hu
  have hcommP : populationPartial (tiltPartial (populationPartial Q)) (0, 0) =
      populationPartial (populationPartial (tiltPartial Q)) (0, 0) :=
    congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hcomm.fderiv_eq
  have hcommT : tiltPartial (tiltPartial (populationPartial Q)) (0, 0) =
      tiltPartial (populationPartial (tiltPartial Q)) (0, 0) :=
    congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hcomm.fderiv_eq
  rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ',
    (analytic_curve_deriv_split Q τ hQ hτ hz).iteratedDeriv_eq,
    iteratedDeriv_fun_add
      (f := fun e => populationPartial Q (e, τ e))
      (g := fun e => tiltPartial Q (e, τ e) * deriv τ e)
      hPc.contDiffAt (hTc.mul hτ.deriv).contDiffAt,
    analytic_mul_iteratedDeriv2 _ _ hTc hτ.deriv]
  dsimp only [c]
  rw [analytic_curve_deriv2_partials (populationPartial Q) τ hP hτ hz,
    analytic_curve_deriv2_partials (tiltPartial Q) τ hT hτ hz,
    analytic_curve_deriv_split_zero (tiltPartial Q) τ hT hτ hz,
    hcommP, hcommT, analytic_partials_commute (tiltPartial Q) (0, 0) hT,
    analytic_partials_commute Q (0, 0) hQ]
  simp only [hz, show deriv (deriv τ) 0 = iteratedDeriv 2 τ 0 by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero],
    show iteratedDeriv 2 (deriv τ) 0 = iteratedDeriv 3 τ 0 by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
  ring

end

end ExactHoeffding
