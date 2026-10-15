import ExactHoeffding.RescaledOptimumThird

/-! # Coordinate partial jets of a jointly analytic function

Iterated coordinate partials agree with the corresponding iterated
ordinary derivatives of analytic slices, including mixed population--tilt jets.
-/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem analyticAt_iterate_tiltPartial (n : ℕ) (Q : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (hQ : AnalyticAt ℝ Q u) : AnalyticAt ℝ ((tiltPartial^[n]) Q) u := by
  induction n with
  | zero => exact hQ
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact analyticAt_tiltPartial _ u ih

theorem analyticAt_iterate_populationPartial (n : ℕ) (Q : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (hQ : AnalyticAt ℝ Q u) : AnalyticAt ℝ ((populationPartial^[n]) Q) u := by
  induction n with
  | zero => exact hQ
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact analyticAt_populationPartial _ u ih

theorem iterate_tiltPartial_eq_iteratedDeriv (n : ℕ) (Q : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (hQ : AnalyticAt ℝ Q u) :
    ((tiltPartial^[n]) Q) u = iteratedDeriv n (fun t => Q (u.1, t)) u.2 := by
  induction n generalizing Q u with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', tiltPartial_eq_deriv _ u
        (analyticAt_iterate_tiltPartial n Q u hQ)]
      have hc : ContinuousAt (fun t : ℝ => (u.1, t)) u.2 :=
        continuousAt_const.prodMk continuousAt_id
      have heq : (fun t => ((tiltPartial^[n]) Q) (u.1, t)) =ᶠ[𝓝 u.2]
          iteratedDeriv n (fun t => Q (u.1, t)) := by
        filter_upwards [hc.eventually hQ.eventually_analyticAt] with t ht
        exact ih Q (u.1, t) ht
      rw [heq.deriv_eq, iteratedDeriv_succ]

theorem iterate_populationPartial_eq_iteratedDeriv (n : ℕ)
    (Q : ℝ × ℝ → ℝ) (u : ℝ × ℝ) (hQ : AnalyticAt ℝ Q u) :
    ((populationPartial^[n]) Q) u = iteratedDeriv n (fun e => Q (e, u.2)) u.1 := by
  induction n generalizing Q u with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', populationPartial_eq_deriv _ u
        (analyticAt_iterate_populationPartial n Q u hQ)]
      have hc : ContinuousAt (fun e : ℝ => (e, u.2)) u.1 :=
        continuousAt_id.prodMk continuousAt_const
      have heq : (fun e => ((populationPartial^[n]) Q) (e, u.2)) =ᶠ[𝓝 u.1]
          iteratedDeriv n (fun e => Q (e, u.2)) := by
        filter_upwards [hc.eventually hQ.eventually_analyticAt] with e he
        exact ih Q (e, u.2) he
      rw [heq.deriv_eq, iteratedDeriv_succ]

theorem analytic_mixed_coordinate_jets (n r : ℕ) (Q : ℝ × ℝ → ℝ)
    (hQ : AnalyticAt ℝ Q (0, 0)) :
    ((populationPartial^[n]) ((tiltPartial^[r]) Q)) (0, 0) =
      iteratedDeriv n (fun e => iteratedDeriv r (fun t => Q (e, t)) 0) 0 := by
  rw [iterate_populationPartial_eq_iteratedDeriv n _ (0, 0)
    (analyticAt_iterate_tiltPartial r Q (0, 0) hQ)]
  have hc : ContinuousAt (fun e : ℝ => (e, (0 : ℝ))) 0 :=
    continuousAt_id.prodMk continuousAt_const
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [hc.eventually hQ.eventually_analyticAt] with e he
  exact iterate_tiltPartial_eq_iteratedDeriv r Q (e, 0) he

theorem populationPartial_congr_germ (Q R : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (h : Q =ᶠ[𝓝 u] R) : populationPartial Q =ᶠ[𝓝 u] populationPartial R := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with z hz
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hz

theorem tiltPartial_congr_germ (Q R : ℝ × ℝ → ℝ) (u : ℝ × ℝ)
    (h : Q =ᶠ[𝓝 u] R) : tiltPartial Q =ᶠ[𝓝 u] tiltPartial R := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with z hz
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hz

theorem iterate_tiltPartial_population_commute (r : ℕ) (Q : ℝ × ℝ → ℝ)
    (u : ℝ × ℝ) (hQ : AnalyticAt ℝ Q u) :
    ((tiltPartial^[r]) (populationPartial Q)) =ᶠ[𝓝 u]
      populationPartial ((tiltPartial^[r]) Q) := by
  induction r with
  | zero => exact Filter.EventuallyEq.rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      apply (tiltPartial_congr_germ _ _ u ih).trans
      have hR := analyticAt_iterate_tiltPartial r Q u hQ
      filter_upwards [hR.eventually_analyticAt] with z hz
      exact analytic_partials_commute _ z hz

end

end ExactHoeffding
