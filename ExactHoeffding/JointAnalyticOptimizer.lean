import ExactHoeffding.JointImplicitTilt
import ExactHoeffding.JointProxyAnalytic
import ExactHoeffding.RescaledMixedDerivative

/-! # The jointly analytic critical tilt for independent population and imbalance -/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

/-- Reassociate the three independent coordinates so that the implicit
function theorem solves for the scalar tilt and retains both parameters. -/
def jointProxyObjective (m : ℕ) (u : (ℝ × ℝ) × ℝ) : ℝ :=
  jointProxyExtension m u.1.1 u.1.2 u.2

theorem jointProxyObjective_analytic (m : ℕ) :
    AnalyticAt ℝ (jointProxyObjective m) ((0, 0), 0) := by
  exact (jointProxyExtension_analytic m).comp_of_eq
    (f := fun u : (ℝ × ℝ) × ℝ => (u.1.1, (u.1.2, u.2)))
    ((analyticAt_fst.comp analyticAt_fst).prod
      ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)) rfl

theorem jointProxyExtension_balanced_axis (m : ℕ) (e : ℝ) :
    jointProxyExtension m e 0 = rescaledProxyExtension m 0 e := by
  funext t
  simpa using jointProxyExtension_rescaled m 0 e t

theorem jointProxyObjective_origin_deriv (m : ℕ) (hm : 0 < m) :
    jointTiltPartial (jointProxyObjective m) ((0, 0), 0) = 0 := by
  rw [jointTiltPartial_eq_deriv _ _ (jointProxyObjective_analytic m)]
  change deriv (jointProxyExtension m 0 0) 0 = 0
  rw [jointProxyExtension_balanced_axis]
  exact rescaledProxyExtension_limit_deriv_zero m hm 0

theorem jointProxyObjective_origin_curvature (m : ℕ) :
    jointTiltPartial (jointTiltPartial (jointProxyObjective m)) ((0, 0), 0) =
      -(m : ℝ) / 48 := by
  rw [jointTiltPartial2_eq_iteratedDeriv2 _ _ (jointProxyObjective_analytic m)]
  change iteratedDeriv 2 (jointProxyExtension m 0 0) 0 = _
  rw [jointProxyExtension_balanced_axis, rescaledProxyExtension_limit_deriv2]

/-- The stationary branch is constructed from the actual three-variable
objective.  Its zero-set characterization gives local existence and uniqueness
of the critical tilt jointly in inverse population and imbalance. -/
theorem jointProxyExtension_analytic_critical_branch
    (m : ℕ) (hm : 0 < m) :
    ∃ τ : ℝ × ℝ → ℝ, AnalyticAt ℝ τ (0, 0) ∧ τ (0, 0) = 0 ∧
      (∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0),
        deriv (jointProxyExtension m u.1.1 u.1.2) u.2 = 0 ↔ τ u.1 = u.2) := by
  have hQ := jointProxyObjective_analytic m
  have hnonzero : jointTiltPartial (jointTiltPartial (jointProxyObjective m))
      ((0, 0), 0) ≠ 0 := by
    rw [jointProxyObjective_origin_curvature]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    linarith
  obtain ⟨τ, hτ, hτzero, heq⟩ := analytic_implicit_joint_tilt
    (jointTiltPartial (jointProxyObjective m))
    (analyticAt_jointTiltPartial _ _ hQ)
    (jointProxyObjective_origin_deriv m hm) hnonzero
  refine ⟨τ, hτ, hτzero, ?_⟩
  filter_upwards [heq, hQ.eventually_analyticAt] with u hu hQu
  simpa only [jointTiltPartial_eq_deriv _ u hQu, jointProxyObjective] using hu

/-- Balanced real margins have zero critical tilt throughout a neighborhood
of inverse population zero, as an exact identity rather than a limit. -/
theorem jointProxyExtension_balanced_deriv_zero (m : ℕ) (e : ℝ)
    (h1 : 1 - e ≠ 0) (h2 : 1 - 2 * e ≠ 0) :
    deriv (jointProxyExtension m e 0) 0 = 0 := by
  rw [jointProxyExtension_balanced_axis,
    rescaledProxyExtension_deriv_tilt_zero m 0 e h1 h2]
  simp

/-- The analytic critical branch vanishes identically on the local balanced
axis.  Both parameters remain independent off that axis. -/
theorem jointProxyExtension_analytic_critical_branch_balanced
    (m : ℕ) (hm : 0 < m) :
    ∃ τ : ℝ × ℝ → ℝ, AnalyticAt ℝ τ (0, 0) ∧ τ (0, 0) = 0 ∧
      (∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0),
        deriv (jointProxyExtension m u.1.1 u.1.2) u.2 = 0 ↔ τ u.1 = u.2) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), τ (e, 0) = 0) := by
  obtain ⟨τ, hτ, hτzero, heq⟩ := jointProxyExtension_analytic_critical_branch m hm
  refine ⟨τ, hτ, hτzero, heq, ?_⟩
  have hins : ContinuousAt (fun e : ℝ => ((e, (0 : ℝ)), (0 : ℝ))) 0 :=
    (continuousAt_id.prodMk continuousAt_const).prodMk continuousAt_const
  have heqaxis := hins.eventually heq
  have h1 : ∀ᶠ e in 𝓝 (0 : ℝ), 1 - e ≠ 0 :=
    (continuous_const.sub continuous_id).continuousAt.eventually_ne (by norm_num)
  have h2 : ∀ᶠ e in 𝓝 (0 : ℝ), 1 - 2 * e ≠ 0 :=
    (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually_ne
      (by norm_num)
  filter_upwards [heqaxis, h1, h2] with e he he1 he2
  exact he.mp (jointProxyExtension_balanced_deriv_zero m e he1 he2)

/-- Evaluating the jointly analytic objective on its analytic critical
branch gives a jointly analytic optimized germ. -/
theorem jointProxyExtension_critical_value_analytic (m : ℕ)
    (τ : ℝ × ℝ → ℝ) (hτ : AnalyticAt ℝ τ (0, 0)) (hτzero : τ (0, 0) = 0) :
    AnalyticAt ℝ (fun p : ℝ × ℝ => jointProxyExtension m p.1 p.2 (τ p)) (0, 0) := by
  exact (jointProxyObjective_analytic m).comp_of_eq
    (f := fun p : ℝ × ℝ => (p, τ p)) (analyticAt_id.prod hτ) (by simp [hτzero])

end

end ExactHoeffding
