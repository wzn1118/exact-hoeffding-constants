import ExactHoeffding.JointOptimizerLocalization

/-! # Three-variable analyticity along the complete binomial parameter axis -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

theorem jointMGFQuadratic_analytic_free_axis (m : ℕ) (d : ℝ) :
    AnalyticAt ℝ (fun u : ℝ × (ℝ × ℝ) =>
      jointMGFQuadratic m u.1 u.2.1 u.2.2) (0, (d, 0)) := by
  unfold jointMGFQuadratic
  apply AnalyticAt.add
  · apply AnalyticAt.mul
    · unfold jointMean jointSuccessFraction
      exact (analyticAt_const.mul
        ((analyticAt_const.sub (analyticAt_fst.comp analyticAt_snd)).div_const))
    · exact expQuadraticKernel_analytic.comp_of_eq
        (analyticAt_snd.comp analyticAt_snd) rfl
  · apply Finset.analyticAt_fun_sum
    intro j hj
    exact (((jointFactorialMoment_analytic m (j + 2) (0, (d, 0))
      (by simp)).div_const).mul ((analyticAt_snd.comp analyticAt_snd).pow j)).mul
        ((expSlopeKernel_analytic.comp_of_eq
          (analyticAt_snd.comp analyticAt_snd) rfl).pow (j + 2))

theorem jointMGFSlope_analytic_free_axis (m : ℕ) (d : ℝ) :
    AnalyticAt ℝ (fun u : ℝ × (ℝ × ℝ) =>
      jointMGFSlope m u.1 u.2.1 u.2.2) (0, (d, 0)) := by
  unfold jointMGFSlope jointMean jointSuccessFraction
  exact (analyticAt_const.mul
    ((analyticAt_const.sub (analyticAt_fst.comp analyticAt_snd)).div_const)).add
      ((analyticAt_snd.comp analyticAt_snd).mul (jointMGFQuadratic_analytic_free_axis m d))

/-- The removable objective is analytic jointly in all three independent
variables at every free imbalance; division by the tilt is removed constructively. -/
theorem jointProxyExtension_analytic_free_axis (m : ℕ) (d : ℝ) :
    AnalyticAt ℝ (fun u : ℝ × (ℝ × ℝ) =>
      jointProxyExtension m u.1 u.2.1 u.2.2) (0, (d, 0)) := by
  unfold jointProxyExtension
  apply AnalyticAt.mul analyticAt_const
  apply (jointMGFQuadratic_analytic_free_axis m d).add
  apply ((jointMGFSlope_analytic_free_axis m d).pow 2).mul
  exact logQuadraticKernel_analytic.comp_of_eq
    ((analyticAt_snd.comp analyticAt_snd).mul (jointMGFSlope_analytic_free_axis m d)) (by simp)

/-- The actual removable objective is jointly analytic at every limiting
binomial parameter with interior success proportion and arbitrary real tilt. -/
theorem jointProxyObjective_analytic_full_axis (m : ℕ) (d t : ℝ)
    (hd : d ∈ Ioo (-1 : ℝ) 1) :
    AnalyticAt ℝ (jointProxyObjective m) ((0,d),t) := by
  by_cases hm0 : m=0
  · subst m
    have hz : jointProxyObjective 0 = (fun _ : (ℝ × ℝ) × ℝ => (0 : ℝ)) := by
      funext u
      simp [jointProxyObjective, jointProxyExtension, jointMGFSlope,
        jointMGFQuadratic, jointMean, jointSuccessFraction]
    rw [hz]
    exact analyticAt_const
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  by_cases ht : t=0
  · subst t
    exact (jointProxyExtension_analytic_free_axis m d).comp_of_eq
      (f := fun u : (ℝ × ℝ) × ℝ => (u.1.1,(u.1.2,u.2)))
      ((analyticAt_fst.comp analyticAt_fst).prod
        ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)) rfl
  have hM : AnalyticAt ℝ (fun u : (ℝ × ℝ) × ℝ =>
      jointMGF m u.1.1 u.1.2 u.2) ((0,d),t) :=
    (jointMGF_analytic m d t).comp_of_eq
      (f := fun u : (ℝ × ℝ) × ℝ => (u.1.1,(u.1.2,u.2)))
      ((analyticAt_fst.comp analyticAt_fst).prod
        ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)) rfl
  have hpos : 0 < jointMGF m 0 d t := by
    rw [jointMGF_at_zero]
    have hp : 0 < jointSuccessFraction d := by unfold jointSuccessFraction; linarith [hd.2]
    have hq : 0 < 1-jointSuccessFraction d := by unfold jointSuccessFraction; linarith [hd.1]
    positivity
  have hmean : AnalyticAt ℝ (fun u : (ℝ × ℝ) × ℝ =>
      jointMean m u.1.1 u.1.2) ((0,d),t) := by
    unfold jointMean jointSuccessFraction
    exact analyticAt_const.mul ((analyticAt_const.sub
      (analyticAt_snd.comp analyticAt_fst)).div_const)
  have hquot : AnalyticAt ℝ (fun u : (ℝ × ℝ) × ℝ =>
      2*(Real.log (jointMGF m u.1.1 u.1.2 u.2)-jointMean m u.1.1 u.1.2*u.2)/u.2^2)
      ((0,d),t) := by
    have hlog : AnalyticAt ℝ (fun u : (ℝ × ℝ) × ℝ =>
        Real.log (jointMGF m u.1.1 u.1.2 u.2)) ((0,d),t) :=
      (analyticAt_log hpos).comp_of_eq hM rfl
    exact (analyticAt_const.mul (hlog.sub
      (hmean.mul analyticAt_snd))).div (analyticAt_snd.pow 2) (pow_ne_zero 2 ht)
  apply hquot.congr
  filter_upwards [(continuousAt_snd : ContinuousAt
    (fun u : (ℝ × ℝ) × ℝ => u.2) ((0,d),t)).eventually_ne ht] with u hu
  exact (jointProxyExtension_eq_quotient m hm u.1.1 u.1.2 u.2 hu).symm

end
end ExactHoeffding
