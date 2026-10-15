import ExactHoeffding.JointParameterFamily

/-! # Three-variable analytic continuation of the actual sharp-proxy objective -/

namespace ExactHoeffding
noncomputable section
open scoped Topology

def jointMean (m : ℕ) (_e d : ℝ) : ℝ := (m : ℝ) * jointSuccessFraction d

theorem jointFactorialMoment_degree_one (m : ℕ) (e d : ℝ) :
    jointFactorialMoment m 1 e d = jointMean m e d := by
  simp [jointFactorialMoment, jointMean, rescaledPopulationDenom,
    scaledFalling]

def jointMGFQuadratic (m : ℕ) (e d t : ℝ) : ℝ :=
  jointMean m e d * expQuadraticKernel t +
    ∑ j ∈ Finset.range (m - 1),
      jointFactorialMoment m (j + 2) e d / (Nat.factorial (j + 2) : ℝ) *
        t ^ j * expSlopeKernel t ^ (j + 2)

theorem jointMGF_split (m : ℕ) (hm : 1 ≤ m) (e d t : ℝ) :
    jointMGF m e d t = 1 + jointMean m e d * (Real.exp t - 1) +
      ∑ j ∈ Finset.range (m - 1),
        jointFactorialMoment m (j + 2) e d / (Nat.factorial (j + 2) : ℝ) *
          (Real.exp t - 1) ^ (j + 2) := by
  unfold jointMGF
  rw [show m + 1 = 2 + (m - 1) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    jointFactorialMoment_degree_zero, jointFactorialMoment_degree_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one, pow_zero,
    pow_one, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_comm 2 j]

theorem jointMGF_quadratic_factor (m : ℕ) (hm : 1 ≤ m) (e d t : ℝ) :
    jointMGF m e d t =
      1 + jointMean m e d * t + t ^ 2 * jointMGFQuadratic m e d t := by
  rw [jointMGF_split m hm, jointMGFQuadratic, mul_add, Finset.mul_sum]
  have htail :
      (∑ j ∈ Finset.range (m - 1),
        jointFactorialMoment m (j + 2) e d / (Nat.factorial (j + 2) : ℝ) *
          (Real.exp t - 1) ^ (j + 2)) =
      ∑ j ∈ Finset.range (m - 1),
        t ^ 2 * (jointFactorialMoment m (j + 2) e d /
          (Nat.factorial (j + 2) : ℝ) * t ^ j * expSlopeKernel t ^ (j + 2)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [exp_sub_one_factor, mul_pow, pow_add]
    ring
  rw [htail, exp_sub_one_factor]
  have h := expSlopeKernel_factor t
  nlinarith [congrArg (fun r : ℝ => jointMean m e d * t * r) h]

def jointMGFSlope (m : ℕ) (e d t : ℝ) : ℝ :=
  jointMean m e d + t * jointMGFQuadratic m e d t

def jointProxyExtension (m : ℕ) (e d t : ℝ) : ℝ :=
  2 * (jointMGFQuadratic m e d t + jointMGFSlope m e d t ^ 2 *
    logQuadraticKernel (t * jointMGFSlope m e d t))

theorem jointMGFQuadratic_analytic (m : ℕ) :
    AnalyticAt ℝ (fun u : ℝ × (ℝ × ℝ) =>
      jointMGFQuadratic m u.1 u.2.1 u.2.2) (0, (0, 0)) := by
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
    exact (((jointFactorialMoment_analytic m (j + 2) (0, (0, 0))
      (by simp)).div_const).mul ((analyticAt_snd.comp analyticAt_snd).pow j)).mul
        ((expSlopeKernel_analytic.comp_of_eq
          (analyticAt_snd.comp analyticAt_snd) rfl).pow (j + 2))

theorem jointMGFSlope_analytic (m : ℕ) :
    AnalyticAt ℝ (fun u : ℝ × (ℝ × ℝ) =>
      jointMGFSlope m u.1 u.2.1 u.2.2) (0, (0, 0)) := by
  unfold jointMGFSlope jointMean jointSuccessFraction
  exact (analyticAt_const.mul
    ((analyticAt_const.sub (analyticAt_fst.comp analyticAt_snd)).div_const)).add
      ((analyticAt_snd.comp analyticAt_snd).mul (jointMGFQuadratic_analytic m))

/-- The removable objective is analytic jointly in all three independent
variables; division by the tilt is removed constructively. -/
theorem jointProxyExtension_analytic (m : ℕ) :
    AnalyticAt ℝ (fun u : ℝ × (ℝ × ℝ) =>
      jointProxyExtension m u.1 u.2.1 u.2.2) (0, (0, 0)) := by
  unfold jointProxyExtension
  apply AnalyticAt.mul analyticAt_const
  apply (jointMGFQuadratic_analytic m).add
  apply ((jointMGFSlope_analytic m).pow 2).mul
  exact logQuadraticKernel_analytic.comp_of_eq
    ((analyticAt_snd.comp analyticAt_snd).mul (jointMGFSlope_analytic m)) (by simp)

theorem joint_logMGF_quadratic_factor (m : ℕ) (hm : 1 ≤ m) (e d t : ℝ) :
    Real.log (jointMGF m e d t) - jointMean m e d * t =
      t ^ 2 * jointProxyExtension m e d t / 2 := by
  have hM := jointMGF_quadratic_factor m hm e d t
  have hlog := logOnePlus_quadratic_factor (t * jointMGFSlope m e d t)
  have hbase : 1 + t * jointMGFSlope m e d t = jointMGF m e d t := by
    rw [hM, jointMGFSlope]
    ring
  rw [hbase] at hlog
  rw [hlog, jointProxyExtension, jointMGFSlope]
  ring

/-- Away from zero, the analytic extension is the actual centered quotient. -/
theorem jointProxyExtension_eq_quotient (m : ℕ) (hm : 1 ≤ m)
    (e d t : ℝ) (ht : t ≠ 0) :
    jointProxyExtension m e d t =
      2 * (Real.log (jointMGF m e d t) - jointMean m e d * t) / t ^ 2 := by
  rw [joint_logMGF_quadratic_factor m hm]
  field_simp

/-- Restriction to every fixed imbalance curve recovers the existing analytic
objective exactly, including its removable value. -/
theorem jointProxyExtension_rescaled (m : ℕ) (s e t : ℝ) :
    jointProxyExtension m e (s * e) t = rescaledProxyExtension m s e t := by
  have hmean : jointMean m e (s * e) = rescaledMean m s e := by
    unfold jointMean rescaledMean jointSuccessFraction
    ring
  have hquad : jointMGFQuadratic m e (s * e) t = rescaledMGFQuadratic m s e t := by
    unfold jointMGFQuadratic rescaledMGFQuadratic
    rw [hmean]
    congr 1
  have hslope : jointMGFSlope m e (s * e) t = rescaledMGFSlope m s e t := by
    simp only [jointMGFSlope, rescaledMGFSlope, hmean, hquad]
  simp only [jointProxyExtension, rescaledProxyExtension, hquad, hslope]

/-- At every physical parameter the joint objective is the actual finite-law
proxy for every real tilt, including zero. -/
theorem jointProxyExtension_hypergeom (N k m : ℕ) (t : ℝ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hm : m ≤ N) (hmpos : 1 ≤ m) :
    jointProxyExtension m (1 / (N : ℝ)) (1 - 2 * (k : ℝ) / N) t =
      actualHypergeomProxy N k m t := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hdeq : 1 - 2 * (k : ℝ) / N =
      ((N : ℝ) - 2 * (k : ℝ)) * (1 / (N : ℝ)) := by
    field_simp [hN0]
  rw [hdeq, jointProxyExtension_rescaled]
  exact rescaledProxyExtension_hypergeom N k m _ t hN hk hm hmpos (by ring)


end
end ExactHoeffding
