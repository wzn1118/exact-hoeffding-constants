import ExactHoeffding.RealMarginLogDerivatives
import ExactHoeffding.RescaledProxyAnalytic
import ExactHoeffding.AnalyticImplicitTilt

/-! # A jointly analytic proxy for the actual finite real-margin law -/

namespace ExactHoeffding
noncomputable section
open Filter Finset
open scoped Topology

def realMarginMean (m : ℕ) (d : ℝ) : ℝ := (m:ℝ)*((1-d)/2)

def realMarginMGFQuadratic (N m : ℕ) (d t : ℝ) : ℝ :=
  ∑ i ∈ range (m+1), realMarginMass m (1/(N:ℝ)) ((1-d)/2) i *
    (i:ℝ)^2 * expQuadraticKernel (t*(i:ℝ))

def realMarginMGFSlope (N m : ℕ) (d t : ℝ) : ℝ :=
  realMarginMean m d + t*realMarginMGFQuadratic N m d t

def realMarginProxy (N m : ℕ) (d t : ℝ) : ℝ :=
  2*(realMarginMGFQuadratic N m d t + realMarginMGFSlope N m d t^2 *
    logQuadraticKernel (t*realMarginMGFSlope N m d t))

private theorem realMarginMass_fixed_joint_analytic (N m i : ℕ) (z : ℝ × ℝ)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => realMarginMass m (1/(N:ℝ)) ((1-u.1)/2) i) z := by
  exact (realMarginMass_joint_analytic m i (1/(N:ℝ), (1-z.1)/2) hden).comp_of_eq
    (analyticAt_const.prod ((analyticAt_const.sub analyticAt_fst).div_const)) rfl

/-- The singular division by `t²` is removed by explicit entire exponential
kernels; the resulting objective is analytic jointly in margin and tilt. -/
theorem realMarginProxy_joint_analytic (N m : ℕ)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => realMarginProxy N m u.1 u.2) (0,0) := by
  have hA : AnalyticAt ℝ (fun u : ℝ × ℝ => realMarginMGFQuadratic N m u.1 u.2) (0,0) := by
    unfold realMarginMGFQuadratic
    apply Finset.analyticAt_fun_sum
    intro i hi
    apply AnalyticAt.mul
    · exact (realMarginMass_fixed_joint_analytic N m i _ hden).mul analyticAt_const
    · exact expQuadraticKernel_analytic.comp_of_eq
        (analyticAt_snd.mul analyticAt_const) (by simp)
  have hS : AnalyticAt ℝ (fun u : ℝ × ℝ => realMarginMGFSlope N m u.1 u.2) (0,0) := by
    unfold realMarginMGFSlope realMarginMean
    exact (analyticAt_const.mul ((analyticAt_const.sub analyticAt_fst).div_const)).add
      (analyticAt_snd.mul hA)
  unfold realMarginProxy
  exact analyticAt_const.mul (hA.add ((hS.pow 2).mul
    (logQuadraticKernel_analytic.comp_of_eq (analyticAt_snd.mul hS) (by simp))))

/-- Exact quadratic factorization of the actual finite exponential moment. -/
theorem realMarginMGF_quadratic_factor (N m : ℕ) (d t : ℝ)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) :
    finiteMGF (range (m+1)) (realMarginMass m (1/(N:ℝ)) ((1-d)/2))
      (fun i => (i:ℝ)) t =
        1+realMarginMean m d*t+t^2*realMarginMGFQuadratic N m d t := by
  have hmean := realMarginMass_mean m (1/(N:ℝ)) ((1-d)/2) hden
  have hsum := realMarginMass_sum m (1/(N:ℝ)) ((1-d)/2) hden
  unfold realMarginMean
  conv_rhs => lhs; lhs; rw [← hsum]
  conv_rhs => lhs; rhs; rw [← hmean]
  unfold finiteMGF realMarginMGFQuadratic
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h1 := exp_sub_one_factor (t*(i:ℝ))
  have h2 := expSlopeKernel_factor (t*(i:ℝ))
  nlinarith [congrArg (fun x:ℝ => realMarginMass m (1/(N:ℝ)) ((1-d)/2) i*x) h1,
    congrArg (fun x:ℝ => realMarginMass m (1/(N:ℝ)) ((1-d)/2) i*t*(i:ℝ)*x) h2]

/-- The analytic objective is exactly twice the centered log-Laplace
transform divided by the square tilt wherever the tilt is nonzero. -/
theorem realMarginProxy_factor (N m : ℕ) (d t : ℝ)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) :
    realMarginCenteredLogMGF N m d t = t^2*realMarginProxy N m d t/2 := by
  have hM := realMarginMGF_quadratic_factor N m d t hden
  have hlog := logOnePlus_quadratic_factor (t*realMarginMGFSlope N m d t)
  have hbase : 1+t*realMarginMGFSlope N m d t =
      finiteMGF (range (m+1)) (realMarginMass m (1/(N:ℝ)) ((1-d)/2))
        (fun i => (i:ℝ)) t := by
    rw [hM, realMarginMGFSlope]
    ring
  rw [hbase] at hlog
  unfold realMarginCenteredLogMGF realMarginProxy realMarginMGFSlope realMarginMean at *
  rw [hlog]
  ring

/-- The completed value is the actual variance, including `m=1`. -/
theorem realMarginProxy_zero (N m : ℕ) (d : ℝ)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) :
    realMarginProxy N m d 0 = marginCumulant2 N m d := by
  have hmoment := realMarginMass_rawMoment N m 2 d (by omega) hden
  have hm := realMarginMass_mean m (1/(N:ℝ)) ((1-d)/2) hden
  have hone := realMarginMass_rawMoment N m 1 d (by omega) hden
  unfold realMarginProxy realMarginMGFSlope realMarginMGFQuadratic realMarginMean
  simp only [zero_mul, add_zero, expQuadraticKernel_at_zero,
    logQuadraticKernel_zero]
  rw [← Finset.sum_mul]
  have hraw : (∑ i ∈ range (m+1), realMarginMass m (1/(N:ℝ)) ((1-d)/2) i * (i:ℝ)^2) =
      finiteRawMoment (range (m+1)) (fun i => (i:ℝ))
        (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  rw [hraw]
  rw [hmoment]
  have hmean : marginRawMoment N m 1 d = (m:ℝ)*((1-d)/2) := by
    rw [← hone]
    simpa [finiteRawMoment] using hm
  rw [marginCumulant2, hmean]
  ring

/-- Every nonzero tilt uses the actual centered log-Laplace quotient. -/
theorem realMarginProxy_eq_quotient (N m : ℕ) (d t : ℝ)
    (hden : scaledFalling 1 (1/(N:ℝ)) m ≠ 0) (ht : t ≠ 0) :
    realMarginProxy N m d t = 2*realMarginCenteredLogMGF N m d t/t^2 := by
  rw [realMarginProxy_factor N m d t hden]
  field_simp

end
end ExactHoeffding
