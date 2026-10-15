import ExactHoeffding.JointAnalyticOptimizer
import ExactHoeffding.RealMarginMoments
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Real-law representation and reflection of the independent-parameter family -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

private theorem cast_descFactorial_div_factorial_joint (i q : ℕ) :
    (Nat.descFactorial i q : ℝ) / (Nat.factorial q : ℝ) = (Nat.choose i q : ℝ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hq : (Nat.factorial q : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  field_simp

/-- The factorial-coordinate continuation is exactly the MGF of the
normalized real-margin masses wherever their common denominator is nonzero. -/
theorem jointMGF_realMargin (m : ℕ) (e d t : ℝ)
    (hden : scaledFalling 1 e m ≠ 0) :
    jointMGF m e d t = finiteMGF (Finset.range (m+1))
      (realMarginMass m e (jointSuccessFraction d)) (fun i => (i : ℝ)) t := by
  have hfac (q : ℕ) (hq : q ≤ m) : jointFactorialMoment m q e d =
      ∑ i ∈ Finset.range (m+1), (Nat.descFactorial i q : ℝ) *
        realMarginMass m e (jointSuccessFraction d) i := by
    rw [realMarginMass_factorialMoment m q e _ hq hden]
    rfl
  unfold jointMGF finiteMGF
  have hsum : (∑ q ∈ Finset.range (m+1),
      jointFactorialMoment m q e d / (Nat.factorial q : ℝ) * (Real.exp t-1)^q) =
      ∑ q ∈ Finset.range (m+1),
        (∑ i ∈ Finset.range (m+1), (Nat.descFactorial i q : ℝ) *
          realMarginMass m e (jointSuccessFraction d) i) /
          (Nat.factorial q : ℝ) * (Real.exp t-1)^q := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [hfac q (Nat.le_of_lt_succ (Finset.mem_range.mp hq))]
  rw [hsum]
  simp_rw [Finset.sum_div, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  calc
    _ = realMarginMass m e (jointSuccessFraction d) i *
        ∑ q ∈ Finset.range (m+1), (Nat.choose i q : ℝ) * (Real.exp t-1)^q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [mul_div_right_comm, cast_descFactorial_div_factorial_joint]
      ring
    _ = realMarginMass m e (jointSuccessFraction d) i *
        ∑ q ∈ Finset.range (i+1), (Nat.choose i q : ℝ) * (Real.exp t-1)^q := by
      congr 1
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ him))
      intro q hqm hqi
      have hiq : i < q := by
        have : ¬ q < i+1 := by simpa only [Finset.mem_range] using hqi
        omega
      simp [Nat.choose_eq_zero_of_lt hiq]
    _ = _ := by
      have hp := add_pow (Real.exp t-1) (1 : ℝ) i
      simp only [sub_add_cancel, one_pow, mul_one] at hp
      have hp' : (∑ q ∈ Finset.range (i+1),
          (Nat.choose i q : ℝ) * (Real.exp t-1)^q) = Real.exp t ^ i := by
        simpa only [mul_comm] using hp.symm
      rw [hp', ← Real.exp_nat_mul]
      simp [mul_comm]

/-- Complementing a continuous margin reverses the tilt in the actual
finite-law MGF. -/
theorem realMarginMGF_reflection (m : ℕ) (e p t : ℝ) :
    finiteMGF (Finset.range (m+1)) (realMarginMass m e (1-p))
      (fun i => (i : ℝ)) t = Real.exp (t*(m : ℝ)) *
      finiteMGF (Finset.range (m+1)) (realMarginMass m e p)
        (fun i => (i : ℝ)) (-t) := by
  unfold finiteMGF
  rw [← Finset.sum_range_reflect (fun i =>
    realMarginMass m e (1-p) i * Real.exp (t*(i : ℝ))) (m+1)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [show m+1-1-i=m-i by omega,
    realMarginMass_reflection m (m-i) e p (Nat.sub_le _ _), Nat.sub_sub_self him,
    Nat.cast_sub him]
  have hexp : Real.exp (t * ((m : ℝ)-(i : ℝ))) =
      Real.exp (t*(m : ℝ))*Real.exp ((-t)*(i : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Exact success-complement symmetry for the independent parameters. -/
theorem jointMGF_reflection (m : ℕ) (e d t : ℝ)
    (hden : scaledFalling 1 e m ≠ 0) :
    jointMGF m e (-d) t = Real.exp (t*(m : ℝ)) * jointMGF m e d (-t) := by
  rw [jointMGF_realMargin m e (-d) t hden,
    jointMGF_realMargin m e d (-t) hden]
  have hp : jointSuccessFraction (-d) = 1-jointSuccessFraction d := by
    unfold jointSuccessFraction
    ring
  rw [hp, realMarginMGF_reflection]

/-- The centered log-MGF is invariant under simultaneous imbalance and
tilt reflection. -/
theorem jointCenteredLogMGF_reflection (m : ℕ) (e d t : ℝ)
    (hden : scaledFalling 1 e m ≠ 0) (hM : jointMGF m e d (-t) ≠ 0) :
    Real.log (jointMGF m e (-d) t) - jointMean m e (-d)*t =
      Real.log (jointMGF m e d (-t)) - jointMean m e d*(-t) := by
  rw [jointMGF_reflection m e d t hden, Real.log_mul (Real.exp_ne_zero _) hM,
    Real.log_exp]
  unfold jointMean jointSuccessFraction
  ring


theorem jointMGFQuadratic_tilt_zero (m : ℕ) (e d : ℝ) :
    jointMGFQuadratic m e d 0 =
      (jointMean m e d + jointFactorialMoment m 2 e d) / 2 := by
  unfold jointMGFQuadratic
  rw [expQuadraticKernel_at_zero, expSlopeKernel_zero]
  have htail :
      (∑ j ∈ Finset.range (m-1), jointFactorialMoment m (j+2) e d /
        (Nat.factorial (j+2) : ℝ) * 0^j * 1^(j+2)) =
      jointFactorialMoment m 2 e d / 2 := by
    by_cases hm2 : 2 ≤ m
    · rw [Finset.sum_eq_single 0]
      · norm_num
      · intro j hj hj0
        simp [hj0]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim
    · have hz : jointFactorialMoment m 2 e d = 0 := by
        unfold jointFactorialMoment
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : m<2)]
        simp
      rw [show m-1=0 by omega, hz]
      simp
  rw [htail]
  ring

theorem jointProxyExtension_tilt_zero (m : ℕ) (e d : ℝ) :
    jointProxyExtension m e d 0 = jointMean m e d +
      jointFactorialMoment m 2 e d - jointMean m e d ^ 2 := by
  unfold jointProxyExtension jointMGFSlope
  rw [jointMGFQuadratic_tilt_zero]
  simp only [zero_mul, add_zero, logQuadraticKernel_zero]
  ring

/-- The removable zero-tilt value is the exact real-margin variance. -/
theorem jointProxyExtension_zero_tilt_formula (m : ℕ) (e d : ℝ)
    (he : 1-e ≠ 0) :
    jointProxyExtension m e d 0 =
      (m : ℝ)*(1-d^2)*(1-(m : ℝ)*e)/(4*(1-e)) := by
  rw [jointProxyExtension_tilt_zero]
  simp only [jointMean, jointFactorialMoment, jointSuccessFraction,
    rescaledPopulationDenom, scaledFalling_succ, scaledFalling_zero,
    Nat.cast_descFactorial_two]
  norm_num
  field_simp [he]
  ring

/-- The removable proxy respects exact simultaneous reflection, including
zero tilt. -/
theorem jointProxyExtension_reflection (m : ℕ) (hm : 1 ≤ m) (e d t : ℝ)
    (hden : scaledFalling 1 e m ≠ 0) (he : 1-e ≠ 0)
    (hM : jointMGF m e d (-t) ≠ 0) :
    jointProxyExtension m e (-d) t = jointProxyExtension m e d (-t) := by
  by_cases ht : t=0
  · subst t
    rw [neg_zero, jointProxyExtension_zero_tilt_formula m e (-d) he,
      jointProxyExtension_zero_tilt_formula m e d he]
    ring
  · rw [jointProxyExtension_eq_quotient m hm e (-d) t ht,
      jointProxyExtension_eq_quotient m hm e d (-t) (neg_ne_zero.mpr ht),
      jointCenteredLogMGF_reflection m e d t hden hM]
    ring

end

end ExactHoeffding
