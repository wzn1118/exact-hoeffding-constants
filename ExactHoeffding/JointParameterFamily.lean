import ExactHoeffding.RescaledActualProxy

/-! # Independent inverse-population and success-imbalance parameters

The two parameters `e` and `d` are independent real variables.  In particular,
`d` is not restricted to a fixed multiple of `e`.  The finite factorial-basis
MGF agrees with the actual hypergeometric MGF at every legal population and
success count, and its binomial limit retains the free success proportion.
-/

namespace ExactHoeffding
noncomputable section
open scoped Topology

/-- The freely varying success fraction. -/
def jointSuccessFraction (d : ℝ) : ℝ := (1 - d) / 2

/-- Factorial coefficients with independent inverse population and imbalance. -/
def jointFactorialMoment (m q : ℕ) (e d : ℝ) : ℝ :=
  (Nat.descFactorial m q : ℝ) * scaledFalling (jointSuccessFraction d) e q /
    rescaledPopulationDenom q e

@[simp] theorem jointFactorialMoment_degree_zero (m : ℕ) (e d : ℝ) :
    jointFactorialMoment m 0 e d = 1 := by
  simp [jointFactorialMoment, rescaledPopulationDenom]

@[simp] theorem jointFactorialMoment_at_zero (m q : ℕ) (d : ℝ) :
    jointFactorialMoment m q 0 d =
      (Nat.descFactorial m q : ℝ) * jointSuccessFraction d ^ q := by
  simp [jointFactorialMoment]

/-- The continuation contains the fixed-imbalance inverse-population curves. -/
theorem jointFactorialMoment_rescaled (m q : ℕ) (s e : ℝ) :
    jointFactorialMoment m q e (s * e) = rescaledFactorialMoment m s q e := by
  rfl

/-- The actual finite factorial moment at an arbitrary legal success count. -/
theorem jointFactorialMoment_hypergeom (N k m q : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N) (hq : q ≤ N) :
    jointFactorialMoment m q (1 / (N : ℝ)) (1 - 2 * (k : ℝ) / N) =
      hypergeomFactorialMoment N k m q := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hdeq : 1 - 2 * (k : ℝ) / N =
      ((N : ℝ) - 2 * (k : ℝ)) * (1 / (N : ℝ)) := by
    field_simp [hN0]
  rw [hdeq, jointFactorialMoment_rescaled]
  exact rescaledFactorialMoment_hypergeom N k m q _ hN hk hm hq (by ring)

/-- MGF in factorial coordinates.  The tilt is a third independent variable. -/
def jointMGF (m : ℕ) (e d t : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (m + 1),
    jointFactorialMoment m q e d / (Nat.factorial q : ℝ) *
      (Real.exp t - 1) ^ q

@[simp] theorem jointMGF_tilt_zero (m : ℕ) (e d : ℝ) :
    jointMGF m e d 0 = 1 := by
  unfold jointMGF
  simp only [Real.exp_zero, sub_self]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro q hq hq0
    simp [zero_pow hq0]
  · simp

theorem jointMGF_rescaled (m : ℕ) (s e t : ℝ) :
    jointMGF m e (s * e) t = rescaledMGF m s e t := by
  rfl

/-- Actual MGF equality for every legal success count, without fixing `N-2k`. -/
theorem jointMGF_hypergeom (N k m : ℕ) (t : ℝ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N) :
    jointMGF m (1 / (N : ℝ)) (1 - 2 * (k : ℝ) / N) t =
      hypergeomMGF N k m t := by
  rw [jointMGF, hypergeomMGF_factorial_basis]
  apply Finset.sum_congr rfl
  intro q hq
  rw [jointFactorialMoment_hypergeom N k m q hN hk hm
    ((Nat.le_of_lt_succ (Finset.mem_range.mp hq)).trans hm)]

/-- At zero inverse population the complete binomial law survives for every
success fraction, rather than only the balanced binomial law. -/
theorem jointMGF_at_zero (m : ℕ) (d t : ℝ) :
    jointMGF m 0 d t =
      (1 - jointSuccessFraction d + jointSuccessFraction d * Real.exp t) ^ m := by
  have hfact (q : ℕ) : (Nat.descFactorial m q : ℝ) /
      (Nat.factorial q : ℝ) = (Nat.choose m q : ℝ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
    have hq : (Nat.factorial q : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
    field_simp
  unfold jointMGF
  simp_rw [jointFactorialMoment_at_zero, mul_div_right_comm, hfact]
  have hsum := add_pow (jointSuccessFraction d * (Real.exp t - 1)) (1 : ℝ) m
  have hbase : jointSuccessFraction d * (Real.exp t - 1) + 1 =
      1 - jointSuccessFraction d + jointSuccessFraction d * Real.exp t := by ring
  rw [hbase] at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [one_pow, mul_one, mul_pow]
  ring

/-- Analyticity of a factorial coefficient on the full three-variable domain. -/
theorem jointFactorialMoment_analytic (m q : ℕ) (u : ℝ × (ℝ × ℝ))
    (hu : rescaledPopulationDenom q u.1 ≠ 0) :
    AnalyticAt ℝ (fun v : ℝ × (ℝ × ℝ) =>
      jointFactorialMoment m q v.1 v.2.1) u := by
  unfold jointFactorialMoment rescaledPopulationDenom scaledFalling jointSuccessFraction
  apply AnalyticAt.div
  · apply AnalyticAt.mul analyticAt_const
    apply Finset.analyticAt_fun_prod
    intro j hj
    exact ((analyticAt_const.sub
      (analyticAt_fst.comp analyticAt_snd)).div_const).sub
        (analyticAt_const.mul analyticAt_fst)
  · apply Finset.analyticAt_fun_prod
    intro j hj
    exact analyticAt_const.sub (analyticAt_const.mul analyticAt_fst)
  · exact hu

/-- Joint analyticity in inverse population, imbalance and tilt near every
point on the binomial axis. -/
theorem jointMGF_analytic (m : ℕ) (d t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ × (ℝ × ℝ) => jointMGF m u.1 u.2.1 u.2.2)
      (0, (d, t)) := by
  unfold jointMGF
  apply Finset.analyticAt_fun_sum
  intro q hq
  exact ((jointFactorialMoment_analytic m q (0, (d, t)) (by simp)).div_const).mul
    (((analyticAt_snd.comp analyticAt_snd).rexp'.sub analyticAt_const).pow q)

end
end ExactHoeffding
