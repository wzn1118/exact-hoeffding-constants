import ExactHoeffding.Cumulants
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# A genuine inverse-population family for the nearly balanced law

For fixed sample size `m` and real imbalance `s`, the parameter `e` is an
independent real variable. At `e = 1 / N` and `2*k + s = N`, the factorial
coefficients agree with the actual finite hypergeometric distribution.
This is distinct from fixing a law and expanding only its real tilt.
-/

namespace ExactHoeffding

noncomputable section

open scoped Topology

/-- A falling factorial with real step `e`, with no natural subtraction. -/
def scaledFalling (a e : ℝ) (q : ℕ) : ℝ :=
  ∏ j ∈ Finset.range q, (a - (j : ℝ) * e)

@[simp] theorem scaledFalling_zero (a e : ℝ) : scaledFalling a e 0 = 1 := by
  simp [scaledFalling]

theorem scaledFalling_succ (a e : ℝ) (q : ℕ) :
    scaledFalling a e (q + 1) = scaledFalling a e q * (a - (q : ℝ) * e) := by
  exact Finset.prod_range_succ _ _

@[simp] theorem scaledFalling_step_zero (a : ℝ) (q : ℕ) :
    scaledFalling a 0 q = a ^ q := by
  simp [scaledFalling]

theorem scaledFalling_div_nat (n N q : ℕ) (hq : q ≤ n) :
    scaledFalling ((n : ℝ) / N) (1 / (N : ℝ)) q =
      (Nat.descFactorial n q : ℝ) / (N : ℝ) ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [scaledFalling_succ, ih (by omega), Nat.descFactorial_succ,
        Nat.cast_mul, Nat.cast_sub (by omega), pow_succ]
      ring

theorem scaledFalling_div_nat_all (n N q : ℕ) :
    scaledFalling ((n : ℝ) / N) (1 / (N : ℝ)) q =
      (Nat.descFactorial n q : ℝ) / (N : ℝ) ^ q := by
  by_cases hq : q ≤ n
  · exact scaledFalling_div_nat n N q hq
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega), Nat.cast_zero, zero_div]
    unfold scaledFalling
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (show n < q by omega))
    ring

/-- The denominator that remains after extracting `N^q` from `(N)_q`. -/
def rescaledPopulationDenom (q : ℕ) (e : ℝ) : ℝ :=
  scaledFalling 1 e q

@[simp] theorem rescaledPopulationDenom_zero (q : ℕ) :
    rescaledPopulationDenom q 0 = 1 := by
  simp [rescaledPopulationDenom]

/-- Actual factorial-moment continuation for success fraction `(1-s*e)/2`. -/
def rescaledFactorialMoment (m : ℕ) (s : ℝ) (q : ℕ) (e : ℝ) : ℝ :=
  (Nat.descFactorial m q : ℝ) *
    scaledFalling ((1 - s * e) / 2) e q / rescaledPopulationDenom q e

@[simp] theorem rescaledFactorialMoment_degree_zero (m : ℕ) (s e : ℝ) :
    rescaledFactorialMoment m s 0 e = 1 := by
  simp [rescaledFactorialMoment, rescaledPopulationDenom]

theorem rescaledFactorialMoment_at_zero (m q : ℕ) (s : ℝ) :
    rescaledFactorialMoment m s q 0 =
      (Nat.descFactorial m q : ℝ) * (1 / 2 : ℝ) ^ q := by
  simp [rescaledFactorialMoment]

/-- The algebraic continuation matches the actual factorial moment at each
valid integer population in the nearly balanced regime. -/
theorem rescaledFactorialMoment_hypergeom (N k m q : ℕ) (s : ℝ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N) (hq : q ≤ N)
    (hbalance : 2 * (k : ℝ) + s = (N : ℝ)) :
    rescaledFactorialMoment m s q (1 / (N : ℝ)) =
      hypergeomFactorialMoment N k m q := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hfrac : (1 - s * (1 / (N : ℝ))) / 2 = (k : ℝ) / N := by
    field_simp [hN0]
    linarith
  have hpop : rescaledPopulationDenom q (1 / (N : ℝ)) =
      (Nat.descFactorial N q : ℝ) / (N : ℝ) ^ q := by
    unfold rescaledPopulationDenom
    simpa only [div_self hN0] using scaledFalling_div_nat N N q hq
  rw [rescaledFactorialMoment, hfrac, scaledFalling_div_nat_all k N q, hpop,
    hypergeom_factorial_moment_formula N k m q hk hm, if_pos hq]
  field_simp [hN0]

theorem scaledFalling_joint_analytic (q : ℕ) (a e : ℝ × ℝ → ℝ)
    (z : ℝ × ℝ) (ha : AnalyticAt ℝ a z) (he : AnalyticAt ℝ e z) :
    AnalyticAt ℝ (fun u => scaledFalling (a u) (e u) q) z := by
  unfold scaledFalling
  apply Finset.analyticAt_fun_prod
  intro j hj
  exact ha.sub (analyticAt_const.mul he)

theorem rescaledPopulationDenom_joint_analytic (q : ℕ) (z : ℝ × ℝ) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => rescaledPopulationDenom q u.1) z := by
  exact scaledFalling_joint_analytic q _ _ z analyticAt_const analyticAt_fst

theorem rescaledFactorialMoment_joint_analytic (m q : ℕ) (s : ℝ)
    (z : ℝ × ℝ) (hz : rescaledPopulationDenom q z.1 ≠ 0) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => rescaledFactorialMoment m s q u.1) z := by
  apply AnalyticAt.div _ (rescaledPopulationDenom_joint_analytic q z) hz
  apply AnalyticAt.mul analyticAt_const
  apply scaledFalling_joint_analytic
  · exact (analyticAt_const.sub (analyticAt_const.mul analyticAt_fst)).div_const
  · exact analyticAt_fst

/-- The finite factorial-basis MGF family, jointly in inverse population
and tilt. The next bridge identifies it with the actual hypergeometric MGF. -/
def rescaledMGF (m : ℕ) (s e t : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (m + 1),
    rescaledFactorialMoment m s q e / (Nat.factorial q : ℝ) *
      (Real.exp t - 1) ^ q

@[simp] theorem rescaledMGF_tilt_zero (m : ℕ) (s e : ℝ) :
    rescaledMGF m s e 0 = 1 := by
  unfold rescaledMGF
  simp only [Real.exp_zero, sub_self]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro q hq hq0
    simp [zero_pow hq0]
  · simp

theorem rescaledMGF_joint_analytic (m : ℕ) (s : ℝ) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => rescaledMGF m s u.1 u.2) (0, t) := by
  unfold rescaledMGF
  apply Finset.analyticAt_fun_sum
  intro q hq
  exact ((rescaledFactorialMoment_joint_analytic m q s (0, t) (by simp)).div_const).mul
    ((analyticAt_snd.rexp'.sub analyticAt_const).pow q)

end

end ExactHoeffding
