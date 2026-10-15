import ExactHoeffding.AnalyticLogCumulantRecursion
import Mathlib.Combinatorics.Enumerative.Stirling

/-! # Actual factorial-basis MGF derivatives and Stirling coefficients -/

namespace ExactHoeffding

noncomputable section

open scoped Topology

private theorem exp_sub_one_power_deriv (q : ℕ) :
    deriv (fun t : ℝ => (Real.exp t - 1) ^ (q + 1)) =
      (fun t => ((q + 1 : ℕ) : ℝ) *
        ((Real.exp t - 1) ^ (q + 1) + (Real.exp t - 1) ^ q)) := by
  funext t
  have h := ((Real.hasDerivAt_exp t).sub_const 1).pow (q + 1)
  change HasDerivAt (fun t : ℝ => (Real.exp t - 1) ^ (q + 1)) _ t at h
  rw [h.deriv]
  simp only [Nat.add_sub_cancel]
  rw [pow_succ]
  ring

theorem exp_sub_one_power_iteratedDeriv_zero (r q : ℕ) :
    iteratedDeriv r (fun t : ℝ => (Real.exp t - 1) ^ q) 0 =
      (q.factorial : ℝ) * (Nat.stirlingSecond r q : ℝ) := by
  induction r generalizing q with
  | zero =>
      cases q <;> simp [iteratedDeriv_zero]
  | succ r ih =>
      cases q with
      | zero => simp [iteratedDeriv_const]
      | succ q =>
          rw [iteratedDeriv_succ', exp_sub_one_power_deriv,
            iteratedDeriv_const_mul_field,
            iteratedDeriv_fun_add (by fun_prop) (by fun_prop), ih, ih,
            Nat.stirlingSecond_succ_succ, Nat.factorial_succ]
          push_cast
          ring

theorem rescaledFactorialMoment_eq_highCumulants (m q : ℕ) (s e : ℝ) :
    rescaledFactorialMoment m s q e = hypergeomRescaledFactorial m q s e := by
  simp only [rescaledFactorialMoment, rescaledPopulationDenom, scaledFalling,
    hypergeomRescaledFactorial, Finset.prod_div_distrib]
  ring

theorem rescaledMGF_iteratedDeriv_zero (m r : ℕ) (s e : ℝ) :
    iteratedDeriv r (rescaledMGF m s e) 0 =
      ∑ q ∈ Finset.range (r + 1),
        rescaledFactorialMoment m s q e * (Nat.stirlingSecond r q : ℝ) := by
  unfold rescaledMGF
  rw [iteratedDeriv_fun_sum (by intro q hq; fun_prop)]
  simp_rw [iteratedDeriv_const_mul_field, exp_sub_one_power_iteratedDeriv_zero]
  have hterm (q : ℕ) : rescaledFactorialMoment m s q e / (q.factorial : ℝ) *
      ((q.factorial : ℝ) * (Nat.stirlingSecond r q : ℝ)) =
      rescaledFactorialMoment m s q e * (Nat.stirlingSecond r q : ℝ) := by
    have hne : (q.factorial : ℝ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
    field_simp
  simp_rw [hterm]
  let f : ℕ → ℝ := fun q =>
    rescaledFactorialMoment m s q e * (Nat.stirlingSecond r q : ℝ)
  have hm : (∑ q ∈ Finset.range (m + 1), f q) =
      ∑ q ∈ Finset.range (m + r + 1), f q := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro q hq hn
    have hmq : m < q := by
      simp only [Finset.mem_range] at hn
      omega
    simp [f, rescaledFactorialMoment_eq_zero_of_lt m q s e hmq]
  have hr : (∑ q ∈ Finset.range (r + 1), f q) =
      ∑ q ∈ Finset.range (m + r + 1), f q := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro q hq hn
    have hrq : r < q := by
      simp only [Finset.mem_range] at hn
      omega
    simp [f, Nat.stirlingSecond_eq_zero_of_lt hrq]
  exact hm.trans hr.symm

theorem rescaledMGF_iteratedDeriv_zero_through_six (m r : ℕ) (s e : ℝ)
    (hr : r ≤ 6) :
    iteratedDeriv r (rescaledMGF m s e) 0 = hypergeomRescaledMoment m r s e := by
  rw [rescaledMGF_iteratedDeriv_zero]
  simp_rw [rescaledFactorialMoment_eq_highCumulants]
  interval_cases r <;> norm_num [Finset.sum_range_succ, Nat.stirlingSecond,
    hypergeomRescaledMoment, momentFromFactorials] <;> ring

end

end ExactHoeffding
