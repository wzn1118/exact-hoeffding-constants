import ExactHoeffding.AnalyticFourthRemainder
import ExactHoeffding.HighCumulants

/-! # Logarithmic derivative recursion for a normalized analytic function

The identity `f' = f (log f)'` gives the moment--cumulant recurrence and
the fifth and sixth logarithmic derivatives of an actual analytic MGF.
-/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem analytic_log_derivative_recursion (f : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) (hf0 : f 0 = 1) (n : ℕ) :
    iteratedDeriv (n + 1) f 0 =
      ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℝ) * iteratedDeriv j f 0 *
        iteratedDeriv (n - j + 1) (fun t => Real.log (f t)) 0 := by
  let L : ℝ → ℝ := fun t => Real.log (f t)
  have hfne : f 0 ≠ 0 := by rw [hf0]; norm_num
  have hL : AnalyticAt ℝ L 0 := hf.log (by rw [hf0]; norm_num)
  have heq : deriv f =ᶠ[𝓝 0] (fun t => f t * deriv L t) := by
    filter_upwards [hf.eventually_analyticAt, hf.continuousAt.eventually_ne hfne]
      with t ht hne
    have h := ht.differentiableAt.hasDerivAt.log hne
    change HasDerivAt L _ t at h
    rw [h.deriv]
    field_simp
  rw [iteratedDeriv_succ', heq.iteratedDeriv_eq,
    iteratedDeriv_fun_mul hf.contDiffAt hL.deriv.contDiffAt]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← iteratedDeriv_succ']

theorem analytic_log_deriv5_polynomial (f : ℝ → ℝ)
    (hf : AnalyticAt ℝ f 0) (hf0 : f 0 = 1) :
    iteratedDeriv 5 (fun t => Real.log (f t)) 0 =
      cumulant5Polynomial (iteratedDeriv 1 f 0) (iteratedDeriv 2 f 0)
        (iteratedDeriv 3 f 0) (iteratedDeriv 4 f 0) (iteratedDeriv 5 f 0) := by
  let L : ℝ → ℝ := fun t => Real.log (f t)
  have h0 := analytic_log_derivative_recursion f hf hf0 0
  have h1 := analytic_log_derivative_recursion f hf hf0 1
  have h2 := analytic_log_derivative_recursion f hf hf0 2
  have h3 := analytic_log_derivative_recursion f hf hf0 3
  have h4 := analytic_log_derivative_recursion f hf hf0 4
  norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_zero, hf0] at h0 h1 h2 h3 h4
  have hk1 : deriv L 0 = deriv f 0 := h0.symm
  change iteratedDeriv 2 f 0 = iteratedDeriv 2 L 0 + deriv f 0 * deriv L 0 at h1
  change iteratedDeriv 3 f 0 = iteratedDeriv 3 L 0 +
    2 * deriv f 0 * iteratedDeriv 2 L 0 + iteratedDeriv 2 f 0 * deriv L 0 at h2
  change iteratedDeriv 4 f 0 = iteratedDeriv 4 L 0 +
    3 * deriv f 0 * iteratedDeriv 3 L 0 + 3 * iteratedDeriv 2 f 0 * iteratedDeriv 2 L 0 +
      iteratedDeriv 3 f 0 * deriv L 0 at h3
  change iteratedDeriv 5 f 0 = iteratedDeriv 5 L 0 +
    4 * deriv f 0 * iteratedDeriv 4 L 0 + 6 * iteratedDeriv 2 f 0 * iteratedDeriv 3 L 0 +
      4 * iteratedDeriv 3 f 0 * iteratedDeriv 2 L 0 + iteratedDeriv 4 f 0 * deriv L 0 at h4
  rw [hk1] at h1 h2 h3 h4
  have hk2 : iteratedDeriv 2 L 0 = iteratedDeriv 2 f 0 - deriv f 0 ^ 2 := by
    nlinarith
  have hk3 : iteratedDeriv 3 L 0 = iteratedDeriv 3 f 0 -
      3 * iteratedDeriv 2 f 0 * deriv f 0 + 2 * deriv f 0 ^ 3 := by
    rw [hk2] at h2
    nlinarith [h2]
  have hk4 : iteratedDeriv 4 L 0 = iteratedDeriv 4 f 0 -
      4 * iteratedDeriv 3 f 0 * deriv f 0 - 3 * iteratedDeriv 2 f 0 ^ 2 +
      12 * iteratedDeriv 2 f 0 * deriv f 0 ^ 2 - 6 * deriv f 0 ^ 4 := by
    rw [hk2, hk3] at h3
    nlinarith [h3]
  rw [hk2, hk3, hk4] at h4
  rw [iteratedDeriv_one]
  dsimp [cumulant5Polynomial]
  nlinarith [h4]

end

end ExactHoeffding
