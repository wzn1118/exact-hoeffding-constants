import ExactHoeffding.PiecewiseKLFull
import ExactHoeffding.AnalyticLogCumulantRecursion

/-! # The scaled Bernoulli KL rate near its target mean

The expansion is in the threshold displacement, not in the exponential
argument of an MGF.  Its fifth-order remainder is analytic at zero.
-/

namespace ExactHoeffding
noncomputable section
open Filter Asymptotics
open scoped Topology

private theorem affine_log_jets (b : ℝ) :
    let L := fun x : ℝ => Real.log (1 + b * x)
    AnalyticAt ℝ L 0 ∧ L 0 = 0 ∧ deriv L 0 = b ∧
      iteratedDeriv 2 L 0 = -b ^ 2 ∧ iteratedDeriv 3 L 0 = 2 * b ^ 3 ∧
      iteratedDeriv 4 L 0 = -6 * b ^ 4 := by
  let A := fun x : ℝ => 1 + b * x
  let L := fun x : ℝ => Real.log (A x)
  have hA : AnalyticAt ℝ A 0 := by dsimp [A]; fun_prop
  have hA0 : A 0 = 1 := by simp [A]
  have hL : AnalyticAt ℝ L 0 := hA.log (by simp [A])
  have h1 : deriv A 0 = b := by
    have hd := (hasDerivAt_const (0:ℝ) 1).add ((hasDerivAt_id (0:ℝ)).const_mul b)
    simpa [A] using hd.deriv
  have hn (n : ℕ) (hn : 2 ≤ n) : iteratedDeriv n A 0 = 0 := by
    dsimp [A]
    rw [iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_id]
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega]
  have r0 := analytic_log_derivative_recursion A hA hA0 0
  have r1 := analytic_log_derivative_recursion A hA hA0 1
  have r2 := analytic_log_derivative_recursion A hA hA0 2
  have r3 := analytic_log_derivative_recursion A hA hA0 3
  norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_zero, iteratedDeriv_one,
    hA0, h1, hn 2 (by omega), hn 3 (by omega), hn 4 (by omega)] at r0 r1 r2 r3
  change AnalyticAt ℝ L 0 ∧ L 0 = 0 ∧ deriv L 0 = b ∧
      iteratedDeriv 2 L 0 = -b ^ 2 ∧ iteratedDeriv 3 L 0 = 2 * b ^ 3 ∧
      iteratedDeriv 4 L 0 = -6 * b ^ 4
  have d1 : deriv L 0 = b := r0.symm
  have d2 : iteratedDeriv 2 L 0 = -b ^ 2 := by
    change 0 = iteratedDeriv 2 L 0 + b * deriv L 0 at r1
    rw [d1] at r1
    nlinarith [r1]
  have d3 : iteratedDeriv 3 L 0 = 2 * b ^ 3 := by
    change 0 = _ at r2
    change 0 = iteratedDeriv 3 L 0 + 2 * b * iteratedDeriv 2 L 0 at r2
    rw [d2] at r2
    nlinarith [r2]
  have d4 : iteratedDeriv 4 L 0 = -6 * b ^ 4 := by
    change 0 = iteratedDeriv 4 L 0 + 3 * b * iteratedDeriv 3 L 0 at r3
    rw [d3] at r3
    nlinarith [r3]
  exact ⟨hL, by simp [L, A], d1, d2, d3, d4⟩

private theorem affine_entropy_jets (r c : ℝ) (hr : r ≠ 0) :
    let F := fun x : ℝ => (r + c * x) * Real.log (1 + (c / r) * x)
    AnalyticAt ℝ F 0 ∧ F 0 = 0 ∧ deriv F 0 = c ∧
      iteratedDeriv 2 F 0 = c ^ 2 / r ∧
      iteratedDeriv 3 F 0 = -c ^ 3 / r ^ 2 ∧
      iteratedDeriv 4 F 0 = 2 * c ^ 4 / r ^ 3 := by
  let A := fun x : ℝ => r + c * x
  let L := fun x : ℝ => Real.log (1 + (c / r) * x)
  obtain ⟨hL, hL0, hL1, hL2, hL3, hL4⟩ := affine_log_jets (c/r)
  have hA : AnalyticAt ℝ A 0 := by dsimp [A]; fun_prop
  have hA0 : A 0 = r := by simp [A]
  have hA1 : deriv A 0 = c := by
    have hd := (hasDerivAt_const (0:ℝ) r).add ((hasDerivAt_id (0:ℝ)).const_mul c)
    simpa [A] using hd.deriv
  have hAn (n : ℕ) (hn : 2 ≤ n) : iteratedDeriv n A 0 = 0 := by
    dsimp [A]
    rw [iteratedDeriv_const_add (by omega), iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_id]
    simp [show n ≠ 0 by omega, show n ≠ 1 by omega]
  refine ⟨hA.mul hL, by simp, ?_, ?_, ?_, ?_⟩
  · rw [show (fun x : ℝ => (r+c*x)*Real.log (1+(c/r)*x)) =
        (fun x => A x * L x) by rfl]
    rw [← iteratedDeriv_one, iteratedDeriv_fun_mul hA.contDiffAt hL.contDiffAt]
    norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_zero, iteratedDeriv_one,
      hA0, hA1, hL0, hL1]
    field_simp [hr]
  · rw [iteratedDeriv_fun_mul hA.contDiffAt hL.contDiffAt]
    norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_zero, iteratedDeriv_one,
      hA0, hA1, hAn 2 (by omega), hL0, hL1, hL2]
    field_simp [hr]
    <;> ring
  · rw [iteratedDeriv_fun_mul hA.contDiffAt hL.contDiffAt]
    norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_zero, iteratedDeriv_one,
      hA0, hA1, hAn 2 (by omega), hAn 3 (by omega), hL0, hL1, hL2, hL3]
    field_simp [hr]
    <;> ring
  · rw [iteratedDeriv_fun_mul hA.contDiffAt hL.contDiffAt]
    norm_num [Finset.sum_range_succ, Nat.choose, iteratedDeriv_zero, iteratedDeriv_one,
      hA0, hA1, hAn 2 (by omega), hAn 3 (by omega), hAn 4 (by omega),
      hL0, hL1, hL2, hL3, hL4]
    field_simp [hr]
    <;> ring

/-- Derivatives through order four of the actual scaled KL target-mean rate. -/
theorem scaledKLRate_target_mean_jets (M p a μ : ℝ)
    (hM : 0 < M) (hp : 0 < p) (hp1 : p < 1) (ha : 0 < a) :
    let F := fun x : ℝ => scaledKLRate M p a μ (μ + x)
    AnalyticAt ℝ F 0 ∧ F 0 = 0 ∧ deriv F 0 = 0 ∧
      iteratedDeriv 2 F 0 = 1 / (M*p*(1-p)) ∧
      iteratedDeriv 3 F 0 = -a*(1-2*p)/(M^2*p^2*(1-p)^2) ∧
      iteratedDeriv 4 F 0 = 2*a^2*(p^3+(1-p)^3)/(M^3*p^3*(1-p)^3) := by
  let c := a / M
  let U := fun x : ℝ => (p+c*x)*Real.log (1+(c/p)*x)
  let V := fun x : ℝ => ((1-p)+(-c)*x)*Real.log (1+((-c)/(1-p))*x)
  obtain ⟨hU, hU0, hU1, hU2, hU3, hU4⟩ := affine_entropy_jets p c hp.ne'
  obtain ⟨hV, hV0, hV1, hV2, hV3, hV4⟩ := affine_entropy_jets (1-p) (-c)
    (sub_pos.mpr hp1).ne'
  have heq : (fun x : ℝ => scaledKLRate M p a μ (μ+x)) =
      (fun x => M/a^2*(U x+V x)) := by
    funext x
    unfold scaledKLRate bernoulliKL
    dsimp [U,V,c]
    congr 1
    congr 1
    · congr 1
      · ring
      · congr 1
        field_simp [hp.ne', hM.ne']
        <;> ring
    · congr 1
      · ring
      · congr 1
        field_simp [hp.ne', hM.ne', (sub_pos.mpr hp1).ne']
        <;> ring
  rw [heq]
  refine ⟨analyticAt_const.mul (hU.add hV), ?_, ?_, ?_, ?_, ?_⟩
  · simp [U, V]
  · rw [← iteratedDeriv_one, iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_add hU.contDiffAt hV.contDiffAt]
    simp only [iteratedDeriv_one, hU1, hV1]
    ring
  · rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_add hU.contDiffAt hV.contDiffAt,
      hU2, hV2]
    dsimp [c]
    field_simp [hM.ne', hp.ne', ha.ne', (sub_pos.mpr hp1).ne']
    <;> ring
  · rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_add hU.contDiffAt hV.contDiffAt,
      hU3, hV3]
    dsimp [c]
    field_simp [hM.ne', hp.ne', ha.ne', (sub_pos.mpr hp1).ne']
    <;> ring
  · rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_add hU.contDiffAt hV.contDiffAt,
      hU4, hV4]
    dsimp [c]
    field_simp [hM.ne', hp.ne', ha.ne', (sub_pos.mpr hp1).ne']
    <;> ring

/-- The scaled relative-entropy rate has the exact target-mean quartic
expansion, with an analytic fifth-order remainder and a two-sided Big-O. -/
theorem scaledKLRate_target_mean_quartic_expansion (M p a μ : ℝ)
    (hM : 0 < M) (hp : 0 < p) (hp1 : p < 1) (ha : 0 < a) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      (∀ x : ℝ, scaledKLRate M p a μ (μ+x) =
        x^2/(2*M*p*(1-p)) - a*(1-2*p)*x^3/(6*M^2*p^2*(1-p)^2) +
        a^2*(p^3+(1-p)^3)*x^4/(12*M^3*p^3*(1-p)^3) + x^5*R x) ∧
      (fun x : ℝ => scaledKLRate M p a μ (μ+x) -
        (x^2/(2*M*p*(1-p)) - a*(1-2*p)*x^3/(6*M^2*p^2*(1-p)^2) +
          a^2*(p^3+(1-p)^3)*x^4/(12*M^3*p^3*(1-p)^3)))
        =O[𝓝 0] (fun x : ℝ => x^5) := by
  obtain ⟨hF, h0, h1, h2, h3, h4⟩ := scaledKLRate_target_mean_jets M p a μ hM hp hp1 ha
  obtain ⟨R, hR, hReq, hO⟩ := analytic_quartic_remainder
    (fun x : ℝ => scaledKLRate M p a μ (μ+x)) hF
  simp only [h0, h1, h2, h3, h4, zero_mul, zero_add] at hReq hO
  refine ⟨R, hR, ?_, ?_⟩
  · intro x
    rw [hReq x]
    field_simp [hM.ne', hp.ne', (sub_pos.mpr hp1).ne']
    <;> ring
  · convert hO using 1 <;> ext x <;>
      field_simp [hM.ne', hp.ne', (sub_pos.mpr hp1).ne'] <;> ring

end
end ExactHoeffding
