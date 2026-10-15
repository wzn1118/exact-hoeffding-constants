import ExactHoeffding.RealMarginMasses
import ExactHoeffding.RealMarginMoments
import ExactHoeffding.ActualAnalyticAsymptotics

/-! # First population correction of the actual real-margin masses -/

namespace ExactHoeffding
noncomputable section
open Filter
open scoped Topology

/-- Differentiating the finite falling product with respect to its step. -/
theorem scaledFalling_hasDerivAt_step_zero (a : ℝ) (ha : a ≠ 0) (q : ℕ) :
    HasDerivAt (fun e => scaledFalling a e q)
      (-((q : ℝ) * ((q : ℝ) - 1)) / 2 * a ^ q / a) 0 := by
  induction q with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  | succ q ih =>
    have h := ih.mul (((hasDerivAt_id (0 : ℝ)).const_mul (q : ℝ)).const_sub a)
    have hfun : (fun e => scaledFalling a e (q + 1)) =
        (fun e => scaledFalling a e q * (a - (q : ℝ) * e)) := by
      funext e
      exact scaledFalling_succ a e q
    rw [hfun]
    apply h.congr_deriv
    simp only [id_eq, scaledFalling_step_zero, mul_zero, sub_zero, mul_one, Nat.cast_add,
      Nat.cast_one, pow_succ]
    field_simp [ha]
    <;> ring

/-- The binomial mass and its exact finite-population first correction. -/
theorem realMarginMass_hasDerivAt_population_zero (m i : ℕ) (p : ℝ)
    (hp : p ≠ 0) (hq : 1 - p ≠ 0) :
    HasDerivAt (fun e => realMarginMass m e p i)
      (((m.choose i : ℝ) * p ^ i * (1 - p) ^ (m-i)) / 2 *
        ((m : ℝ) * ((m : ℝ) - 1) - (i : ℝ) * ((i : ℝ) - 1) / p -
          ((m-i : ℕ) : ℝ) * (((m-i : ℕ) : ℝ) - 1) / (1-p))) 0 := by
  have h := (((scaledFalling_hasDerivAt_step_zero p hp i).const_mul
    (m.choose i : ℝ)).mul (scaledFalling_hasDerivAt_step_zero (1-p) hq (m-i))).div
      (scaledFalling_hasDerivAt_step_zero 1 (by norm_num) m) (by simp)
  change HasDerivAt (fun e => realMarginMass m e p i) _ 0 at h
  apply h.congr_deriv
  simp only [Pi.mul_apply, scaledFalling_step_zero, one_pow, div_one, one_mul, pow_two]
  field_simp [hp, hq]
  <;> ring

/-- The correction has an analytic second-order remainder for every mass. -/
theorem realMarginMass_first_population_analytic_expansion (m i : ℕ) (p : ℝ)
    (hp : p ≠ 0) (hq : 1-p ≠ 0) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      (∀ e, realMarginMass m e p i = (m.choose i : ℝ)*p^i*(1-p)^(m-i) +
        (((m.choose i : ℝ)*p^i*(1-p)^(m-i))/2 *
          ((m : ℝ)*((m : ℝ)-1) - (i : ℝ)*((i : ℝ)-1)/p -
            ((m-i : ℕ) : ℝ)*(((m-i : ℕ) : ℝ)-1)/(1-p))) * e + e^2*R e) ∧
      (fun e => realMarginMass m e p i - (m.choose i : ℝ)*p^i*(1-p)^(m-i) -
        (((m.choose i : ℝ)*p^i*(1-p)^(m-i))/2 *
          ((m : ℝ)*((m : ℝ)-1) - (i : ℝ)*((i : ℝ)-1)/p -
            ((m-i : ℕ) : ℝ)*(((m-i : ℕ) : ℝ)-1)/(1-p))) * e)
        =O[𝓝 0] (fun e => e^2) := by
  have han : AnalyticAt ℝ (fun e => realMarginMass m e p i) 0 :=
    (realMarginMass_joint_analytic m i (0,p) (by simp)).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  obtain ⟨R, hR, heq, hO⟩ := analytic_linear_remainder _ han
  have hz : realMarginMass m 0 p i = (m.choose i : ℝ)*p^i*(1-p)^(m-i) := by
    simp [realMarginMass]
  have hd := (realMarginMass_hasDerivAt_population_zero m i p hp hq).deriv
  exact ⟨R, hR, by simpa only [hz, hd] using heq,
    by simpa only [hz, hd] using hO⟩

/-- Weighted binomial factorial moments, with a free positive generating weight. -/
theorem binomial_factorial_weight_sum (m r : ℕ) (hr : r ≤ m) (p q z : ℝ) :
    (∑ i ∈ Finset.range (m+1), (Nat.descFactorial i r : ℝ) *
      (m.choose i : ℝ) * p^i * q^(m-i) * z^i) =
        (Nat.descFactorial m r : ℝ)*(p*z)^r*(p*z+q)^(m-r) := by
  have h := realMarginNumerator_factorial m r (p*z) q 0
  simp only [scaledFalling_step_zero, if_pos hr, mul_zero, sub_zero] at h
  calc
    _ = ∑ i ∈ Finset.range (m+1), (Nat.descFactorial i r : ℝ)*
        (m.choose i : ℝ)*(p*z)^i*q^(m-i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_pow]
      ring
    _ = _ := h

/-- The finite generating polynomial of the binomial mass. -/
theorem binomial_mass_weight_sum (m : ℕ) (p q z : ℝ) :
    (∑ i ∈ Finset.range (m+1), (m.choose i : ℝ)*p^i*q^(m-i)*z^i) =
      (q+p*z)^m := by
  simpa only [Nat.descFactorial_zero, Nat.cast_one, one_mul, pow_zero,
    mul_one, Nat.sub_zero, add_comm (p*z) q] using
      binomial_factorial_weight_sum m 0 (by omega) p q z

/-- The reflected second factorial moment in the binomial generating law. -/
theorem binomial_complement_factorial_weight_sum (m : ℕ) (hm : 2 ≤ m) (p q z : ℝ) :
    (∑ i ∈ Finset.range (m+1), (Nat.descFactorial (m-i) 2 : ℝ) *
      (m.choose i : ℝ)*p^i*q^(m-i)*z^i) =
        (m : ℝ)*((m : ℝ)-1)*q^2*(q+p*z)^(m-2) := by
  rw [← Finset.sum_range_reflect (fun i => (Nat.descFactorial (m-i) 2 : ℝ)*
    (m.choose i : ℝ)*p^i*q^(m-i)*z^i) (m+1)]
  have h := realMarginNumerator_factorial m 2 q (p*z) 0
  simp only [scaledFalling_step_zero, if_pos hm, mul_zero, sub_zero,
    Nat.cast_descFactorial_two] at h
  calc
    _ = ∑ i ∈ Finset.range (m+1), (Nat.descFactorial i 2 : ℝ)*
        (m.choose i : ℝ)*q^i*(p*z)^(m-i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [show m+1-1-i=m-i by omega, Nat.sub_sub_self him,
        Nat.choose_symm him, mul_pow]
      ring
    _ = _ := by simpa only [Nat.cast_descFactorial_two] using h

end
end ExactHoeffding
