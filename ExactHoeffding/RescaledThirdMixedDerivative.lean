import ExactHoeffding.RescaledFourthTiltInput

/-! # Actual third mixed derivative needed for the second tilt coefficient -/

namespace ExactHoeffding

noncomputable section

open scoped Topology

private theorem cast_descFactorial_three (m : ℕ) :
    (Nat.descFactorial m 3 : ℝ) = (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) := by
  rw [show 3 = 2 + 1 by rfl, Nat.descFactorial_succ, Nat.cast_mul,
    Nat.cast_descFactorial_two]
  by_cases hm : 2 ≤ m
  · rw [Nat.cast_sub hm]; norm_num; ring
  · interval_cases m <;> norm_num

private theorem cast_descFactorial_four (m : ℕ) :
    (Nat.descFactorial m 4 : ℝ) =
      (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 3) := by
  rw [show 4 = 3 + 1 by rfl, Nat.descFactorial_succ, Nat.cast_mul,
    cast_descFactorial_three]
  by_cases hm : 3 ≤ m
  · rw [Nat.cast_sub hm]; norm_num; ring
  · interval_cases m <;> norm_num

private theorem factorial_two_hasDerivAt (m : ℕ) (s : ℝ) :
    HasDerivAt (rescaledFactorialMoment m s 2)
      (-((2 * s + 1) * (Nat.descFactorial m 2 : ℝ)) / 4) 0 := by
  have hi := hasDerivAt_id (0 : ℝ)
  have ha := ((hi.const_mul s).const_sub 1).div_const 2
  have hb := ha.sub hi
  have h := ((ha.mul hb).const_mul (Nat.descFactorial m 2 : ℝ)).div
    (hi.const_sub 1) (by norm_num)
  have heq : rescaledFactorialMoment m s 2 =
      (fun e : ℝ => (Nat.descFactorial m 2 : ℝ) * ((1 - s * e) / 2 *
        ((1 - s * e) / 2 - e)) / (1 - e)) := by
    funext e
    simp [rescaledFactorialMoment, rescaledPopulationDenom, scaledFalling_succ]
  rw [heq]
  change HasDerivAt (fun e : ℝ => (Nat.descFactorial m 2 : ℝ) *
    ((1 - s * e) / 2 * ((1 - s * e) / 2 - e)) / (1 - e)) _ 0 at h
  apply h.congr_deriv
  norm_num
  ring

private theorem factorial_three_hasDerivAt (m : ℕ) (s : ℝ) :
    HasDerivAt (rescaledFactorialMoment m s 3)
      (-((3 * s + 3) * (Nat.descFactorial m 3 : ℝ)) / 8) 0 := by
  have hi := hasDerivAt_id (0 : ℝ)
  have ha := ((hi.const_mul s).const_sub 1).div_const 2
  have hb := ha.sub hi
  have hc := ha.sub (hi.const_mul 2)
  have h := (((ha.mul hb).mul hc).const_mul (Nat.descFactorial m 3 : ℝ)).div
    ((hi.const_sub 1).mul ((hi.const_mul 2).const_sub 1)) (by norm_num)
  have heq : rescaledFactorialMoment m s 3 =
      (fun e : ℝ => (Nat.descFactorial m 3 : ℝ) * (((1 - s * e) / 2 *
        ((1 - s * e) / 2 - e)) * ((1 - s * e) / 2 - 2 * e)) /
          ((1 - e) * (1 - 2 * e))) := by
    funext e
    simp [rescaledFactorialMoment, rescaledPopulationDenom, scaledFalling_succ, mul_comm]
  rw [heq]
  change HasDerivAt (fun e : ℝ => (Nat.descFactorial m 3 : ℝ) *
    (((1 - s * e) / 2 * ((1 - s * e) / 2 - e)) * ((1 - s * e) / 2 - 2 * e)) /
      ((1 - e) * (1 - 2 * e))) _ 0 at h
  apply h.congr_deriv
  norm_num
  ring

private theorem factorial_four_hasDerivAt (m : ℕ) (s : ℝ) :
    HasDerivAt (rescaledFactorialMoment m s 4)
      (-((4 * s + 6) * (Nat.descFactorial m 4 : ℝ)) / 16) 0 := by
  have hi := hasDerivAt_id (0 : ℝ)
  have ha := ((hi.const_mul s).const_sub 1).div_const 2
  have hb := ha.sub hi
  have hc := ha.sub (hi.const_mul 2)
  have hd := ha.sub (hi.const_mul 3)
  have h := ((((ha.mul hb).mul hc).mul hd).const_mul
    (Nat.descFactorial m 4 : ℝ)).div
    (((hi.const_sub 1).mul ((hi.const_mul 2).const_sub 1)).mul
      ((hi.const_mul 3).const_sub 1)) (by norm_num)
  have heq : rescaledFactorialMoment m s 4 =
      (fun e : ℝ => (Nat.descFactorial m 4 : ℝ) * ((((1 - s * e) / 2 *
        ((1 - s * e) / 2 - e)) * ((1 - s * e) / 2 - 2 * e)) *
          ((1 - s * e) / 2 - 3 * e)) /
          (((1 - e) * (1 - 2 * e)) * (1 - 3 * e))) := by
    funext e
    simp [rescaledFactorialMoment, rescaledPopulationDenom, scaledFalling_succ, mul_comm]
  rw [heq]
  change HasDerivAt (fun e : ℝ => (Nat.descFactorial m 4 : ℝ) *
    ((((1 - s * e) / 2 * ((1 - s * e) / 2 - e)) * ((1 - s * e) / 2 - 2 * e)) *
      ((1 - s * e) / 2 - 3 * e)) / (((1 - e) * (1 - 2 * e)) * (1 - 3 * e))) _ 0 at h
  apply h.congr_deriv
  norm_num
  ring

theorem rescaledFourthCumulantPolynomial_hasDerivAt_zero (m : ℕ) (s : ℝ) :
    HasDerivAt (rescaledFourthCumulantPolynomial m s)
      ((m : ℝ) * ((m : ℝ) - 1) / 2) 0 := by
  have hi := hasDerivAt_id (0 : ℝ)
  have ha := ((hi.const_mul s).const_sub 1).const_mul (m : ℝ) |>.div_const 2
  have hb := factorial_two_hasDerivAt m s
  have hc := factorial_three_hasDerivAt m s
  have hd := factorial_four_hasDerivAt m s
  change HasDerivAt (rescaledMean m s) _ 0 at ha
  have h := ((((((ha.add (hb.const_mul 7)).add (hc.const_mul 6)).add hd).sub
      ((ha.const_mul 4).mul ((ha.add (hb.const_mul 3)).add hc))).sub
      (((ha.add hb).pow 2).const_mul 3)).add
      (((ha.pow 2).const_mul 12).mul (ha.add hb))).sub ((ha.pow 4).const_mul 6)
  change HasDerivAt (rescaledFourthCumulantPolynomial m s) _ 0 at h
  apply h.congr_deriv
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, rescaledMean,
    rescaledFactorialMoment_at_zero, Nat.cast_descFactorial_two,
    cast_descFactorial_three, cast_descFactorial_four]
  norm_num
  ring

/-- One inverse-population derivative of the actual second tilt derivative. -/
theorem rescaledProxyExtension_tilt_deriv2_zero_hasDerivAt (m : ℕ) (s : ℝ) :
    HasDerivAt (fun e => iteratedDeriv 2 (rescaledProxyExtension m s e) 0)
      ((m : ℝ) * ((m : ℝ) - 1) / 12) 0 := by
  have heq : (fun e => iteratedDeriv 2 (rescaledProxyExtension m s e) 0) =
      (fun e => rescaledFourthCumulantPolynomial m s e / 6) :=
    funext (rescaledProxyExtension_deriv2_tilt_zero m s)
  rw [heq]
  apply ((rescaledFourthCumulantPolynomial_hasDerivAt_zero m s).div_const 6).congr_deriv
  ring

end

end ExactHoeffding
