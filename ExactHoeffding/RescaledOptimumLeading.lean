import ExactHoeffding.AnalyticOptimizerLeading

/-! # The leading normalized optimal-proxy coefficient -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem rescaledProxyExtension_zero_tilt_formula (m : ℕ) (s e : ℝ)
    (he : 1 - e ≠ 0) :
    rescaledProxyExtension m s e 0 =
      (m : ℝ) * (1 - s ^ 2 * e ^ 2) * (1 - (m : ℝ) * e) / (4 * (1 - e)) := by
  rw [rescaledProxyExtension_tilt_zero]
  simp only [rescaledMean, rescaledFactorialMoment, rescaledPopulationDenom,
    scaledFalling_succ, scaledFalling_zero, Nat.cast_descFactorial_two]
  norm_num
  field_simp [he]
  ring

theorem rescaledProxyExtension_zero_tilt_hasDerivAt (m : ℕ) (s : ℝ) :
    HasDerivAt (fun e => rescaledProxyExtension m s e 0)
      ((m : ℝ) * (1 - (m : ℝ)) / 4) 0 := by
  have hi := hasDerivAt_id (0 : ℝ)
  have hd := (((hi.pow 2).const_mul (s ^ 2)).const_sub 1 |>.const_mul (m : ℝ)).mul
    ((hi.const_mul (m : ℝ)).const_sub 1) |>.div
      ((hi.const_sub 1).const_mul 4) (by norm_num : (4 : ℝ) * (1 - 0) ≠ 0)
  have hd' : HasDerivAt (fun e : ℝ =>
      (m : ℝ) * (1 - s ^ 2 * e ^ 2) * (1 - (m : ℝ) * e) / (4 * (1 - e)))
      ((m : ℝ) * (1 - (m : ℝ)) / 4) 0 := by
    apply hd.congr_deriv
    norm_num
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [((continuous_const.sub continuous_id).continuousAt.eventually_ne
    (by norm_num : (1 : ℝ) - 0 ≠ 0))] with e he
  exact rescaledProxyExtension_zero_tilt_formula m s e he

/-- The envelope theorem here is proved by the chain rule at the actual
critical point; no derivative of a supremum is assumed. -/
theorem rescaledProxyExtension_optimized_value_hasDerivAt
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0) :
    HasDerivAt (fun e => rescaledProxyExtension m s e (τ e))
      ((m : ℝ) * (1 - (m : ℝ)) / 4) 0 := by
  let Q : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
  have hQ : AnalyticAt ℝ Q (0, 0) := rescaledProxyExtension_joint_analytic m s
  have hins : HasDerivAt (fun e : ℝ => (e, (0 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 0)
  have hx : fderiv ℝ Q (0, 0) (1, 0) = (m : ℝ) * (1 - (m : ℝ)) / 4 := by
    exact (hQ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hins rfl).deriv.symm.trans
      (rescaledProxyExtension_zero_tilt_hasDerivAt m s).deriv
  have hy : fderiv ℝ Q (0, 0) (0, 1) = 0 := by
    change tiltPartial Q (0, 0) = _
    rw [tiltPartial_eq_deriv Q (0, 0) hQ]
    exact rescaledProxyExtension_limit_deriv_zero m hm s
  have hpath : HasDerivAt (fun e : ℝ => (e, τ e)) (1, deriv τ 0) 0 :=
    (hasDerivAt_id 0).prodMk hτ.differentiableAt.hasDerivAt
  have hd := hQ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath
    (by simp only [hτzero])
  apply hd.congr_deriv
  rw [show ((1, deriv τ 0) : ℝ × ℝ) = (1, 0) + deriv τ 0 • ((0, 1) : ℝ × ℝ) by
    ext <;> simp, map_add, map_smul, hx, hy, smul_eq_mul, mul_zero, add_zero]

theorem rescaledProxyExtension_normalized_optimum_hasDerivAt
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hτzero : τ 0 = 0) :
    HasDerivAt (fun e =>
      4 * rescaledProxyExtension m s e (τ e) / ((m : ℝ) * (1 - (m : ℝ) * e))) 1 0 := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hn := (rescaledProxyExtension_optimized_value_hasDerivAt m hm s τ hτ hτzero).const_mul 4
  have hd := (((hasDerivAt_id (0 : ℝ)).const_mul (m : ℝ)).const_sub 1).const_mul (m : ℝ)
  have hquot := hn.div hd (by simpa only [id_eq, mul_zero, sub_zero, mul_one] using hmR)
  apply hquot.congr_deriv
  rw [hτzero, rescaledProxyExtension_at_zero]
  simp only [id_eq, mul_zero, sub_zero, mul_one]
  field_simp
  ring

end

end ExactHoeffding
