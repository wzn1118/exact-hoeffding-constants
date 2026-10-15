import ExactHoeffding.FactorialMGFDerivatives

/-! # Population-coordinate derivatives for fourth-order optimization

Exact rational identities for the variance and third cumulant, together
with the fourth-cumulant analytic remainder, determine the mixed jets.
-/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem rescaledFourthCumulantPolynomial_eq_highCumulants (m : ℕ) (s e : ℝ) :
    rescaledFourthCumulantPolynomial m s e = hypergeomRescaledCumulant4 m s e := by
  simp only [rescaledFourthCumulantPolynomial, hypergeomRescaledCumulant4,
    hypergeomRescaledMoment, momentFromFactorials,
    ← rescaledFactorialMoment_eq_highCumulants, rescaledFactorialMoment_degree_one]
  ring

theorem rescaledProxyExtension_tilt_deriv2_zero_deriv2 (m : ℕ) (s : ℝ) :
    iteratedDeriv 2 (fun e => iteratedDeriv 2 (rescaledProxyExtension m s e) 0) 0 =
      (m : ℝ) * (-6 * (m : ℝ) ^ 2 + 19 * (m : ℝ) + 4 * s ^ 2 - 13) / 24 := by
  let R : ℝ → ℝ := fun e => hypergeomCumulant4RemainderFactor m s e / 6
  have hR : AnalyticAt ℝ R 0 := by
    dsimp [R, hypergeomCumulant4RemainderFactor, hypergeomCumulant4RemainderNumerator]
    fun_prop (disch := norm_num)
  have heq : (fun e => iteratedDeriv 2 (rescaledProxyExtension m s e) 0) =ᶠ[𝓝 0]
      (fun e => hypergeomCumulant4Taylor m s e / 6 + e ^ 3 * R e) := by
    have h1 : ∀ᶠ e : ℝ in 𝓝 0, 1 - e ≠ 0 :=
      (continuousAt_const.sub continuousAt_id).eventually_ne (by norm_num)
    have h2 : ∀ᶠ e : ℝ in 𝓝 0, 1 - 2 * e ≠ 0 :=
      (continuousAt_const.sub (continuousAt_id.const_mul 2)).eventually_ne (by norm_num)
    have h3 : ∀ᶠ e : ℝ in 𝓝 0, 1 - 3 * e ≠ 0 :=
      (continuousAt_const.sub (continuousAt_id.const_mul 3)).eventually_ne (by norm_num)
    filter_upwards [h1, h2, h3] with e he1 he2 he3
    rw [rescaledProxyExtension_deriv2_tilt_zero,
      rescaledFourthCumulantPolynomial_eq_highCumulants]
    have h := hypergeom_rescaled_cumulant4_remainder_identity m s e he1 he2 he3
    dsimp [R]
    nlinarith [h]
  have hpoly : (fun e => hypergeomCumulant4Taylor m s e / 6) =
      (fun e : ℝ => -(m : ℝ) / 48 + (m : ℝ) * ((m : ℝ) - 1) / 12 * e +
        (m : ℝ) * (-6 * (m : ℝ) ^ 2 + 19 * (m : ℝ) + 4 * s ^ 2 - 13) / 48 * e ^ 2) := by
    funext e
    unfold hypergeomCumulant4Taylor
    ring
  rw [heq.iteratedDeriv_eq]
  simp_rw [show ∀ e : ℝ, hypergeomCumulant4Taylor m s e / 6 =
    -(m : ℝ) / 48 + (m : ℝ) * ((m : ℝ) - 1) / 12 * e +
      (m : ℝ) * (-6 * (m : ℝ) ^ 2 + 19 * (m : ℝ) + 4 * s ^ 2 - 13) / 48 * e ^ 2
    from fun e => congrFun hpoly e]
  rw [iteratedDeriv_fun_add (by fun_prop)
      (by exact (by fun_prop : AnalyticAt ℝ (fun e : ℝ => e ^ 3 * R e) 0).contDiffAt),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_const, iteratedDeriv_const_mul_field, iteratedDeriv_fun_id,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_fun_mul (by fun_prop) hR.contDiffAt]
  norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, Nat.choose]
  ring

theorem rescaledProxyExtension_tilt_deriv_zero_deriv3 (m : ℕ) (s : ℝ) :
    iteratedDeriv 3 (fun e => deriv (rescaledProxyExtension m s e) 0) 0 =
      (m : ℝ) * s * (2 * (m : ℝ) ^ 2 - 9 * (m : ℝ) - s ^ 2 + 7) / 2 := by
  let H : ℝ → ℝ := fun e => (m : ℝ) * s *
    (2 * (m : ℝ) ^ 2 - 9 * (m : ℝ) - s ^ 2 + 7 +
      (3 * (m : ℝ) * s ^ 2 + 6 * (m : ℝ) - 6) * e -
      2 * (m : ℝ) ^ 2 * s ^ 2 * e ^ 2) / (12 * (1 - e) * (1 - 2 * e))
  have hH : AnalyticAt ℝ H 0 := by dsimp [H]; fun_prop (disch := norm_num)
  have heq : (fun e => deriv (rescaledProxyExtension m s e) 0) =ᶠ[𝓝 0]
      (fun e => (m : ℝ) * s / 12 * e +
        (m : ℝ) * s * (1 - (m : ℝ)) / 4 * e ^ 2 + e ^ 3 * H e) := by
    have h1 : ∀ᶠ e : ℝ in 𝓝 0, 1 - e ≠ 0 :=
      (continuousAt_const.sub continuousAt_id).eventually_ne (by norm_num)
    have h2 : ∀ᶠ e : ℝ in 𝓝 0, 1 - 2 * e ≠ 0 :=
      (continuousAt_const.sub (continuousAt_id.const_mul 2)).eventually_ne (by norm_num)
    filter_upwards [h1, h2] with e he1 he2
    rw [rescaledProxyExtension_deriv_tilt_zero m s e he1 he2]
    dsimp [H]
    field_simp [he1, he2, show 1 - e * 2 ≠ 0 by simpa only [mul_comm] using he2]
    ring
  have hfactor : iteratedDeriv 3 (fun e => e ^ 3 * H e) 0 = 6 * H 0 := by
    rw [iteratedDeriv_fun_mul (by fun_prop) hH.contDiffAt]
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, Nat.choose]
  rw [heq.iteratedDeriv_eq,
    iteratedDeriv_fun_add (by fun_prop)
      (by exact (by fun_prop : AnalyticAt ℝ (fun e : ℝ => e ^ 3 * H e) 0).contDiffAt),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_id,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, hfactor]
  norm_num [H]
  ring

theorem rescaledProxyExtension_zero_tilt_deriv4 (m : ℕ) (s : ℝ) :
    iteratedDeriv 4 (fun e => rescaledProxyExtension m s e 0) 0 =
      6 * (m : ℝ) * (1 - (m : ℝ)) * (1 - s ^ 2) := by
  let H : ℝ → ℝ := fun e =>
    (m : ℝ) * (1 - (m : ℝ)) * (1 - s ^ 2) / (4 * (1 - e))
  have hH : AnalyticAt ℝ H 0 := by dsimp [H]; fun_prop (disch := norm_num)
  have heq : (fun e => rescaledProxyExtension m s e 0) =ᶠ[𝓝 0]
      (fun e => (m : ℝ) / 4 + (m : ℝ) * (1 - (m : ℝ)) / 4 * e +
        (m : ℝ) * (1 - (m : ℝ) - s ^ 2) / 4 * e ^ 2 +
        (m : ℝ) * (1 - (m : ℝ)) * (1 - s ^ 2) / 4 * e ^ 3 + e ^ 4 * H e) := by
    filter_upwards [(continuousAt_const.sub continuousAt_id).eventually_ne
      (by norm_num : (1 : ℝ) - 0 ≠ 0)] with e he
    change 1 - e ≠ 0 at he
    rw [rescaledProxyExtension_zero_tilt_formula m s e he]
    dsimp [H]
    field_simp [he]
    ring
  have hfactor : iteratedDeriv 4 (fun e => e ^ 4 * H e) 0 = 24 * H 0 := by
    rw [iteratedDeriv_fun_mul (by fun_prop) hH.contDiffAt]
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, Nat.choose]
  rw [heq.iteratedDeriv_eq,
    iteratedDeriv_fun_add (by fun_prop)
      (by exact (by fun_prop : AnalyticAt ℝ (fun e : ℝ => e ^ 4 * H e) 0).contDiffAt),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_const, iteratedDeriv_const_mul_field, iteratedDeriv_fun_id,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, hfactor]
  norm_num [H]
  ring

end

end ExactHoeffding
