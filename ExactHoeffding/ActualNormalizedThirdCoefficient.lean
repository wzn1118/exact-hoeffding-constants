import ExactHoeffding.RescaledOptimumThird

/-! # Actual normalized optimum through third inverse-population order

This proves the cubic coefficient and an analytic `e^4` remainder. It does
not assert the fourth coefficient or an `O(e^5)` remainder.
-/

namespace ExactHoeffding

noncomputable section

open Filter Asymptotics
open scoped Topology

private theorem iteratedDeriv3_mul_affine (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0)
    (a b : ℝ) :
    iteratedDeriv 3 (fun e => f e * (a + b * e)) 0 =
      a * iteratedDeriv 3 f 0 + 3 * b * iteratedDeriv 2 f 0 := by
  have heq : (fun e => f e * (a + b * e)) =
      (fun e => a * f e + b * (e * f e)) := by funext e; ring
  rw [heq, iteratedDeriv_fun_add
    (f := fun e : ℝ => a * f e) (g := fun e : ℝ => b * (e * f e))
    (analyticAt_const.mul hf).contDiffAt
    (analyticAt_const.mul (analyticAt_id.mul hf)).contDiffAt,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul (by fun_prop) hf.contDiffAt]
  norm_num [Finset.sum_range_succ, iteratedDeriv_fun_id, Nat.choose]
  ring

theorem rescaledProxyExtension_normalized_optimum_deriv3
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hz : τ 0 = 0)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) :
    iteratedDeriv 3 (fun e => 4 * rescaledProxyExtension m s e (τ e) /
      ((m : ℝ) * (1 - (m : ℝ) * e))) 0 =
        6 * (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) := by
  let V : ℝ → ℝ := fun e => rescaledProxyExtension m s e (τ e)
  let R : ℝ → ℝ := fun e => 4 * V e / ((m : ℝ) * (1 - (m : ℝ) * e))
  have hR : AnalyticAt ℝ R 0 :=
    rescaledProxyExtension_normalized_optimum_analytic m hm s τ hτ hz
  have hdτ := rescaledProxyExtension_critical_branch_hasDerivAt m hm s τ hτ hz heq
  have hR2 : iteratedDeriv 2 R 0 = 2 * (1 - s ^ 2 / 3) :=
    rescaledProxyExtension_normalized_optimum_deriv2 m hm s τ hτ hz hdτ.deriv
  have hV3 : iteratedDeriv 3 V 0 =
      (m : ℝ) * (1 - (m : ℝ)) * (3 + s ^ 2) / 2 :=
    rescaledProxyExtension_optimized_value_deriv3 m hm s τ hτ hz heq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heqR : (fun e => R e * ((m : ℝ) + (-(m : ℝ) ^ 2) * e)) =ᶠ[𝓝 0]
      (fun e => 4 * V e) := by
    have hne : ∀ᶠ e in 𝓝 (0 : ℝ), (m : ℝ) * (1 - (m : ℝ) * e) ≠ 0 :=
      (continuous_const.mul (continuous_const.sub
        (continuous_const.mul continuous_id))).continuousAt.eventually_ne
          (by simpa using hmR.ne')
    filter_upwards [hne] with e he
    change (m : ℝ) * (1 - (m : ℝ) * e) ≠ 0 at he
    dsimp [R]
    rw [show (m : ℝ) + (-(m : ℝ) ^ 2) * e =
      (m : ℝ) * (1 - (m : ℝ) * e) by ring]
    exact div_mul_cancel₀ _ he
  have h3 := heqR.iteratedDeriv_eq 3
  rw [iteratedDeriv3_mul_affine R hR, iteratedDeriv_const_mul_field,
    hR2, hV3] at h3
  change iteratedDeriv 3 R 0 = _
  nlinarith

theorem analytic_cubic_remainder (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      (∀ e : ℝ, f e = f 0 + deriv f 0 * e + iteratedDeriv 2 f 0 / 2 * e ^ 2 +
        iteratedDeriv 3 f 0 / 6 * e ^ 3 + e ^ 4 * R e) ∧
      (fun e => f e - f 0 - deriv f 0 * e - iteratedDeriv 2 f 0 / 2 * e ^ 2 -
        iteratedDeriv 3 f 0 / 6 * e ^ 3) =O[𝓝 0] (fun e => e ^ 4) := by
  obtain ⟨T, hT, hTeq, _⟩ := analytic_quadratic_remainder f hf
  have hfun : f = (fun e => f 0 + deriv f 0 * e + iteratedDeriv 2 f 0 / 2 * e ^ 2 +
      e ^ 3 * T e) := funext hTeq
  have hfactor : iteratedDeriv 3 (fun e => e ^ 3 * T e) 0 = 6 * T 0 := by
    rw [iteratedDeriv_fun_mul (by fun_prop) hT.contDiffAt]
    norm_num [Finset.sum_range_succ, iteratedDeriv_fun_pow_zero, Nat.choose]
  have h3 := congrArg (fun g : ℝ → ℝ => iteratedDeriv 3 g 0) hfun
  rw [iteratedDeriv_fun_add
    (f := fun e : ℝ => f 0 + deriv f 0 * e + iteratedDeriv 2 f 0 / 2 * e ^ 2)
    (g := fun e : ℝ => e ^ 3 * T e) (by fun_prop)
    (by exact (by fun_prop : AnalyticAt ℝ (fun e : ℝ => e ^ 3 * T e) 0).contDiffAt),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_add (by fun_prop) (by fun_prop),
    iteratedDeriv_const, iteratedDeriv_const_mul_field, iteratedDeriv_fun_id,
    iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero, hfactor] at h3
  norm_num at h3
  have hT0 : T 0 = iteratedDeriv 3 f 0 / 6 := by linarith
  let R := dslope T 0
  have hR : AnalyticAt ℝ R 0 := analyticAt_dslope_zero hT
  have hReq (e : ℝ) : f e = f 0 + deriv f 0 * e + iteratedDeriv 2 f 0 / 2 * e ^ 2 +
      iteratedDeriv 3 f 0 / 6 * e ^ 3 + e ^ 4 * R e := by
    have hs := sub_smul_dslope T 0 e
    simp only [sub_zero, smul_eq_mul, hT0] at hs
    rw [hTeq e]
    dsimp [R]
    nlinarith [congrArg (fun x : ℝ => e ^ 3 * x) hs]
  refine ⟨R, hR, hReq, ?_⟩
  have hbounded : R =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := hR.continuousAt.isBigO_one ℝ
  have hb := (isBigO_refl (fun e : ℝ => e ^ 4) (𝓝 0)).mul hbounded
  have heq : (fun e => f e - f 0 - deriv f 0 * e - iteratedDeriv 2 f 0 / 2 * e ^ 2 -
      iteratedDeriv 3 f 0 / 6 * e ^ 3) = (fun e => e ^ 4 * R e) := by
    funext e
    rw [hReq e]
    ring
  rw [heq]
  simpa only [mul_one] using hb

/-- The cubic normalized coefficient belongs to the actual unique global
optimizer, not merely an arbitrary analytic test tilt. -/
theorem actualHypergeomProxy_optimum_third_analytic_expansion
    (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ τ U : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ AnalyticAt ℝ U 0 ∧
      τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ e, 4 * rescaledProxyExtension m s e (τ e) /
        ((m : ℝ) * (1 - (m : ℝ) * e)) =
          1 + e + (1 - s ^ 2 / 3) * e ^ 2 +
            (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) * e ^ 3 + e ^ 4 * U e) ∧
      (fun e => 4 * rescaledProxyExtension m s e (τ e) /
        ((m : ℝ) * (1 - (m : ℝ) * e)) - 1 - e - (1 - s ^ 2 / 3) * e ^ 2 -
          (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) * e ^ 3)
        =O[𝓝 0] (fun e => e ^ 4) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
        2 * (k : ℝ) + s = (N : ℝ) → ∀ t : ℝ,
        (∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) ↔
          t = τ e) := by
  obtain ⟨τ, hτ, hz, hd, heq⟩ :=
    rescaledProxyExtension_analytic_critical_branch_leading m hm s
  let R : ℝ → ℝ := fun e => 4 * rescaledProxyExtension m s e (τ e) /
    ((m : ℝ) * (1 - (m : ℝ) * e))
  have hR := rescaledProxyExtension_normalized_optimum_analytic m hm s τ hτ hz
  have hR0 : R 0 = 1 := rescaledProxyExtension_normalized_optimum_zero m hm s τ hz
  have hR1 : deriv R 0 = 1 :=
    (rescaledProxyExtension_normalized_optimum_hasDerivAt m hm s τ hτ hz).deriv
  have hR2 : iteratedDeriv 2 R 0 / 2 = 1 - s ^ 2 / 3 := by
    rw [rescaledProxyExtension_normalized_optimum_deriv2 m hm s τ hτ hz hd.deriv]
    ring
  have hR3 : iteratedDeriv 3 R 0 / 6 = 1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3 := by
    rw [rescaledProxyExtension_normalized_optimum_deriv3 m hm s τ hτ hz heq]
    ring
  obtain ⟨U, hU, hUeq, hUO⟩ := analytic_cubic_remainder R hR
  refine ⟨τ, U, hτ, hU, hz, hd, ?_, ?_,
    actualHypergeomProxy_critical_branch_is_global m hm s τ heq⟩
  · simpa only [hR0, hR1, hR2, hR3, one_mul] using hUeq
  · simpa only [hR0, hR1, hR2, hR3, one_mul] using hUO

end

end ExactHoeffding
