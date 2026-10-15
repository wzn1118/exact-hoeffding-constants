import ExactHoeffding.ActualTiltThirdCoefficient
import ExactHoeffding.AnalyticStationaryFourthDerivative

/-! # Fourth coefficient and analytic fifth-order remainder of the actual optimum

For fixed sample size and imbalance, the analytic stationary branch is
the unique global optimizer of every sufficiently large admissible law.
The normalization is by `m * (1 - m * e) / 4`.
-/

namespace ExactHoeffding

noncomputable section

open Filter Asymptotics
open scoped Topology

theorem rescaledProxyExtension_optimized_value_deriv4
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hz : τ 0 = 0)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) :
    iteratedDeriv 4 (fun e => rescaledProxyExtension m s e (τ e)) 0 =
      6 * (m : ℝ) * (1 - (m : ℝ) -
        (2 * (m : ℝ) ^ 2 - (m : ℝ) - 1) * s ^ 2 / 3 - 4 * s ^ 4 / 45) := by
  let Q : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
  have hQ : AnalyticAt ℝ Q (0, 0) := rescaledProxyExtension_joint_analytic m s
  obtain ⟨h40, h31, h22, h13, _⟩ := rescaledProxyExtension_coordinate_jet4 m hm s
  have h21 : populationPartial (populationPartial (tiltPartial Q)) (0, 0) =
      (m : ℝ) * s * (1 - (m : ℝ)) / 2 := by
    change ((populationPartial^[2]) ((tiltPartial^[1]) Q)) (0, 0) = _
    rw [analytic_mixed_coordinate_jets 2 1 Q hQ]
    simpa only [iteratedDeriv_one] using rescaledProxyExtension_tilt_deriv_zero_deriv2 m s
  have h12 : populationPartial (tiltPartial (tiltPartial Q)) (0, 0) =
      (m : ℝ) * ((m : ℝ) - 1) / 12 := by
    change ((populationPartial^[1]) ((tiltPartial^[2]) Q)) (0, 0) = _
    rw [analytic_mixed_coordinate_jets 1 2 Q hQ, iteratedDeriv_one]
    exact (rescaledProxyExtension_tilt_deriv2_zero_hasDerivAt m s).deriv
  have h11 : populationPartial (tiltPartial Q) (0, 0) = (m : ℝ) * s / 12 := by
    change ((populationPartial^[1]) ((tiltPartial^[1]) Q)) (0, 0) = _
    rw [analytic_mixed_coordinate_jets 1 1 Q hQ]
    simpa only [iteratedDeriv_one] using (rescaledProxyExtension_mixed_hasDerivAt m s).deriv
  have hpath : Tendsto (fun e : ℝ => (e, τ e)) (𝓝 0) (𝓝 (0, 0)) := by
    simpa only [ContinuousAt, hz, id_eq] using (continuousAt_id.prodMk hτ.continuousAt)
  have hcritical : (fun e => tiltPartial Q (e, τ e)) =ᶠ[𝓝 0] (fun _ => 0) := by
    filter_upwards [hpath.eventually heq, hpath.eventually hQ.eventually_analyticAt]
      with e he ha
    rw [tiltPartial_eq_deriv Q (e, τ e) ha]
    exact he.mpr rfl
  rw [analytic_stationary_value_deriv4 Q τ hQ hτ hz hcritical,
    h40, h31, h22, h13, h21, h12, h11,
    (rescaledProxyExtension_critical_branch_hasDerivAt m hm s τ hτ hz heq).deriv,
    rescaledProxyExtension_critical_branch_deriv2 m hm s τ hτ hz heq,
    rescaledProxyExtension_critical_branch_deriv3 m hm s τ hτ hz heq]
  ring

private theorem iteratedDeriv4_mul_affine (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0)
    (a b : ℝ) :
    iteratedDeriv 4 (fun e => f e * (a + b * e)) 0 =
      a * iteratedDeriv 4 f 0 + 4 * b * iteratedDeriv 3 f 0 := by
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

theorem rescaledProxyExtension_normalized_optimum_deriv4
    (m : ℕ) (hm : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (hτ : AnalyticAt ℝ τ 0) (hz : τ 0 = 0)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) :
    iteratedDeriv 4 (fun e => 4 * rescaledProxyExtension m s e (τ e) /
      ((m : ℝ) * (1 - (m : ℝ) * e))) 0 =
        24 * (1 - (4 * (m : ℝ) ^ 2 - 2 * (m : ℝ) - 1) * s ^ 2 / 3 -
          4 * s ^ 4 / 45) := by
  let V : ℝ → ℝ := fun e => rescaledProxyExtension m s e (τ e)
  let R : ℝ → ℝ := fun e => 4 * V e / ((m : ℝ) * (1 - (m : ℝ) * e))
  have hR : AnalyticAt ℝ R 0 :=
    rescaledProxyExtension_normalized_optimum_analytic m hm s τ hτ hz
  have hR3 : iteratedDeriv 3 R 0 = 6 * (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) :=
    rescaledProxyExtension_normalized_optimum_deriv3 m hm s τ hτ hz heq
  have hV4 := rescaledProxyExtension_optimized_value_deriv4 m hm s τ hτ hz heq
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
  have h4 := heqR.iteratedDeriv_eq 4
  rw [iteratedDeriv4_mul_affine R hR, iteratedDeriv_const_mul_field, hR3, hV4] at h4
  change iteratedDeriv 4 R 0 = _
  nlinarith [h4]

theorem actualHypergeomProxy_optimum_fourth_analytic_expansion
    (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ τ U : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ AnalyticAt ℝ U 0 ∧
      τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ e, 4 * rescaledProxyExtension m s e (τ e) /
        ((m : ℝ) * (1 - (m : ℝ) * e)) =
          1 + e + (1 - s ^ 2 / 3) * e ^ 2 +
          (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) * e ^ 3 +
          (1 - (4 * (m : ℝ) ^ 2 - 2 * (m : ℝ) - 1) * s ^ 2 / 3 -
            4 * s ^ 4 / 45) * e ^ 4 + e ^ 5 * U e) ∧
      (fun e => 4 * rescaledProxyExtension m s e (τ e) /
        ((m : ℝ) * (1 - (m : ℝ) * e)) - 1 - e - (1 - s ^ 2 / 3) * e ^ 2 -
        (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) * e ^ 3 -
        (1 - (4 * (m : ℝ) ^ 2 - 2 * (m : ℝ) - 1) * s ^ 2 / 3 -
          4 * s ^ 4 / 45) * e ^ 4) =O[𝓝 0] (fun e => e ^ 5) ∧
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
  have h0 : R 0 = 1 := rescaledProxyExtension_normalized_optimum_zero m hm s τ hz
  have h1 : deriv R 0 = 1 :=
    (rescaledProxyExtension_normalized_optimum_hasDerivAt m hm s τ hτ hz).deriv
  have h2 : iteratedDeriv 2 R 0 / 2 = 1 - s ^ 2 / 3 := by
    rw [rescaledProxyExtension_normalized_optimum_deriv2 m hm s τ hτ hz hd.deriv]
    ring
  have h3 : iteratedDeriv 3 R 0 / 6 = 1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3 := by
    rw [rescaledProxyExtension_normalized_optimum_deriv3 m hm s τ hτ hz heq]
    ring
  have h4 : iteratedDeriv 4 R 0 / 24 =
      1 - (4 * (m : ℝ) ^ 2 - 2 * (m : ℝ) - 1) * s ^ 2 / 3 - 4 * s ^ 4 / 45 := by
    rw [rescaledProxyExtension_normalized_optimum_deriv4 m hm s τ hτ hz heq]
    ring
  obtain ⟨U, hU, hUeq, hUO⟩ := analytic_quartic_remainder R hR
  refine ⟨τ, U, hτ, hU, hz, hd, ?_, ?_,
    actualHypergeomProxy_critical_branch_is_global m hm s τ heq⟩
  · simpa only [h0, h1, h2, h3, h4, one_mul] using hUeq
  · simpa only [h0, h1, h2, h3, h4, one_mul] using hUO

end

end ExactHoeffding
