import ExactHoeffding.ActualAnalyticAsymptotics
import ExactHoeffding.NormalizedOptimumSecond

/-! # Actual globally optimized expansion through second inverse-population order

The remainder is an analytic function times `e^3`. This is not the paper's
fourth-order coefficient formula, which requires further computations.
-/

namespace ExactHoeffding

noncomputable section

open Filter Asymptotics
open scoped Topology

theorem analytic_quadratic_remainder (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      (∀ e : ℝ, f e = f 0 + deriv f 0 * e + iteratedDeriv 2 f 0 / 2 * e ^ 2 +
        e ^ 3 * R e) ∧
      (fun e => f e - f 0 - deriv f 0 * e - iteratedDeriv 2 f 0 / 2 * e ^ 2)
        =O[𝓝 0] (fun e => e ^ 3) := by
  obtain ⟨T, hT, hTeq, _⟩ := analytic_linear_remainder f hf
  have hfun : f = (fun e => f 0 + deriv f 0 * e + e ^ 2 * T e) := funext hTeq
  have hdd := congrArg (fun g : ℝ → ℝ => iteratedDeriv 2 g 0) hfun
  rw [iteratedDeriv_fun_add
    (f := fun e : ℝ => f 0 + deriv f 0 * e) (g := fun e : ℝ => e ^ 2 * T e)
    (by fun_prop) (analyticAt_id.pow 2 |>.mul hT |>.contDiffAt),
    iteratedDeriv_fun_add (f := fun _ : ℝ => f 0) (g := fun e : ℝ => deriv f 0 * e)
      (by fun_prop) (by fun_prop),
    iteratedDeriv_const, iteratedDeriv_const_mul_field, iteratedDeriv_fun_id,
    iteratedDeriv2_quadratic_factor T hT] at hdd
  norm_num at hdd
  have hTzero : T 0 = iteratedDeriv 2 f 0 / 2 := by linarith
  let R := dslope T 0
  have hR : AnalyticAt ℝ R 0 := analyticAt_dslope_zero hT
  have heq (e : ℝ) : f e = f 0 + deriv f 0 * e + iteratedDeriv 2 f 0 / 2 * e ^ 2 +
      e ^ 3 * R e := by
    have hs := sub_smul_dslope T 0 e
    simp only [sub_zero, smul_eq_mul, hTzero] at hs
    rw [hTeq e]
    dsimp [R]
    nlinarith [congrArg (fun x : ℝ => e ^ 2 * x) hs]
  refine ⟨R, hR, heq, ?_⟩
  have hbounded : R =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := hR.continuousAt.isBigO_one ℝ
  have hbound := (isBigO_refl (fun e : ℝ => e ^ 3) (𝓝 0)).mul hbounded
  have hrem : (fun e => f e - f 0 - deriv f 0 * e - iteratedDeriv 2 f 0 / 2 * e ^ 2) =
      (fun e => e ^ 3 * R e) := by
    funext e
    rw [heq e]
    ring
  rw [hrem]
  simpa only [mul_one] using hbound

theorem actualHypergeomProxy_optimum_second_analytic_expansion
    (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ τ U : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ AnalyticAt ℝ U 0 ∧
      τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ e, 4 * rescaledProxyExtension m s e (τ e) /
        ((m : ℝ) * (1 - (m : ℝ) * e)) =
          1 + e + (1 - s ^ 2 / 3) * e ^ 2 + e ^ 3 * U e) ∧
      (fun e => 4 * rescaledProxyExtension m s e (τ e) /
        ((m : ℝ) * (1 - (m : ℝ) * e)) - 1 - e - (1 - s ^ 2 / 3) * e ^ 2)
        =O[𝓝 0] (fun e => e ^ 3) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
        2 * (k : ℝ) + s = (N : ℝ) → ∀ t : ℝ,
        (∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) ↔
          t = τ e) := by
  obtain ⟨τ, hτ, hτzero, hd, hglobal⟩ := actualHypergeomProxy_analytic_optimizer_leading m hm s
  let R : ℝ → ℝ := fun e => 4 * rescaledProxyExtension m s e (τ e) /
    ((m : ℝ) * (1 - (m : ℝ) * e))
  have hR := rescaledProxyExtension_normalized_optimum_analytic m hm s τ hτ hτzero
  have hz : R 0 = 1 := rescaledProxyExtension_normalized_optimum_zero m hm s τ hτzero
  have hdR : deriv R 0 = 1 :=
    (rescaledProxyExtension_normalized_optimum_hasDerivAt m hm s τ hτ hτzero).deriv
  have hdd : iteratedDeriv 2 R 0 / 2 = 1 - s ^ 2 / 3 := by
    rw [rescaledProxyExtension_normalized_optimum_deriv2 m hm s τ hτ hτzero hd.deriv]
    ring
  obtain ⟨U, hU, hUeq, hUO⟩ := analytic_quadratic_remainder R hR
  refine ⟨τ, U, hτ, hU, hτzero, hd, ?_, ?_, hglobal⟩
  · simpa only [hz, hdR, hdd, one_mul] using hUeq
  · simpa only [hz, hdR, hdd, one_mul] using hUO

end

end ExactHoeffding
