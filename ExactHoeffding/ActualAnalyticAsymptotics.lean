import ExactHoeffding.RescaledOptimumLeading
import Mathlib.Analysis.Asymptotics.Lemmas

/-! # Actual global optimizers with analytic first-order asymptotic remainders

These expansions are in inverse population, not in the tilt of a fixed law.
The second and higher numerical coefficients are deliberately not asserted.
-/

namespace ExactHoeffding

noncomputable section

open Set Filter Asymptotics
open scoped Topology

theorem analytic_linear_remainder (f : ℝ → ℝ) (hf : AnalyticAt ℝ f 0) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      (∀ e : ℝ, f e = f 0 + deriv f 0 * e + e ^ 2 * R e) ∧
      (fun e => f e - f 0 - deriv f 0 * e) =O[𝓝 0] (fun e => e ^ 2) := by
  let R := dslope (dslope f 0) 0
  have hR : AnalyticAt ℝ R 0 := analyticAt_dslope_zero (analyticAt_dslope_zero hf)
  have heq (e : ℝ) : f e = f 0 + deriv f 0 * e + e ^ 2 * R e := by
    have h1 := sub_smul_dslope f 0 e
    have h2 := sub_smul_dslope (dslope f 0) 0 e
    simp only [sub_zero, smul_eq_mul, dslope_same] at h1 h2
    dsimp [R]
    nlinarith [congrArg (fun x : ℝ => e * x) h2]
  refine ⟨R, hR, heq, ?_⟩
  have hbounded : R =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := hR.continuousAt.isBigO_one ℝ
  have hbound := (isBigO_refl (fun e : ℝ => e ^ 2) (𝓝 0)).mul
    hbounded
  have hrem : (fun e => f e - f 0 - deriv f 0 * e) = (fun e => e ^ 2 * R e) := by
    funext e
    rw [heq e]
    ring
  rw [hrem]
  simpa only [mul_one] using hbound

theorem actualHypergeomProxy_critical_branch_is_global
    (m : ℕ) (hmpos : 0 < m) (s : ℝ) (τ : ℝ → ℝ)
    (heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
      deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) :
    ∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
      2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
      2 * (k : ℝ) + s = (N : ℝ) → ∀ t : ℝ,
      (∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) ↔
        t = τ e := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp heq
  filter_upwards [actualHypergeomProxy_eventually_exists_unique_global_max m hmpos s,
    actualHypergeomProxy_eventually_outside_lt_zero m hmpos s (r / 2) (by linarith),
    isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-r / 2) (r / 2) by
      constructor <;> linarith)] with e hexists hloc he
  intro N k hN hk hm heN hbalance
  have hbridge (t : ℝ) : rescaledProxyExtension m s e t =
      actualHypergeomProxy N k m t := by
    rw [heN]
    exact rescaledProxyExtension_hypergeom N k m s t hN hk hm hmpos hbalance
  have hforward (t : ℝ)
      (hmax : ∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) :
      t = τ e := by
    have ht : |t| < r / 2 := by
      by_contra hn
      exact (not_lt_of_ge (hmax 0))
        (hloc N k hN hk hm heN hbalance t (le_of_not_gt hn))
    have hdist : dist (e, t) ((0 : ℝ), (0 : ℝ)) < r := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero, max_lt_iff]
      constructor
      · exact abs_lt.mpr ⟨by linarith [he.1], by linarith [he.2]⟩
      · linarith
    have hmaxQ : IsLocalMax (rescaledProxyExtension m s e) t := by
      apply Filter.Eventually.of_forall
      intro u
      simpa only [hbridge] using hmax u
    exact ((hball hdist).mp hmaxQ.deriv_eq_zero).symm
  intro t
  refine ⟨hforward t, ?_⟩
  intro ht
  obtain ⟨v, hv, _⟩ := hexists N k hN hk hm heN hbalance
  simpa only [ht, hforward v hv] using hv

/-- One branch simultaneously has the proved leading coefficient and
characterizes the actual unique global optimizer for every large valid law. -/
theorem actualHypergeomProxy_analytic_optimizer_leading
    (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ τ : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
        2 * (k : ℝ) + s = (N : ℝ) → ∀ t : ℝ,
        (∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) ↔
          t = τ e) := by
  obtain ⟨τ, hτ, hτzero, hd, heq⟩ :=
    rescaledProxyExtension_analytic_critical_branch_leading m hm s
  exact ⟨τ, hτ, hτzero, hd,
    actualHypergeomProxy_critical_branch_is_global m hm s τ heq⟩

theorem actualHypergeomProxy_optimizer_analytic_remainders
    (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ τ T U : ℝ → ℝ,
      AnalyticAt ℝ τ 0 ∧ AnalyticAt ℝ T 0 ∧ AnalyticAt ℝ U 0 ∧
      τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ e, τ e = 4 * s * e + e ^ 2 * T e) ∧
      (∀ e, 4 * rescaledProxyExtension m s e (τ e) /
        ((m : ℝ) * (1 - (m : ℝ) * e)) = 1 + e + e ^ 2 * U e) ∧
      (fun e => τ e - 4 * s * e) =O[𝓝 0] (fun e => e ^ 2) ∧
      (fun e => 4 * rescaledProxyExtension m s e (τ e) /
        ((m : ℝ) * (1 - (m : ℝ) * e)) - 1 - e) =O[𝓝 0] (fun e => e ^ 2) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
        2 * (k : ℝ) + s = (N : ℝ) → ∀ t : ℝ,
        (∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) ↔
          t = τ e) := by
  obtain ⟨τ, hτ, hτzero, hd, hglobal⟩ := actualHypergeomProxy_analytic_optimizer_leading m hm s
  obtain ⟨T, hT, hTeq, hTO⟩ := analytic_linear_remainder τ hτ
  let R : ℝ → ℝ := fun e => 4 * rescaledProxyExtension m s e (τ e) /
    ((m : ℝ) * (1 - (m : ℝ) * e))
  have hR := rescaledProxyExtension_normalized_optimum_analytic m hm s τ hτ hτzero
  have hRzero : R 0 = 1 :=
    rescaledProxyExtension_normalized_optimum_zero m hm s τ hτzero
  have hRd : deriv R 0 = 1 :=
    (rescaledProxyExtension_normalized_optimum_hasDerivAt m hm s τ hτ hτzero).deriv
  obtain ⟨U, hU, hUeq, hUO⟩ := analytic_linear_remainder R hR
  refine ⟨τ, T, U, hτ, hT, hU, hτzero, hd, ?_, ?_, ?_, ?_, hglobal⟩
  · simpa only [hτzero, hd.deriv, zero_add] using hTeq
  · simpa only [hRzero, hRd, one_mul] using hUeq
  · simpa only [hτzero, hd.deriv, sub_zero] using hTO
  · simpa only [hRzero, hRd, one_mul] using hUO

end

end ExactHoeffding
