import ExactHoeffding.ActualOptimizerLocalization
import ExactHoeffding.RescaledUniformConcavity
import Mathlib.Analysis.Convex.Continuous

/-! # Existence and uniqueness of actual globally maximizing tilts

For fixed positive sample size and fixed real imbalance, this proves the
unique global maximizer for all sufficiently large admissible populations.
No existence, uniqueness, or localization statement is an assumption.
Analytic dependence and expansion coefficients are separate remaining claims.
-/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

theorem exists_unique_global_max_of_strictConcave_localized
    (f : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hconc : StrictConcaveOn ℝ (Icc (-δ) δ) f)
    (houtside : ∀ t : ℝ, δ / 2 ≤ |t| → f t < f 0) :
    ∃! t : ℝ, ∀ u : ℝ, f u ≤ f t := by
  have hcont : ContinuousOn f (Icc (-(δ / 2)) (δ / 2)) := by
    apply hconc.concaveOn.continuousOn_interior.mono
    intro t ht
    rw [interior_Icc]
    constructor <;> linarith [ht.1, ht.2]
  have h0 : (0 : ℝ) ∈ Icc (-(δ / 2)) (δ / 2) := by constructor <;> linarith
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, h0⟩ hcont
  have hglobal : ∀ u : ℝ, f u ≤ f t := by
    intro u
    by_cases hu : u ∈ Icc (-(δ / 2)) (δ / 2)
    · exact hmax hu
    · have huabs : δ / 2 ≤ |u| := by
        by_contra hn
        have habs := abs_lt.mp (lt_of_not_ge hn)
        exact hu ⟨habs.1.le, habs.2.le⟩
      exact (houtside u huabs).le.trans (hmax h0)
  refine ⟨t, hglobal, ?_⟩
  intro v hv
  have hvabs : |v| < δ / 2 := by
    by_contra hn
    exact (not_lt_of_ge (hv 0)) (houtside v (le_of_not_gt hn))
  have htbig : t ∈ Icc (-δ) δ := by constructor <;> linarith [ht.1, ht.2]
  have hvbig : v ∈ Icc (-δ) δ := by
    have hvbounds := abs_lt.mp hvabs
    constructor <;> linarith [hvbounds.1, hvbounds.2]
  exact hconc.eq_of_isMaxOn (fun _ _ => hv _) (fun _ _ => hglobal _) hvbig htbig

/-- The paper's existence and unique-global-optimizer assertion, before
positivity, analytic dependence, and the coefficient expansion are added. -/
theorem actualHypergeomProxy_eventually_exists_unique_global_max
    (m : ℕ) (hmpos : 0 < m) (s : ℝ) :
    ∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
      2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
      2 * (k : ℝ) + s = (N : ℝ) →
      ∃! t : ℝ, ∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t := by
  obtain ⟨δ, hδ, hconc⟩ := rescaledProxyExtension_uniform_strictConcave m hmpos s
  filter_upwards [hconc,
    actualHypergeomProxy_eventually_outside_lt_zero m hmpos s (δ / 2) (by linarith)]
      with e hconce hloc
  intro N k hN hk hm he hbalance
  have heq : ∀ t, rescaledProxyExtension m s e t = actualHypergeomProxy N k m t := by
    intro t
    rw [he]
    exact rescaledProxyExtension_hypergeom N k m s t hN hk hm hmpos hbalance
  apply exists_unique_global_max_of_strictConcave_localized _ δ hδ
  · exact hconce.congr (fun t _ => heq t)
  · exact hloc N k hN hk hm he hbalance

/-- Arbitrary admissible subsequences are covered; no parity-specific
enumeration or optimizer-selection hypothesis is used. -/
theorem actualHypergeomProxy_exists_unique_global_max_along
    (m : ℕ) (hmpos : 0 < m) (s : ℝ) (N K : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ)) :
    ∀ᶠ n in atTop,
      ∃! t : ℝ, ∀ u : ℝ,
        actualHypergeomProxy (N n) (K n) m u ≤ actualHypergeomProxy (N n) (K n) m t := by
  have he : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hN
  filter_upwards [he.eventually
      (actualHypergeomProxy_eventually_exists_unique_global_max m hmpos s),
    hvalid, hN.eventually (eventually_ge_atTop 2)] with n hopt hv hNn
  exact hopt (N n) (K n) hNn hv.1 hv.2.1 rfl hv.2.2

end

end ExactHoeffding
