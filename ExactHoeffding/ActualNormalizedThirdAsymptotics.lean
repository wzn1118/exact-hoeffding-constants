import ExactHoeffding.ActualNormalizedThirdCoefficient

/-! # The actual normalized global optimum along integer populations

This exposes the manuscript's normalization `4*N/(m*(N-m))` directly.
The third-order coefficient and quartic remainder refer to actual global
maximizing tilts along every admissible population sequence.
-/

namespace ExactHoeffding

noncomputable section

open Set Filter Asymptotics
open scoped Topology

theorem actualHypergeomProxy_normalized_optimum_third_along
    (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (N K : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ)) :
    ∃ τ : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ᶠ n in atTop, 0 < τ (1 / (N n : ℝ)) ∧ ∀ t : ℝ,
        (∀ u : ℝ, actualHypergeomProxy (N n) (K n) m u ≤
          actualHypergeomProxy (N n) (K n) m t) ↔ t = τ (1 / (N n : ℝ))) ∧
      (fun n =>
        4 * (N n : ℝ) * actualHypergeomProxy (N n) (K n) m (τ (1 / (N n : ℝ))) /
          ((m : ℝ) * ((N n : ℝ) - (m : ℝ))) -
          1 - 1 / (N n : ℝ) - (1 - s ^ 2 / 3) * (1 / (N n : ℝ)) ^ 2 -
          (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) * (1 / (N n : ℝ)) ^ 3)
        =O[atTop] (fun n => (1 / (N n : ℝ)) ^ 4) := by
  obtain ⟨τ, U, hτ, _, hτzero, hd, _, hRO, hglobal⟩ :=
    actualHypergeomProxy_optimum_third_analytic_expansion m hm s
  have he : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hN
  have hepos : ∀ᶠ n in atTop, 0 < 1 / (N n : ℝ) := by
    filter_upwards [hN.eventually (eventually_ge_atTop 2)] with n hn
    have hNR : (0 : ℝ) < N n := by exact_mod_cast (show 0 < N n by omega)
    exact one_div_pos.mpr hNR
  have heright : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ he hepos
  have hbridge : ∀ᶠ n in atTop,
      4 * rescaledProxyExtension m s (1 / (N n : ℝ)) (τ (1 / (N n : ℝ))) /
          ((m : ℝ) * (1 - (m : ℝ) * (1 / (N n : ℝ)))) =
        4 * (N n : ℝ) * actualHypergeomProxy (N n) (K n) m (τ (1 / (N n : ℝ))) /
          ((m : ℝ) * ((N n : ℝ) - (m : ℝ))) := by
    filter_upwards [hvalid, hN.eventually (eventually_ge_atTop (max 2 (m + 1)))]
      with n hv hn
    have hn2 : 2 ≤ N n := (le_max_left _ _).trans hn
    have hnm : m < N n := by have := (le_max_right 2 (m + 1)).trans hn; omega
    have hNR : (N n : ℝ) ≠ 0 := by exact_mod_cast (show N n ≠ 0 by omega)
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have hdiff : (N n : ℝ) - (m : ℝ) ≠ 0 := by
      have hlt : (m : ℝ) < N n := by exact_mod_cast hnm
      linarith
    rw [rescaledProxyExtension_hypergeom (N n) (K n) m s _ hn2 hv.1 hv.2.1 hm hv.2.2]
    field_simp [hNR, hmR, hdiff]
  refine ⟨τ, hτ, hτzero, hd, ?_, ?_⟩
  · filter_upwards [he.eventually hglobal, hvalid,
      hN.eventually (eventually_ge_atTop 2),
      heright.eventually (analytic_branch_eventually_positive τ (4 * s) (by linarith)
        hτzero hd)] with n hg hv hn hp
    exact ⟨hp, hg (N n) (K n) hn hv.1 hv.2.1 rfl hv.2.2⟩
  · apply (hRO.comp_tendsto he).congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hbridge] with n hn
    dsimp only [Function.comp_def]
    rw [hn]

end

end ExactHoeffding
