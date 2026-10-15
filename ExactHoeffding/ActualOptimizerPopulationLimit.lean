import ExactHoeffding.ActualAnalyticAsymptotics

/-! # Leading asymptotics and positive actual optimizers along populations -/

namespace ExactHoeffding

noncomputable section

open Set Filter Asymptotics
open scoped Topology

theorem actualHypergeomProxy_positive_analytic_optimizer_along
    (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (N K : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ)) :
    ∃ τ : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ᶠ n in atTop, 0 < τ (1 / (N n : ℝ)) ∧ ∀ t : ℝ,
        (∀ u : ℝ, actualHypergeomProxy (N n) (K n) m u ≤
          actualHypergeomProxy (N n) (K n) m t) ↔ t = τ (1 / (N n : ℝ))) ∧
      (fun n => τ (1 / (N n : ℝ)) - 4 * s / (N n : ℝ))
        =O[atTop] (fun n => (1 / (N n : ℝ)) ^ 2) ∧
      Tendsto (fun n => τ (1 / (N n : ℝ)) / (1 / (N n : ℝ))) atTop (𝓝 (4 * s)) := by
  obtain ⟨τ, T, U, hτ, hT, _, hτzero, hd, _, _, hTO, _, hglobal⟩ :=
    actualHypergeomProxy_optimizer_analytic_remainders m hm s
  have he : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hN
  have hepos : ∀ᶠ n in atTop, 0 < 1 / (N n : ℝ) := by
    filter_upwards [hN.eventually (eventually_ge_atTop 2)] with n hn
    have hNR : (0 : ℝ) < N n := by exact_mod_cast (show 0 < N n by omega)
    exact one_div_pos.mpr hNR
  have heright : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ he hepos
  have hene : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝[≠] 0) :=
    heright.mono_right (nhdsGT_le_nhdsNE 0)
  refine ⟨τ, hτ, hτzero, hd, ?_, ?_, ?_⟩
  · filter_upwards [he.eventually hglobal, hvalid,
      hN.eventually (eventually_ge_atTop 2),
      heright.eventually (analytic_branch_eventually_positive τ (4 * s) (by linarith)
        hτzero hd)] with n hg hv hn hp
    exact ⟨hp, hg (N n) (K n) hn hv.1 hv.2.1 rfl hv.2.2⟩
  · simpa only [Function.comp_def, mul_one_div] using hTO.comp_tendsto he
  · have hlim := hd.tendsto_slope.comp hene
    simpa only [Function.comp_def, slope_def_field, hτzero, sub_zero] using hlim

end

end ExactHoeffding
