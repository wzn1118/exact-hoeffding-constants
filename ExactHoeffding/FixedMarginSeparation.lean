import ExactHoeffding.OptimalProxyAsymptotics

/-! # Comparison of two globally optimized fixed-margin population families -/

namespace ExactHoeffding
noncomputable section
open Set Filter Asymptotics
open scoped Topology

/-- The exact leading separation between two fixed-imbalance normalized
proxies.  Both values are the actual global optima. -/
theorem normalizedHypergeomProxy_fixed_margin_difference_limit
    (m₀ m₁ : ℕ) (hm₀ : 0 < m₀) (hm₁ : 0 < m₁)
    (s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (hs₁ : 0 < s₁)
    (N K₀ K₁ : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hvalid₀ : ∀ᶠ n in atTop,
      K₀ n ≤ N n ∧ m₀ ≤ N n ∧ 2 * (K₀ n : ℝ) + s₀ = (N n : ℝ))
    (hvalid₁ : ∀ᶠ n in atTop,
      K₁ n ≤ N n ∧ m₁ ≤ N n ∧ 2 * (K₁ n : ℝ) + s₁ = (N n : ℝ)) :
    Tendsto (fun n =>
      (normalizedHypergeomProxy (N n) (K₀ n) m₀ -
        normalizedHypergeomProxy (N n) (K₁ n) m₁) /
          (1 / (N n : ℝ)) ^ 2) atTop (𝓝 ((s₁ ^ 2 - s₀ ^ 2) / 3)) := by
  have h₀ := normalizedHypergeomProxy_second_expansion_along
    m₀ hm₀ s₀ hs₀ N K₀ hN hvalid₀
  have h₁ := normalizedHypergeomProxy_second_expansion_along
    m₁ hm₁ s₁ hs₁ N K₁ hN hvalid₁
  have hO : (fun n =>
      normalizedHypergeomProxy (N n) (K₀ n) m₀ -
        normalizedHypergeomProxy (N n) (K₁ n) m₁ -
          (s₁ ^ 2 - s₀ ^ 2) / 3 * (1 / (N n : ℝ)) ^ 2)
      =O[atTop] (fun n => (1 / (N n : ℝ)) ^ 3) := by
    apply (h₀.sub h₁).congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall (fun n => by ring)
  have he : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hN
  have hl := hO.trans_isLittleO
    ((isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 3 by omega)).comp_tendsto he)
  have ht := hl.tendsto_div_nhds_zero.add_const ((s₁ ^ 2 - s₀ ^ 2) / 3)
  simp only [zero_add] at ht
  apply ht.congr' ?_
  filter_upwards [hN.eventually (eventually_ge_atTop 2)] with n hn
  have hn0 : (N n : ℝ) ≠ 0 := by exact_mod_cast (show N n ≠ 0 by omega)
  simp only [Function.comp_def]
  field_simp [hn0]
  <;> ring

/-- A larger fixed imbalance has a strictly smaller normalized proxy for
every sufficiently large admissible population. -/
theorem normalizedHypergeomProxy_fixed_margin_eventually_lt
    (m₀ m₁ : ℕ) (hm₀ : 0 < m₀) (hm₁ : 0 < m₁)
    (s₀ s₁ : ℝ) (hs₀ : 0 < s₀) (hss : s₀ < s₁)
    (N K₀ K₁ : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (hvalid₀ : ∀ᶠ n in atTop,
      K₀ n ≤ N n ∧ m₀ ≤ N n ∧ 2 * (K₀ n : ℝ) + s₀ = (N n : ℝ))
    (hvalid₁ : ∀ᶠ n in atTop,
      K₁ n ≤ N n ∧ m₁ ≤ N n ∧ 2 * (K₁ n : ℝ) + s₁ = (N n : ℝ)) :
    ∀ᶠ n in atTop,
      normalizedHypergeomProxy (N n) (K₁ n) m₁ <
        normalizedHypergeomProxy (N n) (K₀ n) m₀ := by
  have hc : 0 < (s₁ ^ 2 - s₀ ^ 2) / 3 := by nlinarith
  have hl := normalizedHypergeomProxy_fixed_margin_difference_limit
    m₀ m₁ hm₀ hm₁ s₀ s₁ hs₀ (lt_trans hs₀ hss) N K₀ K₁ hN hvalid₀ hvalid₁
  filter_upwards [hl.eventually (eventually_gt_nhds hc),
    hN.eventually (eventually_ge_atTop 2)] with n hn hNn
  have hp : 0 < (1 / (N n : ℝ)) ^ 2 := by
    have : (0 : ℝ) < N n := by exact_mod_cast (show 0 < N n by omega)
    positivity
  have hgap := (lt_div_iff₀ hp).mp hn
  linarith

end
end ExactHoeffding
