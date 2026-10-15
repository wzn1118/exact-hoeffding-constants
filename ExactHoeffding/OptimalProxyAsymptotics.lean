import ExactHoeffding.ActualNormalizedAsymptotics
import ExactHoeffding.ActualNormalizedThirdAsymptotics
import ExactHoeffding.NormalizedProxy
import ExactHoeffding.OddHypergeomExtremizers

/-! # Globally optimized population expansions for the least quadratic proxy

The actual maximizing value is identified with the supremum defining the
manuscript's optimal variance proxy. This transfers the analytic optimizer
expansion to `normalizedHypergeomProxy` itself.
-/

namespace ExactHoeffding

noncomputable section

open Set Filter Asymptotics
open scoped Topology

theorem actualHypergeomProxy_eq_quotient (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) (ht : t ≠ 0) :
    actualHypergeomProxy N k m t = 2 * hypergeomCenteredLogMGF N k m t / t ^ 2 := by
  rw [actualHypergeomProxy, if_neg ht, hypergeom_centered_log_identity N k m hk hm]
  rfl

theorem hypergeomOptimalProxy_eq_actual_at_global_max (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) (ht : t ≠ 0)
    (hmax : ∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) :
    hypergeomOptimalProxy N k m = actualHypergeomProxy N k m t := by
  apply le_antisymm
  · unfold hypergeomOptimalProxy optimalProxy
    apply csSup_le (proxyQuotientSet_nonempty _)
    rintro v ⟨u, hu, rfl⟩
    rw [← actualHypergeomProxy_eq_quotient N k m hk hm u hu]
    exact hmax u
  · unfold hypergeomOptimalProxy optimalProxy
    apply le_csSup (proxyQuotientSet_bddAbove _ _
      (hypergeom_uniform_log_laplace_domination N k m hk hm))
    exact ⟨t, ht, actualHypergeomProxy_eq_quotient N k m hk hm t ht⟩

theorem normalizedHypergeomProxy_second_expansion_along
    (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (N K : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ)) :
    (fun n => normalizedHypergeomProxy (N n) (K n) m -
      1 - 1 / (N n : ℝ) - (1 - s ^ 2 / 3) * (1 / (N n : ℝ)) ^ 2)
      =O[atTop] (fun n => (1 / (N n : ℝ)) ^ 3) := by
  obtain ⟨τ, _, _, _, hglobal, hO⟩ :=
    actualHypergeomProxy_normalized_optimum_second_along m hm s hs N K hN hvalid
  apply hO.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hvalid, hglobal] with n hv hg
  have hopt := hypergeomOptimalProxy_eq_actual_at_global_max (N n) (K n) m
    hv.1 hv.2.1 (τ (1 / (N n : ℝ))) (ne_of_gt hg.1) ((hg.2 _).mpr rfl)
  rw [normalizedHypergeomProxy, hopt]
  ring

theorem normalizedHypergeomProxy_third_expansion_along
    (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (N K : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ)) :
    (fun n => normalizedHypergeomProxy (N n) (K n) m -
      1 - 1 / (N n : ℝ) - (1 - s ^ 2 / 3) * (1 / (N n : ℝ)) ^ 2 -
      (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) * (1 / (N n : ℝ)) ^ 3)
      =O[atTop] (fun n => (1 / (N n : ℝ)) ^ 4) := by
  obtain ⟨τ, _, _, _, hglobal, hO⟩ :=
    actualHypergeomProxy_normalized_optimum_third_along m hm s hs N K hN hvalid
  apply hO.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hvalid, hglobal] with n hv hg
  have hopt := hypergeomOptimalProxy_eq_actual_at_global_max (N n) (K n) m
    hv.1 hv.2.1 (τ (1 / (N n : ℝ))) (ne_of_gt hg.1) ((hg.2 _).mpr rfl)
  rw [normalizedHypergeomProxy, hopt]
  ring

/-- The leading separation from the odd singleton optimum, along every
admissible fixed-imbalance population sequence. -/
theorem odd_singleton_gap_second_expansion_along
    (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (N K J : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ))
    (hodd : ∀ᶠ n in atTop, N n = 2 * J n + 1) :
    (fun n => oddHypergeomConstant (N n) - normalizedHypergeomProxy (N n) (K n) m -
      (s ^ 2 - 1) / 3 * (1 / (N n : ℝ)) ^ 2)
      =O[atTop] (fun n => (1 / (N n : ℝ)) ^ 3) := by
  have hsingle : ∀ᶠ n in atTop,
      J n ≤ N n ∧ 1 ≤ N n ∧ 2 * (J n : ℝ) + (1 : ℝ) = (N n : ℝ) := by
    filter_upwards [hodd] with n hn
    refine ⟨by omega, by omega, ?_⟩
    rw [hn]
    push_cast
    rfl
  have h1 := normalizedHypergeomProxy_second_expansion_along 1 (by omega)
    1 (by norm_num) N J hN hsingle
  have hmO := normalizedHypergeomProxy_second_expansion_along m hm s hs N K hN hvalid
  apply (h1.sub hmO).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hodd, hN.eventually (eventually_ge_atTop 3)] with n hn hlarge
  have hj : 0 < J n := by omega
  have heq : normalizedHypergeomProxy (N n) (J n) 1 = oddHypergeomConstant (N n) := by
    rw [hn]
    exact (odd_normalized_proxy_all_equality (J n) (J n) 1 hj hj (by omega)
      (by omega) (by omega)).mpr ⟨Or.inl rfl, Or.inl rfl⟩
  rw [heq]
  ring

theorem odd_singleton_gap_third_expansion_along
    (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (N K J : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ))
    (hodd : ∀ᶠ n in atTop, N n = 2 * J n + 1) :
    (fun n => oddHypergeomConstant (N n) - normalizedHypergeomProxy (N n) (K n) m -
      (s ^ 2 - 1) / 3 * (1 / (N n : ℝ)) ^ 2 -
      ((2 * (m : ℝ) - 1) * s ^ 2 - 1) / 3 * (1 / (N n : ℝ)) ^ 3)
      =O[atTop] (fun n => (1 / (N n : ℝ)) ^ 4) := by
  have hsingle : ∀ᶠ n in atTop,
      J n ≤ N n ∧ 1 ≤ N n ∧ 2 * (J n : ℝ) + (1 : ℝ) = (N n : ℝ) := by
    filter_upwards [hodd] with n hn
    refine ⟨by omega, by omega, ?_⟩
    rw [hn]
    push_cast
    rfl
  have h1 := normalizedHypergeomProxy_third_expansion_along 1 (by omega)
    1 (by norm_num) N J hN hsingle
  have hmO := normalizedHypergeomProxy_third_expansion_along m hm s hs N K hN hvalid
  apply (h1.sub hmO).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hodd, hN.eventually (eventually_ge_atTop 3)] with n hn hlarge
  have hj : 0 < J n := by omega
  have heq : normalizedHypergeomProxy (N n) (J n) 1 = oddHypergeomConstant (N n) := by
    rw [hn]
    exact (odd_normalized_proxy_all_equality (J n) (J n) 1 hj hj (by omega)
      (by omega) (by omega)).mpr ⟨Or.inl rfl, Or.inl rfl⟩
  rw [heq]
  ring

/-- The exact leading off-balance singleton gap coefficient. -/
theorem odd_singleton_gap_second_limit_along
    (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (N K J : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ))
    (hodd : ∀ᶠ n in atTop, N n = 2 * J n + 1) :
    Tendsto (fun n =>
      (oddHypergeomConstant (N n) - normalizedHypergeomProxy (N n) (K n) m) /
        (1 / (N n : ℝ)) ^ 2) atTop (𝓝 ((s ^ 2 - 1) / 3)) := by
  have he : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hN
  have hO := odd_singleton_gap_second_expansion_along m hm s hs N K J hN hvalid hodd
  have hl := hO.trans_isLittleO
    ((isLittleO_pow_pow (𝕜 := ℝ) (show 2 < 3 by omega)).comp_tendsto he)
  have ht := hl.tendsto_div_nhds_zero.add_const ((s ^ 2 - 1) / 3)
  simp only [zero_add] at ht
  apply ht.congr' ?_
  filter_upwards [hN.eventually (eventually_ge_atTop 2)] with n hn
  have hn0 : (N n : ℝ) ≠ 0 := by exact_mod_cast (show N n ≠ 0 by omega)
  simp only [Function.comp_def]
  field_simp [hn0]
  <;> ring

/-- Every fixed imbalance strictly larger than one is separated from the
odd optimal constant for every sufficiently large admissible population. -/
theorem odd_singleton_gap_eventually_pos_along
    (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 1 < s) (N K J : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ))
    (hodd : ∀ᶠ n in atTop, N n = 2 * J n + 1) :
    ∀ᶠ n in atTop,
      normalizedHypergeomProxy (N n) (K n) m < oddHypergeomConstant (N n) := by
  have hc : 0 < (s ^ 2 - 1) / 3 := by nlinarith
  have hl := odd_singleton_gap_second_limit_along m hm s (by linarith)
    N K J hN hvalid hodd
  filter_upwards [hl.eventually (eventually_gt_nhds hc),
    hN.eventually (eventually_ge_atTop 2)] with n hn hNn
  have hp : 0 < (1 / (N n : ℝ)) ^ 2 := by
    have : (0 : ℝ) < N n := by exact_mod_cast (show 0 < N n by omega)
    positivity
  have hgap := (lt_div_iff₀ hp).mp hn
  linarith

end

end ExactHoeffding
