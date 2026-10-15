import ExactHoeffding.ActualNormalizedFourthAsymptotics
import ExactHoeffding.OptimalProxyAsymptotics

/-! # Fourth-order actual optimal proxies and singleton separation -/

namespace ExactHoeffding
noncomputable section
open Set Filter Asymptotics
open scoped Topology

theorem normalizedHypergeomProxy_fourth_expansion_along
    (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (N K : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ)) :
    (fun n => normalizedHypergeomProxy (N n) (K n) m -
      1 - 1 / (N n : ℝ) - (1 - s ^ 2 / 3) * (1 / (N n : ℝ)) ^ 2 -
      (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) * (1 / (N n : ℝ)) ^ 3 -
      (1 - (4 * (m : ℝ)^2 - 2 * (m : ℝ) - 1) * s^2/3 - 4*s^4/45) *
        (1 / (N n : ℝ)) ^ 4)
      =O[atTop] (fun n => (1 / (N n : ℝ)) ^ 5) := by
  obtain ⟨τ, _, _, _, hglobal, hO⟩ :=
    actualHypergeomProxy_normalized_optimum_fourth_along m hm s hs N K hN hvalid
  apply hO.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hvalid, hglobal] with n hv hg
  have hopt := hypergeomOptimalProxy_eq_actual_at_global_max (N n) (K n) m
    hv.1 hv.2.1 (τ (1 / (N n : ℝ))) (ne_of_gt hg.1) ((hg.2 _).mpr rfl)
  rw [normalizedHypergeomProxy, hopt]
  ring

theorem odd_singleton_gap_fourth_expansion_along
    (m : ℕ) (hm : 0 < m) (s : ℝ) (hs : 0 < s) (N K J : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hvalid : ∀ᶠ n in atTop,
      K n ≤ N n ∧ m ≤ N n ∧ 2 * (K n : ℝ) + s = (N n : ℝ))
    (hodd : ∀ᶠ n in atTop, N n = 2 * J n + 1) :
    (fun n => oddHypergeomConstant (N n) - normalizedHypergeomProxy (N n) (K n) m -
      (s ^ 2 - 1) / 3 * (1 / (N n : ℝ)) ^ 2 -
      ((2 * (m : ℝ) - 1) * s ^ 2 - 1) / 3 * (1 / (N n : ℝ)) ^ 3 -
      (((4 * (m : ℝ)^2 - 2*(m : ℝ)-1)*s^2-1)/3 + 4*(s^4-1)/45) *
        (1 / (N n : ℝ)) ^ 4)
      =O[atTop] (fun n => (1 / (N n : ℝ)) ^ 5) := by
  have hsingle : ∀ᶠ n in atTop,
      J n ≤ N n ∧ 1 ≤ N n ∧ 2 * (J n : ℝ) + (1 : ℝ) = (N n : ℝ) := by
    filter_upwards [hodd] with n hn
    refine ⟨by omega, by omega, ?_⟩
    rw [hn]
    push_cast
    rfl
  have h1 := normalizedHypergeomProxy_fourth_expansion_along 1 (by omega)
    1 (by norm_num) N J hN hsingle
  have hmO := normalizedHypergeomProxy_fourth_expansion_along m hm s hs N K hN hvalid
  apply (h1.sub hmO).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hodd, hN.eventually (eventually_ge_atTop 3)] with n hn hlarge
  have hj : 0 < J n := by omega
  have heq : normalizedHypergeomProxy (N n) (J n) 1 = oddHypergeomConstant (N n) := by
    rw [hn]
    exact (odd_normalized_proxy_all_equality (J n) (J n) 1 hj hj (by omega)
      (by omega) (by omega)).mpr ⟨Or.inl rfl, Or.inl rfl⟩
  rw [heq]
  ring

/-- The fourth-order singleton gap of the actual supremum-defined proxy. -/
theorem odd_nearly_balanced_gap_fourth_expansion_along
    (m : ℕ) (hm : 0 < m) (N J : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hodd : ∀ᶠ n in atTop, N n = 2 * J n + 1) :
    (fun n => oddHypergeomConstant (N n) - normalizedHypergeomProxy (N n) (J n) m -
      2 * ((m : ℝ)-1)/3 * (1/(N n : ℝ))^3 -
      2 * ((m : ℝ)-1)*(2*(m : ℝ)+1)/3 * (1/(N n : ℝ))^4)
      =O[atTop] (fun n => (1/(N n : ℝ))^5) := by
  have hvalid : ∀ᶠ n in atTop,
      J n ≤ N n ∧ m ≤ N n ∧ 2 * (J n : ℝ) + 1 = (N n : ℝ) := by
    filter_upwards [hodd, hN.eventually (eventually_ge_atTop m)] with n hn hmN
    refine ⟨by omega, hmN, ?_⟩
    rw [hn]
    push_cast
    rfl
  have h := odd_singleton_gap_fourth_expansion_along m hm 1 (by norm_num)
    N J J hN hvalid hodd
  apply h.congr' ?_ Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall fun n => by ring

/-- Removing the cubic term isolates the exact fourth-order singleton gap. -/
theorem odd_nearly_balanced_gap_fourth_limit_along
    (m : ℕ) (hm : 0 < m) (N J : ℕ → ℕ)
    (hN : Tendsto N atTop atTop)
    (hodd : ∀ᶠ n in atTop, N n = 2 * J n + 1) :
    Tendsto (fun n =>
      (oddHypergeomConstant (N n) - normalizedHypergeomProxy (N n) (J n) m -
        2*((m : ℝ)-1)/3*(1/(N n : ℝ))^3) / (1/(N n : ℝ))^4)
      atTop (𝓝 (2*((m : ℝ)-1)*(2*(m : ℝ)+1)/3)) := by
  have he : Tendsto (fun n => 1/(N n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hN
  have hO := odd_nearly_balanced_gap_fourth_expansion_along m hm N J hN hodd
  have hl := hO.trans_isLittleO
    ((isLittleO_pow_pow (𝕜 := ℝ) (show 4 < 5 by omega)).comp_tendsto he)
  have ht := hl.tendsto_div_nhds_zero.add_const (2*((m : ℝ)-1)*(2*(m : ℝ)+1)/3)
  simp only [zero_add] at ht
  apply ht.congr' ?_
  filter_upwards [hN.eventually (eventually_ge_atTop 2)] with n hn
  have hn0 : (N n : ℝ) ≠ 0 := by exact_mod_cast (show N n ≠ 0 by omega)
  simp only [Function.comp_def]
  field_simp [hn0]
  <;> ring

end
end ExactHoeffding
