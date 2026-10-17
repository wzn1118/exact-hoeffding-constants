import ExactHoeffding.GoalBIndividualMargin

/-! # Strict imbalance monotonicity of the individual-margin certificate

A positive sample scale makes the first branch of the explicit certificate
strictly increasing with the nonnegative population imbalance.
-/

namespace ExactHoeffding
noncomputable section

/-- For positive M, distinct nonnegative imbalances give strictly ordered
first-branch certificates. -/
theorem individualMargin_first_branch_gap_strict_mono
    (W M d₁ d₂ : ℝ) (hM : 0 < M)
    (hd₁ : 0 ≤ d₁) (hdd : d₁ < d₂) :
    W - M / (4 * (1 + d₁ ^ 2 / 3)) <
      W - M / (4 * (1 + d₂ ^ 2 / 3)) := by
  have hd₂ : 0 < d₂ := lt_of_le_of_lt hd₁ hdd
  have hsquares : d₁ ^ 2 < d₂ ^ 2 := by
    have hprod : 0 < (d₂ - d₁) * (d₂ + d₁) :=
      mul_pos (sub_pos.mpr hdd) (by linarith)
    nlinarith
  have hden₁ : 0 < 4 * (1 + d₁ ^ 2 / 3) := by positivity
  have hden₂ : 0 < 4 * (1 + d₂ ^ 2 / 3) := by positivity
  have hfrac : M / (4 * (1 + d₂ ^ 2 / 3)) <
      M / (4 * (1 + d₁ ^ 2 / 3)) := by
    apply (div_lt_div_iff₀ hden₂ hden₁).2
    have hcross : 0 < M * (d₂ ^ 2 - d₁ ^ 2) :=
      mul_pos hM (sub_pos.mpr hsquares)
    nlinarith [hcross]
  linarith

/-- For an actual nondegenerate sample, moving strictly away from the
center strictly increases the first-branch formula. -/
theorem individualMargin_first_branch_gap_strict_mono_reduced
    (N m k₁ k₂ : ℕ) (hN : 2 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hkk : k₁ < k₂) (hk₂N : 2 * k₂ ≤ N) :
    individualMarginW N m - individualMarginM N m /
        (4 * (1 + (1 - 2 * (k₂ : ℝ) / (N : ℝ)) ^ 2 / 3)) <
      individualMarginW N m - individualMarginM N m /
        (4 * (1 + (1 - 2 * (k₁ : ℝ) / (N : ℝ)) ^ 2 / 3)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hM : 0 < individualMarginM N m := by
    unfold individualMarginM
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hNm : (0 : ℝ) < ((N - m : ℕ) : ℝ) := by
      exact_mod_cast (Nat.sub_pos_of_lt hmN)
    have hden : 0 < (N : ℝ) - 1 := by
      have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      linarith
    exact div_pos (mul_pos hmR hNm) hden
  have hd₂ : 0 ≤ 1 - 2 * (k₂ : ℝ) / (N : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hNR).2
    norm_num
    exact_mod_cast hk₂N
  have hdk : 1 - 2 * (k₂ : ℝ) / (N : ℝ) <
      1 - 2 * (k₁ : ℝ) / (N : ℝ) := by
    have hkkR : (k₁ : ℝ) < k₂ := by exact_mod_cast hkk
    have hdiv : 2 * (k₁ : ℝ) / (N : ℝ) <
        2 * (k₂ : ℝ) / (N : ℝ) := by
      apply (div_lt_div_iff₀ hNR hNR).2
      have hcross : 0 < ((k₂ : ℝ) - (k₁ : ℝ)) * (N : ℝ) :=
        mul_pos (sub_pos.mpr hkkR) hNR
      nlinarith [hcross]
    linarith
  exact individualMargin_first_branch_gap_strict_mono
    (individualMarginW N m) (individualMarginM N m)
    (1 - 2 * (k₂ : ℝ) / (N : ℝ))
    (1 - 2 * (k₁ : ℝ) / (N : ℝ)) hM hd₂ hdk

/-- On the actual first branch, a strict move towards the center strictly
reduces G; equivalently, a strict increase in imbalance strictly raises G. -/
theorem individualMarginGap_strict_mono_reduced
    (N m k₁ k₂ : ℕ) (hN : 2 ≤ N) (hm : 0 < m) (hmN : m < N)
    (hkk : k₁ < k₂) (hk₂N : 2 * k₂ ≤ N)
    (hbranch : min m (N - m) ≤ k₁) :
    individualMarginGap N k₂ m < individualMarginGap N k₁ m := by
  have hmin₁ : min k₁ (N - k₁) = k₁ := min_eq_left (by omega)
  have hmin₂ : min k₂ (N - k₂) = k₂ := min_eq_left (by omega)
  have hbranch₂ : min m (N - m) ≤ k₂ := hbranch.trans hkk.le
  unfold individualMarginGap
  dsimp only
  rw [hmin₁, hmin₂, if_pos hbranch, if_pos hbranch₂]
  exact individualMargin_first_branch_gap_strict_mono_reduced
    N m k₁ k₂ hN hm hmN hkk hk₂N

end
end ExactHoeffding
