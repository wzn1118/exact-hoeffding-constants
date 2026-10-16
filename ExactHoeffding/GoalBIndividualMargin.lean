import ExactHoeffding.GoalBFixedSample

namespace ExactHoeffding
noncomputable section

/-- The finite-sample scale appearing in the individual-margin certificate. -/
def individualMarginM (N m : ℕ) : ℝ :=
  (m : ℝ) * ((N - m : ℕ) : ℝ) / ((N : ℝ) - 1)

/-- The ordinary variance at the closest-to-balanced population margin. -/
def individualMarginW (N m : ℕ) : ℝ :=
  individualMarginM N m *
    ((N / 2 : ℕ) : ℝ) * ((N - N / 2 : ℕ) : ℝ) / (N : ℝ) ^ 2

/-- The exact two-branch gap in Proposition `individual`. -/
def individualMarginGap (N k m : ℕ) : ℝ :=
  let kb := min k (N - k)
  let mb := min m (N - m)
  let d := 1 - 2 * (kb : ℝ) / (N : ℝ)
  let W := individualMarginW N m
  let M := individualMarginM N m
  if mb ≤ kb then
    W - M / (4 * (1 + d ^ 2 / 3))
  else
    W - (kb : ℝ) * ((N - kb : ℕ) : ℝ) /
      (4 * ((N : ℝ) - 1))

/-- Reduced first-branch Bernoulli comparison, before the cubic scalar cap. -/
theorem normalizedHypergeomProxy_reduced_le_bernoulli
    (N k m : ℕ) (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmk : m ≤ k) (hkhalf : 2 * k < N) :
    normalizedHypergeomProxy N k m ≤
      (N : ℝ) / ((N : ℝ) - 1) *
        imbalanceFactor (1 - 2 * (k : ℝ) / (N : ℝ)) := by
  by_cases hm1 : m = 1
  · subst m
    rw [normalizedHypergeomProxy_singleton_subhalf N k hk hkhalf]
  · have hm2 : 2 ≤ m := by omega
    exact (normalizedHypergeomProxy_inner_lt_bernoulli N k m hm2 hmk hkhalf).le

/-- The first branch of the individual-margin certificate bounds the actual
optimal proxy for every reduced off-center margin. -/
theorem hypergeomOptimalProxy_reduced_first_branch
    (N k m : ℕ) (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N) (hmk : m ≤ k) (hkhalf : 2 * k < N) :
    hypergeomOptimalProxy N k m ≤
      individualMarginM N m /
        (4 * (1 + (1 - 2 * (k : ℝ) / (N : ℝ)) ^ 2 / 3)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNmR : (0 : ℝ) < (N : ℝ) - m := by
    exact sub_pos.mpr (by exact_mod_cast hmN)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hd0 : (0 : ℝ) < 1 - 2 * (k : ℝ) / (N : ℝ) := by
    apply sub_pos.mpr
    rw [div_lt_one hNR]
    exact_mod_cast hkhalf
  have hd1 : 1 - 2 * (k : ℝ) / (N : ℝ) < 1 := by
    have : 0 < 2 * (k : ℝ) / (N : ℝ) := by positivity
    linarith
  have hnorm := normalizedHypergeomProxy_reduced_le_bernoulli N k m hN hk hkN
    hm hmk hkhalf
  have hfactor := imbalanceFactor_cubic_upper
    (1 - 2 * (k : ℝ) / (N : ℝ)) hd0 hd1
  have hscale : 0 ≤ (m : ℝ) * ((N : ℝ) - m) / (4 * (N : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hnorm hscale
  unfold normalizedHypergeomProxy at hmul
  have hcancel :
      (m : ℝ) * ((N : ℝ) - m) / (4 * (N : ℝ)) *
        (4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) = 1 := by
    field_simp [ne_of_gt hNR, ne_of_gt hmR, ne_of_gt hNmR]
  rw [← mul_assoc, hcancel, one_mul] at hmul
  have hright :
      (m : ℝ) * ((N : ℝ) - m) / (4 * (N : ℝ)) *
        ((N : ℝ) / ((N : ℝ) - 1) *
          (1 / (1 + (1 - 2 * (k : ℝ) / (N : ℝ)) ^ 2 / 3))) =
      individualMarginM N m /
        (4 * (1 + (1 - 2 * (k : ℝ) / (N : ℝ)) ^ 2 / 3)) := by
    unfold individualMarginM
    rw [Nat.cast_sub hmN.le]
    field_simp [ne_of_gt hNR, ne_of_gt hN1, ne_of_gt hmR, ne_of_gt hNmR]
  have hfactorScaled := mul_le_mul_of_nonneg_left hfactor
    (by positivity : 0 ≤ (N : ℝ) / ((N : ℝ) - 1))
  have hmul' := hmul.trans
    (mul_le_mul_of_nonneg_left hfactorScaled hscale)
  rw [hright] at hmul'
  exact hmul'

/-- The second branch is the curvature certificate after reducing both margins. -/
theorem hypergeomOptimalProxy_reduced_second_branch
    (N k m : ℕ) (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N)
    (hkh : 2 * k ≤ N) (hmh : 2 * m ≤ N) (hkm : k < m) :
    hypergeomOptimalProxy N k m ≤
      (k : ℝ) * ((N - k : ℕ) : ℝ) /
        (4 * ((N : ℝ) - 1)) := by
  have hcurv := hypergeomOptimalProxy_le_curvature N k m hkN.le hmN.le
  unfold sharpCurvatureConstant at hcurv
  have hprod : (k : ℝ) * ((N : ℝ) - k) ≤
      (m : ℝ) * ((N : ℝ) - m) := by
    have hkR : (k : ℝ) < m := by exact_mod_cast hkm
    have hNkR : (0 : ℝ) ≤ (N : ℝ) - k - m := by
      have hkNhalf : k ≤ N / 2 := by omega
      have hmNhalf : m ≤ N / 2 := by omega
      have hsumR : (k : ℝ) + (m : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (show k + m ≤ N by omega)
      linarith
    have hNmK : (0 : ℝ) ≤ (N : ℝ) - m - k := by
      have hsumR : (k : ℝ) + (m : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (show k + m ≤ N by omega)
      linarith
    have hnonneg : 0 ≤ ((m : ℝ) - k) * ((N : ℝ) - m - k) :=
      mul_nonneg (by linarith) hNmK
    have hid :
        (m : ℝ) * ((N : ℝ) - m) - (k : ℝ) * ((N : ℝ) - k) =
          ((m : ℝ) - k) * ((N : ℝ) - m - k) := by ring
    nlinarith [hid, hnonneg]
  have hcurv' : hypergeomOptimalProxy N k m ≤
      (k : ℝ) * ((N : ℝ) - k) / (4 * ((N : ℝ) - 1)) := by
    rw [min_eq_left hprod] at hcurv
    exact hcurv
  simpa [Nat.cast_sub hkN.le] using hcurv'

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

private theorem hypergeomOptimalProxy_reduce_min_margins (N k m : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomOptimalProxy N k m =
      hypergeomOptimalProxy N (min k (N - k)) (min m (N - m)) := by
  by_cases hkl : k ≤ N - k
  · by_cases hml : m ≤ N - m
    · simp [min_eq_left hkl, min_eq_left hml]
    · have hmc := hypergeomOptimalProxy_sample_complement N k m hk hm hN
      have hml' : N - m ≤ m := by omega
      simpa [min_eq_left hkl, min_eq_right hml'] using hmc
  · have hkl' : N - k ≤ k := by omega
    by_cases hml : m ≤ N - m
    · have hkc := hypergeomOptimalProxy_success_complement N k m hk hm hN
      have hml' : m = min m (N - m) := by simp [min_eq_left hml]
      simpa [min_eq_right hkl', min_eq_left hml] using hkc
    · have hkc := hypergeomOptimalProxy_success_complement N k m hk hm hN
      have hsc := hypergeomOptimalProxy_sample_complement N (N - k) m
        (Nat.sub_le _ _) hm hN
      have hml' : N - m ≤ m := by omega
      simpa [min_eq_right hkl', min_eq_right hml'] using hkc.trans hsc

private theorem individualMarginM_reduce_sample (N m : ℕ)
    (hm : m ≤ N) : individualMarginM N (min m (N - m)) = individualMarginM N m := by
  by_cases hml : m ≤ N - m
  · simp [min_eq_left hml]
  · have hml' : N - m ≤ m := by omega
    simp [min_eq_right hml', individualMarginM, Nat.sub_sub_self hm]
    ring

private theorem individualMargin_center_reduced (N k : ℕ)
    (hk : 0 < k) (hkN : k < N)
    (hkc : k ≠ N / 2) (hkc' : k ≠ N - N / 2) :
    2 * min k (N - k) < N := by
  by_cases hkl : k ≤ N - k
  · simp [min_eq_left hkl]
    by_contra h
    have heq : 2 * k = N := by omega
    have : k = N / 2 := by omega
    exact hkc this
  · have hkl' : N - k ≤ k := by omega
    simp [min_eq_right hkl']
    by_contra h
    have heq : 2 * (N - k) = N := by omega
    have : k = N - N / 2 := by omega
    exact hkc' this

private theorem individualMargin_sample_reduced (N m : ℕ)
    (hm : 0 < m) (hmN : m < N) :
    0 < min m (N - m) ∧ min m (N - m) < N ∧
      2 * min m (N - m) ≤ N := by
  have hleft : 0 < m := hm
  have hright : 0 < N - m := by omega
  have hminpos : 0 < min m (N - m) := by omega
  have hminN : min m (N - m) < N :=
    lt_of_le_of_lt (min_le_left _ _) hmN
  have hminhalf : 2 * min m (N - m) ≤ N := by
    by_cases hml : m ≤ N - m
    · simp [min_eq_left hml]
      omega
    · have hml' : N - m ≤ m := by omega
      simp [min_eq_right hml']
      omega
  exact ⟨hminpos, hminN, hminhalf⟩

/-- The actual optimal proxy obeys the exact two-branch certificate used to
state the individual-margin proposition, after both complement reductions. -/
theorem hypergeomOptimalProxy_le_individualMargin_cap
    (N k m : ℕ) (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N)
    (hkc : k ≠ N / 2) (hkc' : k ≠ N - N / 2) :
    hypergeomOptimalProxy N k m ≤
      if min m (N - m) ≤ min k (N - k) then
        individualMarginM N m /
          (4 * (1 + (1 - 2 * (min k (N - k) : ℝ) / (N : ℝ)) ^ 2 / 3))
      else
        (min k (N - k) : ℝ) *
            ((N - min k (N - k) : ℕ) : ℝ) /
          (4 * ((N : ℝ) - 1)) := by
  let kb := min k (N - k)
  let mb := min m (N - m)
  have hN0 : 0 < N := by omega
  have hkb0 : 0 < kb := by
    dsimp [kb]
    exact (individualMargin_sample_reduced N k hk hkN).1
  have hkbN : kb < N := by
    dsimp [kb]
    exact (individualMargin_sample_reduced N k hk hkN).2.1
  have hmbData := individualMargin_sample_reduced N m hm hmN
  have hmb0 : 0 < mb := hmbData.1
  have hmbN : mb < N := hmbData.2.1
  have hkbhalf : 2 * kb < N := by
    dsimp [kb]
    exact individualMargin_center_reduced N k hk hkN hkc hkc'
  have hred := hypergeomOptimalProxy_reduce_min_margins N k m hN0 hkN.le hmN.le
  by_cases hbranch : mb ≤ kb
  · have hfirst := hypergeomOptimalProxy_reduced_first_branch N kb mb hN hkb0 hkbN
      hmb0 hmbN hbranch hkbhalf
    have hM := individualMarginM_reduce_sample N m hmN.le
    rw [hred]
    dsimp [kb, mb] at hfirst ⊢
    rw [if_pos hbranch]
    rw [hM] at hfirst
    simpa [Nat.cast_min, Nat.cast_sub hkN.le] using hfirst
  · have hkm : kb < mb := by omega
    have hsecond := hypergeomOptimalProxy_reduced_second_branch N kb mb hN
      hkb0 hkbN hmb0 hmbN hkbhalf.le hmbData.2.2 hkm
    rw [hred]
    dsimp [kb, mb] at hsecond ⊢
    rw [if_neg (by omega)]
    simpa [Nat.cast_min, Nat.cast_sub hkN.le] using hsecond

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

private theorem one_div_cubic_denom_antitone (d₁ d₂ : ℝ)
    (hd₁ : 0 ≤ d₁) (hdd : d₁ ≤ d₂) :
    1 / (1 + d₂ ^ 2 / 3) ≤ 1 / (1 + d₁ ^ 2 / 3) := by
  have hd₂ : 0 ≤ d₂ := hd₁.trans hdd
  have hsquares : d₁ ^ 2 ≤ d₂ ^ 2 := by
    have hprod : 0 ≤ (d₂ - d₁) * (d₂ + d₁) :=
      mul_nonneg (sub_nonneg.mpr hdd) (add_nonneg hd₂ hd₁)
    nlinarith
  have hden₁ : 0 < 1 + d₁ ^ 2 / 3 := by positivity
  have hden₂ : 0 < 1 + d₂ ^ 2 / 3 := by positivity
  apply (div_le_div_iff₀ hden₂ hden₁).2
  nlinarith

/-- The first branch of `G` is monotone in the reduced imbalance. -/
theorem individualMargin_first_branch_gap_mono
    (W M d₁ d₂ : ℝ) (hM : 0 ≤ M)
    (hd₁ : 0 ≤ d₁) (hdd : d₁ ≤ d₂) :
    W - M / (4 * (1 + d₁ ^ 2 / 3)) ≤
      W - M / (4 * (1 + d₂ ^ 2 / 3)) := by
  have hinv := one_div_cubic_denom_antitone d₁ d₂ hd₁ hdd
  have hmul := mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ M / 4)
  have hden₁ : 0 < 1 + d₁ ^ 2 / 3 := by positivity
  have hden₂ : 0 < 1 + d₂ ^ 2 / 3 := by positivity
  have heq₁ : M / (4 * (1 + d₁ ^ 2 / 3)) =
      M / 4 * (1 / (1 + d₁ ^ 2 / 3)) := by
    field_simp [ne_of_gt hden₁]
  have heq₂ : M / (4 * (1 + d₂ ^ 2 / 3)) =
      M / 4 * (1 / (1 + d₂ ^ 2 / 3)) := by
    field_simp [ne_of_gt hden₂]
  rw [heq₁, heq₂]
  linarith

/-- In the reduced half-margin, moving away from the center increases the
first-branch certificate. -/
theorem individualMargin_first_branch_gap_mono_reduced
    (N m k₁ k₂ : ℕ) (hN : 0 < N) (hm : 0 < m) (hmN : m < N)
    (hk₁ : 0 < k₁) (hkk : k₁ ≤ k₂) (hk₂N : 2 * k₂ < N) :
    individualMarginW N m - individualMarginM N m /
        (4 * (1 + (1 - 2 * (k₂ : ℝ) / (N : ℝ)) ^ 2 / 3)) ≤
      individualMarginW N m - individualMarginM N m /
        (4 * (1 + (1 - 2 * (k₁ : ℝ) / (N : ℝ)) ^ 2 / 3)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hd₂ : 0 ≤ 1 - 2 * (k₂ : ℝ) / (N : ℝ) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hNR).2
    norm_num
    exact_mod_cast (show 2 * k₂ ≤ N by omega)
  have hdk :
      1 - 2 * (k₂ : ℝ) / (N : ℝ) ≤
        1 - 2 * (k₁ : ℝ) / (N : ℝ) := by
    have hkkR : (k₁ : ℝ) ≤ k₂ := by exact_mod_cast hkk
    have hdiv : 2 * (k₁ : ℝ) / (N : ℝ) ≤
        2 * (k₂ : ℝ) / (N : ℝ) := by
      apply (div_le_div_iff₀ hNR hNR).2
      nlinarith
    linarith
  have hM : 0 ≤ individualMarginM N m := by
    unfold individualMarginM
    have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by
      have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
      linarith
    positivity
  have hmono := individualMargin_first_branch_gap_mono
    (individualMarginW N m) (individualMarginM N m)
    (1 - 2 * (k₂ : ℝ) / (N : ℝ))
    (1 - 2 * (k₁ : ℝ) / (N : ℝ)) hM hd₂ hdk
  exact hmono

end
end ExactHoeffding
