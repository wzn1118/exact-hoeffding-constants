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

namespace ExactHoeffding
noncomputable section

/-- The branchwise certificate in `individualMarginGap` applies directly to the
actual optimal hypergeometric proxy after the population and sample
complement reductions. -/
theorem hypergeomOptimalProxy_le_individualMarginGap
    (N k m : ℕ) (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N)
    (hkc : k ≠ N / 2) (hkc' : k ≠ N - N / 2) :
    hypergeomOptimalProxy N k m ≤
      individualMarginW N m - individualMarginGap N k m := by
  have hcap := hypergeomOptimalProxy_le_individualMargin_cap N k m hN hk hkN
    hm hmN hkc hkc'
  unfold individualMarginGap
  dsimp
  by_cases hbranch :
      (min m (N - m) ≤ min k (N - k))
  · rw [if_pos hbranch] at hcap ⊢
    simpa [individualMarginW, individualMarginM, Nat.cast_sub hkN.le] using hcap
  · rw [if_neg hbranch] at hcap ⊢
    simpa [individualMarginW, individualMarginM, Nat.cast_sub hkN.le] using hcap

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The parity-dependent uniform margin gap from the fixed-sample theorem. -/
def individualMarginDelta (N m : ℕ) : ℝ :=
  if N % 2 = 0 then
    individualMarginM N m / (3 * (N : ℝ) ^ 2 + 4)
  else
    individualMarginM N m * (2 * (N : ℝ) ^ 2 - 3) /
      (4 * (N : ℝ) ^ 2 * ((N : ℝ) ^ 2 + 3))

private theorem individualGap_even_first_algebra (N M d : ℝ)
    (hN : 0 < N) (hM : 0 ≤ M) (hd : 2 / N ≤ d) :
    M / 4 - M / (4 * (1 + d ^ 2 / 3)) ≥ M / (3 * N ^ 2 + 4) := by
  have hd0 : 0 ≤ 2 / N := by positivity
  have hd1 : 0 ≤ d := hd0.trans hd
  have hsq : (2 / N) ^ 2 ≤ d ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hd) (add_nonneg hd1 hd0)
    nlinarith
  have hden0 : 0 < 1 + (2 / N) ^ 2 / 3 := by positivity
  have hden1 : 0 < 1 + d ^ 2 / 3 := by positivity
  have hrecip : 1 / (1 + d ^ 2 / 3) ≤ 1 / (1 + (2 / N) ^ 2 / 3) := by
    apply (div_le_div_iff₀ hden1 hden0).2
    nlinarith
  have hscale : 0 ≤ M / 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hrecip hscale
  have htarget : M / 4 * (1 - 1 / (1 + (2 / N) ^ 2 / 3)) =
      M / (3 * N ^ 2 + 4) := by
    field_simp [ne_of_gt hN]
    ring
  calc
    M / 4 - M / (4 * (1 + d ^ 2 / 3)) =
        M / 4 * (1 - 1 / (1 + d ^ 2 / 3)) := by
        field_simp [ne_of_gt (show 0 < 4 * (1 + d ^ 2 / 3) by positivity)]
        <;> ring
    _ ≥ M / 4 * (1 - 1 / (1 + (2 / N) ^ 2 / 3)) := by linarith
    _ = M / (3 * N ^ 2 + 4) := htarget

private theorem individualGap_odd_first_algebra (N M d : ℝ)
    (hN : 0 < N) (hM : 0 ≤ M) (hd : 3 / N ≤ d) :
    M * (N ^ 2 - 1) / (4 * N ^ 2) - M / (4 * (1 + d ^ 2 / 3)) ≥
      M * (2 * N ^ 2 - 3) / (4 * N ^ 2 * (N ^ 2 + 3)) := by
  have hd0 : 0 ≤ 3 / N := by positivity
  have hd1 : 0 ≤ d := hd0.trans hd
  have hsq : (3 / N) ^ 2 ≤ d ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hd) (add_nonneg hd1 hd0)
    nlinarith
  have hden0 : 0 < 1 + (3 / N) ^ 2 / 3 := by positivity
  have hden1 : 0 < 1 + d ^ 2 / 3 := by positivity
  have hrecip : 1 / (1 + d ^ 2 / 3) ≤ 1 / (1 + (3 / N) ^ 2 / 3) := by
    apply (div_le_div_iff₀ hden1 hden0).2
    nlinarith
  have hscale : 0 ≤ M / 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hrecip hscale
  have htarget : M * (N ^ 2 - 1) / (4 * N ^ 2) -
      M / 4 * (1 / (1 + (3 / N) ^ 2 / 3)) =
      M * (2 * N ^ 2 - 3) / (4 * N ^ 2 * (N ^ 2 + 3)) := by
    field_simp [ne_of_gt hN]
    ring
  calc
    M * (N ^ 2 - 1) / (4 * N ^ 2) - M / (4 * (1 + d ^ 2 / 3)) =
        M * (N ^ 2 - 1) / (4 * N ^ 2) - M / 4 *
          (1 / (1 + d ^ 2 / 3)) := by
            field_simp [ne_of_gt (show 0 < 4 * (1 + d ^ 2 / 3) by positivity)]
            <;> ring
    _ ≥ M * (N ^ 2 - 1) / (4 * N ^ 2) - M / 4 *
          (1 / (1 + (3 / N) ^ 2 / 3)) := by linarith
    _ = M * (2 * N ^ 2 - 3) / (4 * N ^ 2 * (N ^ 2 + 3)) := htarget

private theorem individualGap_even_second_algebra
    (N M Pm Pk : ℝ) (hN : 1 < N) (hM : 0 ≤ M)
    (hMbound : M ≤ N ^ 2 / (4 * (N - 1)))
    (hMrepr : M = Pm / (N - 1)) (hprod : 1 ≤ Pm - Pk) :
    M / 4 - Pk / (4 * (N - 1)) ≥ M / (3 * N ^ 2 + 4) := by
  have hNm1 : 0 < N - 1 := by linarith
  have hden : 0 < 3 * N ^ 2 + 4 := by positivity
  have hN2 : 0 < N ^ 2 := by positivity
  have hsimple : 1 / (4 * (N - 1)) ≥ M / (3 * N ^ 2 + 4) := by
    change M / (3 * N ^ 2 + 4) ≤ 1 / (4 * (N - 1))
    have hMscaled : M * (4 * (N - 1)) ≤ N ^ 2 :=
      (le_div_iff₀ (by positivity : 0 < 4 * (N - 1))).1 hMbound
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * N ^ 2 + 4)
      (by positivity : 0 < 4 * (N - 1))).2
    nlinarith [hMscaled, sq_nonneg N]
  have hgap : M / 4 - Pk / (4 * (N - 1)) =
      (Pm - Pk) / (4 * (N - 1)) := by
    rw [hMrepr]
    field_simp [ne_of_gt hNm1]
  rw [hgap]
  have hprod' : 1 / (4 * (N - 1)) ≤ (Pm - Pk) / (4 * (N - 1)) := by
    exact div_le_div_of_nonneg_right hprod (by positivity)
  exact hsimple.trans hprod'

private theorem individualGap_odd_second_algebra
    (N M Pm Pk : ℝ) (hN : 2 ≤ N) (hM : 0 ≤ M)
    (hMbound : M ≤ N ^ 2 / (4 * (N - 1)))
    (hMrepr : M = Pm / (N - 1)) (hprod : 2 ≤ Pm - Pk) :
    M * (N ^ 2 - 1) / (4 * N ^ 2) - Pk / (4 * (N - 1)) ≥
      M * (2 * N ^ 2 - 3) / (4 * N ^ 2 * (N ^ 2 + 3)) := by
  have hNm1 : 0 < N - 1 := by linarith
  have hN2 : 0 < N ^ 2 := by positivity
  have hden : 0 < 4 * N ^ 2 * (N ^ 2 + 3) := by positivity
  have hdelta : M * (2 * N ^ 2 - 3) / (4 * N ^ 2 * (N ^ 2 + 3)) ≤
      1 / (8 * (N - 1)) := by
    have hMscaled : M * (4 * (N - 1)) ≤ N ^ 2 :=
      (le_div_iff₀ (by positivity : 0 < 4 * (N - 1))).1 hMbound
    have hfac : 0 ≤ 2 * N ^ 2 - 3 := by nlinarith [sq_nonneg N]
    have hMscaled' := mul_le_mul_of_nonneg_right hMscaled hfac
    apply (div_le_div_iff₀ hden (by positivity : 0 < 8 * (N - 1))).2
    nlinarith [hMscaled']
  have hgap : M * (N ^ 2 - 1) / (4 * N ^ 2) - Pk / (4 * (N - 1)) =
      (Pm - Pk - Pm / N ^ 2) / (4 * (N - 1)) := by
    rw [hMrepr]
    field_simp [ne_of_gt hNm1, ne_of_gt hN2]
    ring
  rw [hgap]
  have hpm : Pm / N ^ 2 ≤ 1 / 4 := by
    have hreprbound : Pm / (N - 1) ≤ (N ^ 2 / 4) / (N - 1) := by
      rw [← hMrepr]
      calc
        M ≤ N ^ 2 / (4 * (N - 1)) := hMbound
        _ = (N ^ 2 / 4) / (N - 1) := by
          field_simp [ne_of_gt hNm1]
    have hPm : Pm ≤ N ^ 2 / 4 := by
      have hcross := (div_le_div_iff₀ hNm1 hNm1).1 hreprbound
      exact (mul_le_mul_iff_of_pos_right hNm1).1 hcross
    apply (div_le_iff₀ hN2).2
    nlinarith [hPm]
  have hgap' : 7 / (16 * (N - 1)) ≤
      (Pm - Pk - Pm / N ^ 2) / (4 * (N - 1)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 16 * (N - 1))
      (by positivity : 0 < 4 * (N - 1))).2
    nlinarith [hprod, hpm]
  have hsmall : 1 / (8 * (N - 1)) ≤ 7 / (16 * (N - 1)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * (N - 1))
      (by positivity : 0 < 16 * (N - 1))).2
    nlinarith [hNm1]
  exact hdelta.trans (hsmall.trans hgap')

/-- The full noncentral individual-margin gap dominates the paper's
parity-dependent uniform gap, in both branches and for every admissible sample
and success count. -/
theorem individualMarginGap_ge_parityDelta_all
    (N k m : ℕ) (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N)
    (hkc : k ≠ N / 2) (hkc' : k ≠ N - N / 2) :
    individualMarginGap N k m ≥ individualMarginDelta N m := by
  let kb := min k (N - k)
  let mb := min m (N - m)
  have hkbData := individualMargin_sample_reduced N k hk hkN
  have hmbData := individualMargin_sample_reduced N m hm hmN
  have hcenter := individualMargin_center_reduced N k hk hkN hkc hkc'
  have hMnonneg : 0 ≤ individualMarginM N m := by
    unfold individualMarginM
    rw [Nat.cast_sub hmN.le]
    have hden : 0 < (N : ℝ) - 1 := by
      have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
      linarith
    have hmNreal : (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hmN.le
    apply div_nonneg
    · exact mul_nonneg (by positivity) (sub_nonneg.mpr hmNreal)
    · exact le_of_lt hden
  have hMreduce : individualMarginM N mb = individualMarginM N m :=
    individualMarginM_reduce_sample N m hmN.le
  have hMbound : individualMarginM N m ≤
      (N : ℝ) ^ 2 / (4 * ((N : ℝ) - 1)) := by
    have hden : 0 < (N : ℝ) - 1 := by
      have : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
      linarith
    have hprod : (m : ℝ) * ((N : ℝ) - m) ≤ (N : ℝ) ^ 2 / 4 := by
      nlinarith [sq_nonneg ((m : ℝ) - (N : ℝ) / 2)]
    unfold individualMarginM
    rw [Nat.cast_sub hmN.le]
    field_simp [ne_of_gt hden]
    nlinarith
  have hMrepr : individualMarginM N m =
      (mb : ℝ) * ((N - mb : ℕ) : ℝ) / ((N : ℝ) - 1) := by
    rw [← hMreduce]
    unfold individualMarginM
    rw [Nat.cast_sub (by omega : mb ≤ N)]
  let Pm : ℝ := (mb : ℝ) * ((N - mb : ℕ) : ℝ)
  let Pk : ℝ := (kb : ℝ) * ((N - kb : ℕ) : ℝ)
  have hMrepr' : individualMarginM N m = Pm / ((N : ℝ) - 1) := by
    simpa [Pm] using hMrepr
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' N
  · subst N
    have hqpos : 0 < q := by omega
    have hNreal : (0 : ℝ) < (2 * q : ℕ) := by exact_mod_cast (by omega : 0 < 2 * q)
    have hmod : (2 * q) % 2 = 0 := by omega
    have hkb_lt : kb < q := by omega
    have hmb_le : mb ≤ q := by omega
    have hMscale : 0 ≤ individualMarginM (2 * q) m := hMnonneg
    have hW : individualMarginW (2 * q) m =
        individualMarginM (2 * q) m / 4 := by
      unfold individualMarginW
      have hhalf : (2 * q) / 2 = q := by omega
      have hcompl : 2 * q - q = q := by omega
      rw [hhalf, hcompl]
      push_cast
      field_simp [ne_of_gt hNreal]
      ring
    have hNbound : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) - (mb : ℝ) - (kb : ℝ) := by
      have hNat : 1 ≤ 2 * q - mb - kb := by omega
      have hcast : ((2 * q - mb - kb : ℕ) : ℝ) =
          ((2 * q : ℕ) : ℝ) - (mb : ℝ) - (kb : ℝ) := by
        rw [Nat.cast_sub (by omega : kb ≤ 2 * q - mb),
          Nat.cast_sub (by omega : mb ≤ 2 * q)]
      rw [← hcast]
      exact_mod_cast hNat
    by_cases hbranch : mb ≤ kb
    · have hdelta : individualMarginDelta (2 * q) m =
          individualMarginM (2 * q) m /
            (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4) := by
        simp [individualMarginDelta, hmod]
      have hd : 2 / ((2 * q : ℕ) : ℝ) ≤
          1 - 2 * (kb : ℝ) / ((2 * q : ℕ) : ℝ) := by
        apply (div_le_iff₀ hNreal).2
        have hNat : 2 * kb + 2 ≤ 2 * q := by omega
        have hNatR : (2 : ℝ) * (kb : ℝ) + 2 ≤ ((2 * q : ℕ) : ℝ) := by
          exact_mod_cast hNat
        field_simp [ne_of_gt hNreal]
        nlinarith
      have hfirst := individualGap_even_first_algebra
        ((2 * q : ℕ) : ℝ) (individualMarginM (2 * q) m)
        (1 - 2 * (kb : ℝ) / ((2 * q : ℕ) : ℝ)) hNreal hMscale hd
      have hgoal : individualMarginW (2 * q) m -
          individualMarginM (2 * q) m /
            (4 * (1 + (1 - 2 * (kb : ℝ) / ((2 * q : ℕ) : ℝ)) ^ 2 / 3)) ≥
          individualMarginDelta (2 * q) m := by
        rw [hW, hdelta]
        exact hfirst
      simpa [individualMarginGap, kb, mb, hbranch] using hgoal
    · have hdiff : 1 ≤ (mb : ℝ) - (kb : ℝ) := by
        have hNat : kb + 1 ≤ mb := by omega
        have hcast : ((mb - kb : ℕ) : ℝ) = (mb : ℝ) - (kb : ℝ) := by
          rw [Nat.cast_sub (by omega : kb ≤ mb)]
        rw [← hcast]
        exact_mod_cast (show 1 ≤ mb - kb by omega)
      have hid : Pm - Pk = ((mb : ℝ) - (kb : ℝ)) *
          (((2 * q : ℕ) : ℝ) - (mb : ℝ) - (kb : ℝ)) := by
        dsimp [Pm, Pk]
        rw [Nat.cast_sub (by omega : mb ≤ 2 * q),
          Nat.cast_sub (by omega : kb ≤ 2 * q)]
        push_cast
        ring
      have hprod : 1 ≤ Pm - Pk := by
        rw [hid]
        have hmul := mul_le_mul hdiff hNbound (by norm_num)
          (by linarith : 0 ≤ (mb : ℝ) - (kb : ℝ))
        nlinarith [hmul]
      have hsecond := individualGap_even_second_algebra
        ((2 * q : ℕ) : ℝ) (individualMarginM (2 * q) m) Pm Pk
        (by exact_mod_cast (show 1 < 2 * q by omega)) hMscale
        (by simpa using hMbound) hMrepr' hprod
      have hdelta : individualMarginDelta (2 * q) m =
          individualMarginM (2 * q) m /
            (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4) := by
        simp [individualMarginDelta, hmod]
      have hgoal : individualMarginW (2 * q) m -
          (kb : ℝ) * ((2 * q - kb : ℕ) : ℝ) /
            (4 * (((2 * q : ℕ) : ℝ) - 1)) ≥
          individualMarginDelta (2 * q) m := by
        rw [hW, hdelta]
        have hPkcast : Pk = (kb : ℝ) * ((2 * q - kb : ℕ) : ℝ) := by rfl
        rw [← hPkcast]
        exact hsecond
      simpa [individualMarginGap, kb, mb, hbranch] using hgoal
  · subst N
    have hqpos : 0 < q := by omega
    have hNreal : (0 : ℝ) < (2 * q + 1 : ℕ) := by exact_mod_cast (by omega : 0 < 2 * q + 1)
    have hmod : (2 * q + 1) % 2 = 1 := by omega
    have hkb_le : kb ≤ q := by omega
    have hkb_lt : kb < q := by
      by_contra hnot
      have hEq : kb = q := by omega
      dsimp [kb] at hEq
      by_cases hkle : k ≤ 2 * q + 1 - k
      · rw [Nat.min_eq_left hkle] at hEq
        have hcenter : k = (2 * q + 1) / 2 := by omega
        exact hkc hcenter
      · have hkle' : 2 * q + 1 - k ≤ k := by omega
        rw [Nat.min_eq_right hkle'] at hEq
        have hcenter : k = (2 * q + 1) - (2 * q + 1) / 2 := by omega
        exact hkc' hcenter
    have hmb_le : mb ≤ q := by omega
    have hMscale : 0 ≤ individualMarginM (2 * q + 1) m := hMnonneg
    have hW : individualMarginW (2 * q + 1) m =
        individualMarginM (2 * q + 1) m *
          (((2 * q + 1 : ℕ) : ℝ) ^ 2 - 1) /
            (4 * ((2 * q + 1 : ℕ) : ℝ) ^ 2) := by
      unfold individualMarginW
      have hhalf : (2 * q + 1) / 2 = q := by omega
      have hcompl : 2 * q + 1 - q = q + 1 := by omega
      rw [hhalf, hcompl]
      push_cast
      field_simp [ne_of_gt hNreal]
      <;> ring
    have hNbound : (2 : ℝ) ≤ ((2 * q + 1 : ℕ) : ℝ) - (mb : ℝ) - (kb : ℝ) := by
      have hNat : 2 ≤ 2 * q + 1 - mb - kb := by omega
      have hcast : ((2 * q + 1 - mb - kb : ℕ) : ℝ) =
          ((2 * q + 1 : ℕ) : ℝ) - (mb : ℝ) - (kb : ℝ) := by
        rw [Nat.cast_sub (by omega : kb ≤ 2 * q + 1 - mb),
          Nat.cast_sub (by omega : mb ≤ 2 * q + 1)]
      rw [← hcast]
      exact_mod_cast hNat
    by_cases hbranch : mb ≤ kb
    · have hdelta : individualMarginDelta (2 * q + 1) m =
          individualMarginM (2 * q + 1) m *
            (2 * ((2 * q + 1 : ℕ) : ℝ) ^ 2 - 3) /
              (4 * ((2 * q + 1 : ℕ) : ℝ) ^ 2 *
                (((2 * q + 1 : ℕ) : ℝ) ^ 2 + 3)) := by
        simp [individualMarginDelta, hmod]
      have hd : 3 / ((2 * q + 1 : ℕ) : ℝ) ≤
          1 - 2 * (kb : ℝ) / ((2 * q + 1 : ℕ) : ℝ) := by
        apply (div_le_iff₀ hNreal).2
        have hNat : 2 * kb + 3 ≤ 2 * q + 1 := by omega
        have hNatR : (2 : ℝ) * (kb : ℝ) + 3 ≤ ((2 * q + 1 : ℕ) : ℝ) := by
          exact_mod_cast hNat
        field_simp [ne_of_gt hNreal]
        nlinarith
      have hfirst := individualGap_odd_first_algebra
        ((2 * q + 1 : ℕ) : ℝ) (individualMarginM (2 * q + 1) m)
        (1 - 2 * (kb : ℝ) / ((2 * q + 1 : ℕ) : ℝ)) hNreal hMscale hd
      have hgoal : individualMarginW (2 * q + 1) m -
          individualMarginM (2 * q + 1) m /
            (4 * (1 + (1 - 2 * (kb : ℝ) / ((2 * q + 1 : ℕ) : ℝ)) ^ 2 / 3)) ≥
          individualMarginDelta (2 * q + 1) m := by
        rw [hW, hdelta]
        exact hfirst
      simpa [individualMarginGap, kb, mb, hbranch] using hgoal
    · have hdiff : 1 ≤ (mb : ℝ) - (kb : ℝ) := by
        have hNat : kb + 1 ≤ mb := by omega
        have hcast : ((mb - kb : ℕ) : ℝ) = (mb : ℝ) - (kb : ℝ) := by
          rw [Nat.cast_sub (by omega : kb ≤ mb)]
        rw [← hcast]
        exact_mod_cast (show 1 ≤ mb - kb by omega)
      have hid : Pm - Pk = ((mb : ℝ) - (kb : ℝ)) *
          (((2 * q + 1 : ℕ) : ℝ) - (mb : ℝ) - (kb : ℝ)) := by
        dsimp [Pm, Pk]
        rw [Nat.cast_sub (by omega : mb ≤ 2 * q + 1),
          Nat.cast_sub (by omega : kb ≤ 2 * q + 1)]
        push_cast
        ring
      have hprod : 2 ≤ Pm - Pk := by
        rw [hid]
        have hdiff2 : 1 ≤ (mb : ℝ) - (kb : ℝ) := hdiff
        have hmul := mul_le_mul hdiff2 hNbound (by norm_num)
          (by linarith : 0 ≤ (mb : ℝ) - (kb : ℝ))
        nlinarith [hmul]
      have hsecond := individualGap_odd_second_algebra
        ((2 * q + 1 : ℕ) : ℝ) (individualMarginM (2 * q + 1) m) Pm Pk
        (by exact_mod_cast (show 2 ≤ 2 * q + 1 by omega)) hMscale
        (by simpa using hMbound) hMrepr' hprod
      have hdelta : individualMarginDelta (2 * q + 1) m =
          individualMarginM (2 * q + 1) m *
            (2 * ((2 * q + 1 : ℕ) : ℝ) ^ 2 - 3) /
              (4 * ((2 * q + 1 : ℕ) : ℝ) ^ 2 *
                (((2 * q + 1 : ℕ) : ℝ) ^ 2 + 3)) := by
        simp [individualMarginDelta, hmod]
      have hgoal : individualMarginW (2 * q + 1) m -
          (kb : ℝ) * ((2 * q + 1 - kb : ℕ) : ℝ) /
            (4 * (((2 * q + 1 : ℕ) : ℝ) - 1)) ≥
          individualMarginDelta (2 * q + 1) m := by
        rw [hW, hdelta]
        have hPkcast : Pk = (kb : ℝ) * ((2 * q + 1 - kb : ℕ) : ℝ) := by rfl
        rw [← hPkcast]
        exact hsecond
      simpa [individualMarginGap, kb, mb, hbranch] using hgoal

end
end ExactHoeffding
