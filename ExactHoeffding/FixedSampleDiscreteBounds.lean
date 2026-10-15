import ExactHoeffding.OddHypergeomExtremizers
import ExactHoeffding.ZeroTiltMoments

/-! # Discrete bounds uniform over the success count at fixed sample size -/

namespace ExactHoeffding
noncomputable section

/-- Singleton normalized proxies increase towards half success. -/
theorem normalizedHypergeomProxy_singleton_mono_subhalf (N k l : ℕ)
    (hk : 0 < k) (hkl : k ≤ l) (hlhalf : 2 * l < N) :
    normalizedHypergeomProxy N k 1 ≤ normalizedHypergeomProxy N l 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlR : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hklR : (k : ℝ) ≤ l := by exact_mod_cast hkl
  have hhalfR : 2 * (l : ℝ) < N := by exact_mod_cast hlhalf
  have hdlo : 0 < 1 - 2 * (l : ℝ) / N := by
    have := (div_lt_one hN).mpr hhalfR
    linarith
  have hdhi : 1 - 2 * (k : ℝ) / N < 1 := by
    have : 0 < 2 * (k : ℝ) / N := by positivity
    linarith
  have hdd : 1 - 2 * (l : ℝ) / N ≤ 1 - 2 * (k : ℝ) / N := by
    exact sub_le_sub_left ((div_le_div_iff_of_pos_right hN).mpr (by linarith)) 1
  rw [normalizedHypergeomProxy_singleton_subhalf N k hk (by omega),
    normalizedHypergeomProxy_singleton_subhalf N l (by omega) hlhalf]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact imbalanceFactor_strictAnti.antitoneOn ⟨hdlo, lt_of_le_of_lt hdd hdhi⟩
    ⟨lt_of_lt_of_le hdlo hdd, hdhi⟩ hdd

/-- Every noncentral success count in the canonical interior is uniformly
below the singleton law at the nearest noncentral success count. -/
theorem odd_normalized_proxy_interior_lt_offcenter_singleton (n k m : ℕ)
    (hm : 2 ≤ m) (hmk : m ≤ k) (hkn : k < n) :
    normalizedHypergeomProxy (2 * n + 1) k m <
      normalizedHypergeomProxy (2 * n + 1) (n - 1) 1 := by
  have hinner := normalizedHypergeomProxy_inner_lt_bernoulli
    (2 * n + 1) k m hm hmk (by omega)
  rw [← normalizedHypergeomProxy_singleton_subhalf (2 * n + 1) k
    (by omega) (by omega)] at hinner
  exact hinner.trans_le (normalizedHypergeomProxy_singleton_mono_subhalf
    (2 * n + 1) k (n - 1) (by omega) (by omega) (by omega))

/-- At any legal margin the normalized optimum is at least its normalized
ordinary variance. -/
theorem normalizedHypergeomProxy_ge_variance (N k m : ℕ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hm : 0 < m) (hmN : m < N) :
    4 * (k : ℝ) * ((N : ℝ) - k) / ((N : ℝ) * ((N : ℝ) - 1)) ≤
      normalizedHypergeomProxy N k m := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmNR : (m : ℝ) < N := by exact_mod_cast hmN
  have hscale : 0 ≤ 4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m)) := by positivity
  have hv := mul_le_mul_of_nonneg_left
    (hypergeomOptimalProxy_ge_variance N k m hk hmN.le) hscale
  rw [hypergeomTiltVariance_zero N k m hk hmN.le,
    Nat.cast_sub hk, Nat.cast_sub hmN.le] at hv
  have halg :
      (4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) *
        ((m : ℝ) * (k : ℝ) * ((N : ℝ) - k) * ((N : ℝ) - m) /
          ((N : ℝ) ^ 2 * ((N : ℝ) - 1))) =
        4 * (k : ℝ) * ((N : ℝ) - k) / ((N : ℝ) * ((N : ℝ) - 1)) := by
    field_simp [show (N : ℝ) ≠ 0 by linarith,
      show (N : ℝ) - 1 ≠ 0 by linarith, hmR.ne',
      (sub_pos.mpr hmNR).ne']
  rw [halg] at hv
  exact hv

/-- At the nearest-balanced odd success count the normalized ordinary
variance already exceeds one, uniformly over every nonconstant sample. -/
theorem odd_normalized_proxy_center_gt_one (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hmN : m < 2 * n + 1) :
    1 < normalizedHypergeomProxy (2 * n + 1) n m := by
  have hv := normalizedHypergeomProxy_ge_variance (2 * n + 1) n m
    (by omega) (by omega) hm hmN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have heq : 4 * (n : ℝ) * ((((2 * n + 1 : ℕ) : ℝ)) - n) /
      ((((2 * n + 1 : ℕ) : ℝ)) * ((((2 * n + 1 : ℕ) : ℝ)) - 1)) =
        1 + 1 / (((2 * n + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp [hnR.ne']
    ring
  rw [heq] at hv
  have : 0 < 1 / (((2 * n + 1 : ℕ) : ℝ)) := by positivity
  linarith

/-- A finite-population algebraic boundary estimate. Its population
threshold depends only on the sample size, not on the success count. -/
theorem normalizedHypergeomProxy_boundary_lt_one (N k m : ℕ)
    (hm : 0 < m) (hkm : k < m) (hlarge : 2 * m * (m + 1) ≤ N) :
    normalizedHypergeomProxy N k m < 1 := by
  have hN : 2 ≤ N := by nlinarith
  have hkN : k ≤ N := by nlinarith
  have hmN : m < N := by nlinarith
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkmR : (k : ℝ) < m := by exact_mod_cast hkm
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hlargeR : 2 * (m : ℝ) * ((m : ℝ) + 1) ≤ N := by exact_mod_cast hlarge
  have hNm : 0 < (N : ℝ) - m := by
    have : (m : ℝ) < N := by exact_mod_cast hmN
    linarith
  have hN1 : 0 < (N : ℝ) - 1 := by linarith
  have hscale : 0 ≤ 4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m)) := by positivity
  have hcurv : sharpCurvatureConstant N k m ≤
      (k : ℝ) * ((N : ℝ) - k) / (4 * ((N : ℝ) - 1)) :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
  have hbound := mul_le_mul_of_nonneg_left
    ((hypergeomOptimalProxy_le_curvature N k m hkN hmN.le).trans hcurv) hscale
  have hstrict :
      (4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) *
        ((k : ℝ) * ((N : ℝ) - k) / (4 * ((N : ℝ) - 1))) < 1 := by
    have hkstep : (k : ℝ) ≤ (m : ℝ) - 1 := by
      have hh : k + 1 ≤ m := by omega
      have hhR : (k : ℝ) + 1 ≤ m := by exact_mod_cast hh
      linarith
    have hprod : (k : ℝ) * ((N : ℝ) - k) ≤ ((m : ℝ) - 1) * (N : ℝ) := by
      nlinarith [sq_nonneg (k : ℝ)]
    have hmargin : (N : ℝ) ^ 2 * ((m : ℝ) - 1) <
        (m : ℝ) * ((N : ℝ) - m) * ((N : ℝ) - 1) := by
      have hmn : (m : ℝ) * ((m : ℝ) + 1) < N := by
        have : 0 < (m : ℝ) * ((m : ℝ) + 1) := by positivity
        linarith
      have hmul : 0 < (N : ℝ) * ((N : ℝ) - (m : ℝ) * ((m : ℝ) + 1)) := by
        exact mul_pos (by linarith) (by linarith)
      nlinarith [sq_nonneg (m : ℝ)]
    have hden : 0 < (m : ℝ) * ((N : ℝ) - m) * ((N : ℝ) - 1) := by positivity
    have halg :
        (4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) *
          ((k : ℝ) * ((N : ℝ) - k) / (4 * ((N : ℝ) - 1))) =
        (N : ℝ) * (k : ℝ) * ((N : ℝ) - k) /
          ((m : ℝ) * ((N : ℝ) - m) * ((N : ℝ) - 1)) := by
      field_simp [hmR.ne', hNm.ne', hN1.ne']
    rw [halg]
    apply (div_lt_one hden).mpr
    have hprodN := mul_le_mul_of_nonneg_left hprod (show 0 ≤ (N : ℝ) by positivity)
    nlinarith only [hprodN, hmargin]
  exact hbound.trans_lt hstrict

end
end ExactHoeffding
