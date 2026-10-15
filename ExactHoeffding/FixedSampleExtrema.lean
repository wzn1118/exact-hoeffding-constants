import ExactHoeffding.TwoDrawSingletonComparison
import ExactHoeffding.NormalizedProxy

namespace ExactHoeffding
noncomputable section

private lemma odd_two_draw_scale_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < 4 * (((2 * n + 1 : ℕ) : ℝ)) /
      ((2 : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - 2)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnum : 0 < 4 * (((2 * n + 1 : ℕ) : ℝ)) := by positivity
  have hden : 0 < (2 : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - 2) := by
    push_cast
    nlinarith
  exact div_pos hnum hden

private lemma odd_two_draw_central_optimal_value (n : ℕ) (hn : 2 ≤ n) :
    hypergeomOptimalProxy (2 * n + 1) n 2 =
      threeMassProxy (hypergeomMass (2 * n + 1) n 2 0)
        (hypergeomMass (2 * n + 1) n 2 2) := by
  exact hypergeomOptimalProxy_two_draw (2 * n + 1) n hn (by omega)

/-- For two draws in an odd population, the nearest-balanced success counts
maximize the normalized optimal quadratic proxy at every admissible count. -/
theorem odd_normalized_proxy_two_draw_max (n k : ℕ)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hkN : k ≤ 2 * n) :
    normalizedHypergeomProxy (2 * n + 1) k 2 ≤
      normalizedHypergeomProxy (2 * n + 1) n 2 := by
  have hscale := odd_two_draw_scale_pos n hn
  have hupper := odd_two_draw_all_success_upper n k hn hk hkN
  have hopt : hypergeomOptimalProxy (2 * n + 1) k 2 ≤
      threeMassProxy (hypergeomMass (2 * n + 1) n 2 0)
        (hypergeomMass (2 * n + 1) n 2 2) :=
    optimalProxy_le _ _ hupper
  unfold normalizedHypergeomProxy
  rw [odd_two_draw_central_optimal_value n hn]
  exact mul_le_mul_of_nonneg_left hopt hscale.le

/-- The fixed-sample maximum has the closed two-draw value from the
three-point calculation. -/
theorem odd_normalized_proxy_two_draw_value (n : ℕ) (hn : 2 ≤ n) :
    normalizedHypergeomProxy (2 * n + 1) n 2 = oddTwoDrawConstant n := by
  unfold normalizedHypergeomProxy
  rw [odd_two_draw_central_optimal_value n hn]
  norm_num only [Nat.cast_ofNat]
  have hfactor :
      4 * (((2 * n + 1 : ℕ) : ℝ)) /
          ((2 : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - 2)) =
        2 * (((2 * n + 1 : ℕ) : ℝ)) /
          (((2 * n + 1 : ℕ) : ℝ) - 2) := by
    push_cast
    field_simp
    ring
  rw [hfactor]
  exact (oddTwoDrawConstant_eq_normalized_proxy n hn).symm

/-- The two-draw fixed-sample proxy is bounded by its closed maximum for every
admissible success count. -/
theorem odd_normalized_proxy_two_draw_le_constant (n k : ℕ)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hkN : k ≤ 2 * n) :
    normalizedHypergeomProxy (2 * n + 1) k 2 ≤ oddTwoDrawConstant n := by
  exact (odd_normalized_proxy_two_draw_max n k hn hk hkN).trans_eq
    (odd_normalized_proxy_two_draw_value n hn)

/-- Equality in the two-draw fixed-sample maximum occurs exactly at the two
nearest-balanced success counts. -/
theorem odd_normalized_proxy_two_draw_max_iff (n k : ℕ)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hkN : k ≤ 2 * n) :
    normalizedHypergeomProxy (2 * n + 1) k 2 =
      normalizedHypergeomProxy (2 * n + 1) n 2 ↔
      k = n ∨ k = n + 1 := by
  have hscale := odd_two_draw_scale_pos n hn
  have hcentral := odd_two_draw_central_optimal_value n hn
  constructor
  · intro heq
    unfold normalizedHypergeomProxy at heq
    rw [hcentral] at heq
    have hopt : hypergeomOptimalProxy (2 * n + 1) k 2 =
        threeMassProxy (hypergeomMass (2 * n + 1) n 2 0)
          (hypergeomMass (2 * n + 1) n 2 2) := by
      exact (mul_left_cancel₀ hscale.ne') heq
    have hactual := hypergeomOptimalProxy_isOptimal (2 * n + 1) k 2
      (by omega) (by omega)
    rw [hopt] at hactual
    exact (odd_two_draw_all_success_extremizers n k hn hk hkN).mp hactual
  · intro hcase
    rcases hcase with rfl | rfl
    · rfl
    · rw [normalizedHypergeomProxy_success_complement (2 * n + 1) (n + 1) 2
        (by omega) (by omega) (by omega)]
      congr 2; omega

/-- Equality with the closed two-draw constant has the same complete
success-count classification. -/
theorem odd_normalized_proxy_two_draw_eq_constant_iff (n k : ℕ)
    (hn : 2 ≤ n) (hk : 1 ≤ k) (hkN : k ≤ 2 * n) :
    normalizedHypergeomProxy (2 * n + 1) k 2 = oddTwoDrawConstant n ↔
      k = n ∨ k = n + 1 := by
  rw [← odd_normalized_proxy_two_draw_value n hn]
  exact odd_normalized_proxy_two_draw_max_iff n k hn hk hkN

end
end ExactHoeffding
