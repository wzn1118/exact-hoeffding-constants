import ExactHoeffding.OddHypergeomExtremizers

namespace ExactHoeffding

/-- In the canonical triangle a strictly unbalanced marked margin gives a
strict normalized-proxy gap below the even universal coefficient. -/
theorem normalizedHypergeomProxy_triangle_lt_universal (N k m : ℕ)
    (hk : 0 < k) (hm : 0 < m) (hmk : m ≤ k) (hkhalf : 2 * k < N) :
    normalizedHypergeomProxy N k m < (N : ℝ) / ((N : ℝ) - 1) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : 0 < (N : ℝ) - 1 := by
    have hh : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkhalfR : 2 * (k : ℝ) < N := by exact_mod_cast hkhalf
  have hd0 : 0 < 1 - 2 * (k : ℝ) / N := by
    have hh := (div_lt_one hNR).2 hkhalfR
    linarith
  have hd1 : 1 - 2 * (k : ℝ) / N < 1 := by
    have hh : 0 < 2 * (k : ℝ) / N := by positivity
    linarith
  have hfactor := imbalanceFactor_lt_one (1 - 2 * (k : ℝ) / N) hd0 hd1
  have hscale : 0 < (N : ℝ) / ((N : ℝ) - 1) := by positivity
  have hstrict : (N : ℝ) / ((N : ℝ) - 1) *
      imbalanceFactor (1 - 2 * (k : ℝ) / N) < (N : ℝ) / ((N : ℝ) - 1) := by
    nlinarith only [hfactor, hscale]
  by_cases hm1 : m = 1
  · subst m
    rw [normalizedHypergeomProxy_singleton_subhalf N k hk hkhalf]
    exact hstrict
  · exact (normalizedHypergeomProxy_inner_lt_bernoulli N k m (by omega) hmk
      hkhalf).trans hstrict

/-- Complete classification in the half-margin square. Only the marked
margin, rather than either of the two margins, can yield normalized equality. -/
theorem even_normalized_proxy_half_equality (q k m : ℕ)
    (hq : 0 < q) (hk : 0 < k) (hkq : k ≤ q) (hm : 0 < m) (hmq : m ≤ q) :
    normalizedHypergeomProxy (2 * q) k m =
      ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) ↔ k = q := by
  by_cases hbal : k = q
  · subst k
    rw [normalizedHypergeomProxy_even_attains q m hq hm (by omega)]
    simp
  · have hlt : normalizedHypergeomProxy (2 * q) k m <
        ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) := by
      by_cases hmk : m ≤ k
      · exact normalizedHypergeomProxy_triangle_lt_universal (2 * q) k m hk hm hmk
          (by omega)
      · apply normalizedHypergeomProxy_transpose_strict_ceiling (2 * q) k m hk
          (by omega) (by omega)
        · have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
          have hN0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (show 0 < 2 * q by omega)
          have hN1 : 0 < ((2 * q : ℕ) : ℝ) - 1 := by push_cast; linarith
          exact div_pos hN0 hN1
        · exact normalizedHypergeomProxy_universal_upper (2 * q) m k (by omega)
            (by omega) hk (by omega)
    constructor
    · intro heq
      exact False.elim ((ne_of_lt hlt) heq)
    · intro heq
      exact False.elim (hbal heq)

/-- Exhaustive even-population extremizers in the original margins,
including singleton margins and population size two. -/
theorem even_normalized_proxy_all_equality (q k m : ℕ)
    (hq : 0 < q) (hk : 0 < k) (hkN : k < 2 * q)
    (hm : 0 < m) (hmN : m < 2 * q) :
    normalizedHypergeomProxy (2 * q) k m =
      ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) ↔ k = q := by
  by_cases hkq : k ≤ q
  · by_cases hmq : m ≤ q
    · exact even_normalized_proxy_half_equality q k m hq hk hkq hm hmq
    · rw [normalizedHypergeomProxy_sample_complement (2 * q) k m hkN.le hmN.le
        (by omega)]
      exact even_normalized_proxy_half_equality q k (2 * q - m) hq hk hkq
        (by omega) (by omega)
  · rw [normalizedHypergeomProxy_success_complement (2 * q) k m hkN.le hmN.le
      (by omega)]
    by_cases hmq : m ≤ q
    · rw [even_normalized_proxy_half_equality q (2 * q - k) m hq
        (by omega) (by omega) hm hmq]
      omega
    · rw [normalizedHypergeomProxy_sample_complement (2 * q) (2 * q - k) m
        (Nat.sub_le _ _) hmN.le (by omega),
        even_normalized_proxy_half_equality q (2 * q - k) (2 * q - m) hq
          (by omega) (by omega) (by omega) (by omega)]
      omega

/-- The universal upper bound and its full even equality classification. -/
theorem even_normalized_proxy_global_optimality (q k m : ℕ)
    (hq : 0 < q) (hk : 0 < k) (hkN : k < 2 * q)
    (hm : 0 < m) (hmN : m < 2 * q) :
    normalizedHypergeomProxy (2 * q) k m ≤
        ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) ∧
      (normalizedHypergeomProxy (2 * q) k m =
        ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) ↔ 2 * k = 2 * q) := by
  refine ⟨normalizedHypergeomProxy_universal_upper (2 * q) k m (by omega)
    hkN.le hm hmN, ?_⟩
  rw [even_normalized_proxy_all_equality q k m hq hk hkN hm hmN]
  omega

/-- A balanced sample does not by itself maximize the normalized proxy:
the normalization distinguishes the marked and sample margins. -/
theorem normalizedHypergeomProxy_four_one_two :
    normalizedHypergeomProxy 4 1 2 = 1 := by
  rw [normalizedHypergeomProxy_transpose_ratio 4 1 2 (by omega) (by omega)
    (by omega) (by omega)]
  have h := normalizedHypergeomProxy_even_attains 2 1 (by omega) (by omega) (by omega)
  norm_num at h ⊢
  rw [h]
  norm_num

end ExactHoeffding
