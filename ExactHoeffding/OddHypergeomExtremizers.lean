import ExactHoeffding.ParityProxyComparison
import ExactHoeffding.SingletonOptimalProxy
import ExactHoeffding.StrictHypergeometricProxy

namespace ExactHoeffding

private theorem normalized_bernoulli_scale (N k m : ℝ)
    (hN : N≠0) (hN1 : N-1≠0) (hm : m≠0) (hNm : N-m≠0) (hk : k≠0) :
    (4*N/(m*(N-m)))*(envelopeM N m*((1-2*k/N)/(2*Real.log ((1-k/N)/(k/N)))))=
      N/(N-1)*imbalanceFactor (1-2*k/N) := by
  unfold envelopeM imbalanceFactor
  rw [logOdds_success_fraction N k hN hk]
  generalize Real.log ((1-k/N)/(k/N))=L
  field_simp [hN,hN1,hm,hNm] <;> ring

theorem normalizedHypergeomProxy_singleton_subhalf (N k : ℕ)
    (hk0 : 0<k) (hhalf : 2*k<N) :
    normalizedHypergeomProxy N k 1=
      (N:ℝ)/((N:ℝ)-1)*imbalanceFactor (1-2*(k:ℝ)/(N:ℝ)) := by
  have hN : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hN1 : (N:ℝ)-1≠0 := by
    have hh : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
    linarith
  have hkR : (k:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hk0
  unfold normalizedHypergeomProxy
  rw [hypergeomOptimalProxy_singleton_subhalf N k hk0 hhalf]
  norm_num only [Nat.cast_one,one_mul]
  unfold imbalanceFactor
  rw [logOdds_success_fraction (N:ℝ) (k:ℝ) hN hkR]
  generalize Real.log ((1-(k:ℝ)/(N:ℝ))/((k:ℝ)/(N:ℝ)))=L
  field_simp [hN,hN1] <;> ring

theorem normalizedHypergeomProxy_inner_lt_bernoulli (N k m : ℕ)
    (hm : 2≤m) (hmk : m≤k) (hkhalf : 2*k<N) :
    normalizedHypergeomProxy N k m<
      (N:ℝ)/((N:ℝ)-1)*imbalanceFactor (1-2*(k:ℝ)/(N:ℝ)) := by
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hkR : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have hmNR : (m:ℝ)<N := by exact_mod_cast (show m<N by omega)
  have hN1 : (N:ℝ)-1≠0 := by
    have hh : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
    linarith
  have hscale : 0<4*(N:ℝ)/((m:ℝ)*((N:ℝ)-m)) := by positivity
  have hproxy : hypergeomOptimalProxy N k m<envelopeM (N:ℝ) (m:ℝ)*
      ((1-2*(k:ℝ)/(N:ℝ))/(2*Real.log ((1-(k:ℝ)/(N:ℝ))/((k:ℝ)/(N:ℝ))))) := by
    by_cases hm2 : m=2
    · subst m
      rw [hypergeomOptimalProxy_two_draw N k (by omega) (by omega)]
      simpa only [envelopeM,Nat.cast_ofNat] using
        hypergeom_two_draw_bernoulli_envelope N k (by omega) (by omega) hkhalf
    · simpa only [mul_div_assoc] using
        hypergeomOptimalProxy_lt_scaled_bernoulli N k m (by omega) hmk hkhalf
  have h := mul_lt_mul_of_pos_left hproxy hscale
  rw [normalized_bernoulli_scale (N:ℝ) (k:ℝ) (m:ℝ)
    hNR.ne' hN1 hmR.ne' (sub_pos.mpr hmNR).ne' hkR.ne'] at h
  exact h

theorem odd_normalized_proxy_triangle_upper (n k m : ℕ)
    (hn : 0<n) (hk : 0<k) (hm : 0<m) (hmk : m≤k) (hkn : k≤n) :
    normalizedHypergeomProxy (2*n+1) k m≤oddHypergeomConstant (2*n+1) := by
  by_cases hm1 : m=1
  · subst m
    rw [normalizedHypergeomProxy_singleton_subhalf (2*n+1) k hk (by omega)]
    exact odd_imbalance_bound n k hn hk hkn
  · exact (normalizedHypergeomProxy_inner_lt_bernoulli (2*n+1) k m (by omega) hmk (by omega)).le.trans
      (odd_imbalance_bound n k hn hk hkn)

theorem odd_normalized_proxy_triangle_equality (n k m : ℕ)
    (hn : 0<n) (hk : 0<k) (hm : 0<m) (hmk : m≤k) (hkn : k≤n) :
    normalizedHypergeomProxy (2*n+1) k m=oddHypergeomConstant (2*n+1) ↔ m=1 ∧ k=n := by
  by_cases hm1 : m=1
  · subst m
    rw [normalizedHypergeomProxy_singleton_subhalf (2*n+1) k hk (by omega),
      odd_imbalance_bound_equality_iff n k hn hk hkn]
    simp
  · have hlt := (normalizedHypergeomProxy_inner_lt_bernoulli (2*n+1) k m (by omega) hmk (by omega)).trans_le
      (odd_imbalance_bound n k hn hk hkn)
    constructor
    · intro heq
      exact False.elim ((ne_of_lt hlt) heq)
    · rintro ⟨h,_⟩
      exact False.elim (hm1 h)

theorem odd_normalized_proxy_half_upper (n k m : ℕ)
    (hn : 0<n) (hk : 0<k) (hkn : k≤n) (hm : 0<m) (hmn : m≤n) :
    normalizedHypergeomProxy (2*n+1) k m≤oddHypergeomConstant (2*n+1) := by
  by_cases hmk : m≤k
  · exact odd_normalized_proxy_triangle_upper n k m hn hk hm hmk hkn
  · exact (normalizedHypergeomProxy_transpose_strict_ceiling (2*n+1) k m hk (by omega) (by omega)
      (oddHypergeomConstant (2*n+1)) (oddHypergeomConstant_pos (2*n+1) (by omega))
      (odd_normalized_proxy_triangle_upper n m k hn hm hk (by omega) hmn)).le

theorem odd_normalized_proxy_half_equality (n k m : ℕ)
    (hn : 0<n) (hk : 0<k) (hkn : k≤n) (hm : 0<m) (hmn : m≤n) :
    normalizedHypergeomProxy (2*n+1) k m=oddHypergeomConstant (2*n+1) ↔ m=1 ∧ k=n := by
  by_cases hmk : m≤k
  · exact odd_normalized_proxy_triangle_equality n k m hn hk hm hmk hkn
  · have hlt := normalizedHypergeomProxy_transpose_strict_ceiling (2*n+1) k m hk (by omega) (by omega)
      (oddHypergeomConstant (2*n+1)) (oddHypergeomConstant_pos (2*n+1) (by omega))
      (odd_normalized_proxy_triangle_upper n m k hn hm hk (by omega) hmn)
    constructor
    · intro heq
      exact False.elim ((ne_of_lt hlt) heq)
    · rintro ⟨hm1,hkn⟩
      omega

/-- Every odd-population margin pair is reduced by actual complement
symmetries; no asymptotic restriction on the sample size is imposed. -/
theorem odd_normalized_proxy_all_upper (n k m : ℕ)
    (hn : 0<n) (hk : 0<k) (hkN : k<2*n+1) (hm : 0<m) (hmN : m<2*n+1) :
    normalizedHypergeomProxy (2*n+1) k m≤oddHypergeomConstant (2*n+1) := by
  by_cases hkn : k≤n
  · by_cases hmn : m≤n
    · exact odd_normalized_proxy_half_upper n k m hn hk hkn hm hmn
    · rw [normalizedHypergeomProxy_sample_complement (2*n+1) k m hkN.le hmN.le (by omega)]
      exact odd_normalized_proxy_half_upper n k (2*n+1-m) hn hk hkn (by omega) (by omega)
  · rw [normalizedHypergeomProxy_success_complement (2*n+1) k m hkN.le hmN.le (by omega)]
    by_cases hmn : m≤n
    · exact odd_normalized_proxy_half_upper n (2*n+1-k) m hn (by omega) (by omega) hm hmn
    · rw [normalizedHypergeomProxy_sample_complement (2*n+1) (2*n+1-k) m (Nat.sub_le _ _) hmN.le (by omega)]
      exact odd_normalized_proxy_half_upper n (2*n+1-k) (2*n+1-m) hn
        (by omega) (by omega) (by omega) (by omega)

/-- Exhaustive odd-population extremizers in the original margins. -/
theorem odd_normalized_proxy_all_equality (n k m : ℕ)
    (hn : 0<n) (hk : 0<k) (hkN : k<2*n+1) (hm : 0<m) (hmN : m<2*n+1) :
    normalizedHypergeomProxy (2*n+1) k m=oddHypergeomConstant (2*n+1) ↔
      (m=1 ∨ m=2*n) ∧ (k=n ∨ k=n+1) := by
  by_cases hkn : k≤n
  · by_cases hmn : m≤n
    · rw [odd_normalized_proxy_half_equality n k m hn hk hkn hm hmn]
      omega
    · rw [normalizedHypergeomProxy_sample_complement (2*n+1) k m hkN.le hmN.le (by omega),
        odd_normalized_proxy_half_equality n k (2*n+1-m) hn hk hkn (by omega) (by omega)]
      omega
  · rw [normalizedHypergeomProxy_success_complement (2*n+1) k m hkN.le hmN.le (by omega)]
    by_cases hmn : m≤n
    · rw [odd_normalized_proxy_half_equality n (2*n+1-k) m hn (by omega) (by omega) hm hmn]
      omega
    · rw [normalizedHypergeomProxy_sample_complement (2*n+1) (2*n+1-k) m (Nat.sub_le _ _) hmN.le (by omega),
        odd_normalized_proxy_half_equality n (2*n+1-k) (2*n+1-m) hn
          (by omega) (by omega) (by omega) (by omega)]
      omega

end ExactHoeffding
