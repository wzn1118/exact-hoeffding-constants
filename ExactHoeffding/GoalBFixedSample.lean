import ExactHoeffding.FixedSampleGlobalExtrema
import ExactHoeffding.CompactContractionBoundary
import ExactHoeffding.EvenHypergeomExtremizers
import ExactHoeffding.Cumulants

namespace ExactHoeffding
noncomputable section
open Set

/-- The cubic lower bound for inverse hyperbolic tangent used in the finite-size
Bernoulli comparison. -/
theorem real_artanh_cubic_lower (d : ℝ) (hd0 : 0 ≤ d) (hd1 : d < 1) :
    d + d ^ 3 / 3 ≤ Real.artanh d := by
  let f : ℝ → ℝ := fun x => Real.artanh x - x - x ^ 3 / 3
  have hderiv : ∀ x ∈ Icc (0 : ℝ) d,
      HasDerivAt f (1 / (1 - x ^ 2) - 1 - x ^ 2) x := by
    intro x hx
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hd1
    have hxopen : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx1⟩
    have h := ((artanh_hasDerivAt_open x hxopen).sub (hasDerivAt_id x)).sub
      ((hasDerivAt_id x).pow 3 |>.const_mul (1 / 3 : ℝ))
    have hfun : (Real.artanh - id - fun y : ℝ => (1 / 3 : ℝ) * (id ^ 3) y) = f := by
      funext y
      dsimp [f]
      simp
      ring
    have hv : (1 / (1 - x ^ 2) - 1 - x ^ 2) =
        (1 / (1 - x ^ 2) - 1 - 1 / 3 * ((3 : ℝ) * id x ^ (3 - 1) * 1)) := by
      norm_num [id_eq]
      ring
    rw [← hfun]
    exact hv ▸ h
  have hcont : ContinuousOn f (Icc (0 : ℝ) d) := by
    intro x hx
    exact (hderiv x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (interior (Icc (0 : ℝ) d)) := by
    rw [interior_Icc]
    intro x hx
    exact (hderiv x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn f (Icc (0 : ℝ) d) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 d) hcont hdiff
    intro x hx
    rw [interior_Icc] at hx
    rw [(hderiv x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).deriv]
    have hx0 : 0 ≤ x := le_of_lt hx.1
    have hx1 : x < 1 := lt_of_lt_of_le hx.2 (le_of_lt hd1)
    have hden : 0 < 1 - x ^ 2 := by nlinarith
    have : 0 ≤ x ^ 4 := by positivity
    field_simp [ne_of_gt hden]
    nlinarith
  have hfd : 0 ≤ f d := by
    have h := hmono (show (0 : ℝ) ∈ Icc 0 d from ⟨le_rfl, hd0⟩)
      (show d ∈ Icc 0 d from ⟨hd0, le_rfl⟩) hd0
    simpa [f] using h
  dsimp [f] at hfd
  linarith

/-- The cubic bound gives a uniform scalar deficit for every positive
imbalance in the open Bernoulli domain. -/
theorem imbalanceFactor_cubic_upper (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    imbalanceFactor d ≤ 1 / (1 + d ^ 2 / 3) := by
  have h := real_artanh_cubic_lower d hd0.le hd1
  have hartpos : 0 < Real.artanh d := Real.artanh_pos ⟨hd0, hd1⟩
  have hlogOdds : logOdds d = 2 * Real.artanh d := by
    change Real.log ((1 + d) / (1 - d)) = 2 * Real.artanh d
    rw [Real.artanh_eq_half_log ⟨by linarith, hd1.le⟩]
    ring
  unfold imbalanceFactor
  rw [hlogOdds]
  have hratio : 0 ≤ 1 / (1 + d ^ 2 / 3) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left h hratio
  have hden : 0 < 1 + d ^ 2 / 3 := by positivity
  have halg : (1 / (1 + d ^ 2 / 3)) * (d + d ^ 3 / 3) = d := by
    field_simp [ne_of_gt hden]
  rw [halg] at hscaled
  apply (div_le_iff₀ (mul_pos (by norm_num) hartpos)).2
  nlinarith [hscaled]

/-- A strict odd-population Bernoulli deficit at every reduced off-center
success count. -/
theorem odd_imbalance_factor_offcenter_lt (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n) :
    ((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 1 : ℕ) : ℝ) - 1) *
        imbalanceFactor (1 - 2 * (k : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) <
      (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
  let N : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  have hn2 : 2 ≤ n := by omega
  have hN : (5 : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast (show 5 ≤ 2 * n + 1 by omega)
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hd0 : 0 < 3 / N := by positivity
  have hd1 : 3 / N < 1 := (div_lt_one hN0).mpr (by linarith)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hknle : k + 1 ≤ n := by omega
  have hknleR : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hknle
  have hd : 3 / N ≤ 1 - 2 * (k : ℝ) / N := by
    apply (div_le_iff₀ hN0).2
    field_simp [ne_of_gt hN0]
    dsimp [N]
    push_cast
    nlinarith [hknleR]
  have hdk1 : 1 - 2 * (k : ℝ) / N < 1 := by
    have : 0 < 2 * (k : ℝ) / N := by positivity
    linarith
  have hanti : imbalanceFactor (1 - 2 * (k : ℝ) / N) ≤ imbalanceFactor (3 / N) := by
    apply imbalanceFactor_strictAnti.antitoneOn
      ⟨hd0, hd1⟩ ⟨lt_of_lt_of_le hd0 hd, hdk1⟩ hd
  have hlog : 2 * Real.artanh (3 / N) ≥ 2 * (3 / N + (3 / N) ^ 3 / 3) := by
    have h := real_artanh_cubic_lower (3 / N) hd0.le hd1
    linarith
  have hartpos : 0 < Real.artanh (3 / N) := Real.artanh_pos ⟨hd0, hd1⟩
  have hlogOdds : logOdds (3 / N) = 2 * Real.artanh (3 / N) := by
    change Real.log ((1 + 3 / N) / (1 - 3 / N)) = 2 * Real.artanh (3 / N)
    rw [Real.artanh_eq_half_log ⟨by linarith, hd1.le⟩]
    ring
  have hfactor : imbalanceFactor (3 / N) ≤ N ^ 2 / (N ^ 2 + 3) := by
    unfold imbalanceFactor
    rw [hlogOdds]
    have hden : 0 < N ^ 2 + 3 := by positivity
    have hratio : 0 ≤ N ^ 2 / (N ^ 2 + 3) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hlog hratio
    have halg : (N ^ 2 / (N ^ 2 + 3)) * (2 * (3 / N + (3 / N) ^ 3 / 3)) =
        2 * (3 / N) := by
      field_simp [ne_of_gt hN0]
    rw [halg] at hscaled
    apply (div_le_iff₀ (mul_pos (by norm_num) hartpos)).2
    exact hscaled
  have hscale : 0 < N / (N - 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hanti (le_of_lt hscale)
  have hmul2 := hmul.trans (mul_le_mul_of_nonneg_left hfactor (le_of_lt hscale))
  have htarget : N / (N - 1) * (N ^ 2 / (N ^ 2 + 3)) < (N + 1) / N := by
    field_simp [ne_of_gt hN0, ne_of_gt hN1]
    nlinarith [sq_nonneg N]
  exact hmul2.trans_lt htarget

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- Every reduced noncentral odd-population margin is strictly below the
central ordinary variance, after the fixed-sample normalization. -/
theorem odd_normalized_proxy_offcenter_lt_central_variance (n k m : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hm : 0 < m) (hmn : m ≤ n) (hmN : m < 2 * n + 1) :
    normalizedHypergeomProxy (2 * n + 1) k m <
      (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
  have hN : 2 * k < 2 * n + 1 := by omega
  by_cases hmk : m ≤ k
  · by_cases hm1 : m = 1
    · subst m
      rw [normalizedHypergeomProxy_singleton_subhalf (2 * n + 1) k hk hN]
      exact odd_imbalance_factor_offcenter_lt n k hn hk hkn
    · exact (normalizedHypergeomProxy_inner_lt_bernoulli (2 * n + 1) k m
        (by omega) hmk hN).trans (odd_imbalance_factor_offcenter_lt n k hn hk hkn)
  · have hkm : k < m := by omega
    have hkN : k ≤ 2 * n + 1 := by omega
    have hNreal : (0 : ℝ) < (2 * n + 1 : ℕ) := by positivity
    have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hNmreal : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) - m := by
      exact sub_pos.mpr (by exact_mod_cast hmN)
    have hN1real : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) - 1 := by
      have : (1 : ℝ) < (2 * n + 1 : ℕ) := by exact_mod_cast (show 1 < 2 * n + 1 by omega)
      linarith
    have hkreal : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hkmR : (k : ℝ) < (m : ℝ) := by exact_mod_cast hkm
    have hmhalfR : (m : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hmn
    have hNreal_eq : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by push_cast; ring
    have hsumR : (m : ℝ) + (k : ℝ) + 2 ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show m + k + 2 ≤ 2 * n + 1 by omega)
    have hNmkR : (2 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) - m - k := by
      linarith
    have hdiff1nat : k + 1 ≤ m := by omega
    have hdiff1R : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hdiff1nat
    have hdiff1 : (1 : ℝ) ≤ (m : ℝ) - k := by linarith
    have hdiff2 : (2 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) - m - k := hNmkR
    have hprod2 : (2 : ℝ) ≤ ((m : ℝ) - k) *
        (((2 * n + 1 : ℕ) : ℝ) - m - k) := by
      have h := mul_le_mul hdiff1 hdiff2 (by norm_num : (0 : ℝ) ≤ 2)
        (by linarith : (0 : ℝ) ≤ (m : ℝ) - k)
      nlinarith
    have hmin : (k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k) ≤
        (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) := by
      have hid : (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) -
          (k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k) =
          ((m : ℝ) - k) * (((2 * n + 1 : ℕ) : ℝ) - m - k) := by ring
      linarith
    have hcurv := hypergeomOptimalProxy_le_curvature (2 * n + 1) k m
      hkN (by omega)
    unfold sharpCurvatureConstant at hcurv
    rw [min_eq_left hmin] at hcurv
    have hscale : 0 ≤ 4 * ((2 * n + 1 : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m)) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hcurv hscale
    unfold normalizedHypergeomProxy
    have htarget :
        4 * ((2 * n + 1 : ℕ) : ℝ) /
            ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m)) *
          (((k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k)) /
            (4 * (((2 * n + 1 : ℕ) : ℝ) - 1))) <
        (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
      have hgap : (2 : ℝ) ≤
          (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) -
            (k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k) := by
        have hid : (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) -
            (k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k) =
            ((m : ℝ) - k) * (((2 * n + 1 : ℕ) : ℝ) - m - k) := by ring
        rw [hid]
        exact hprod2
      field_simp [ne_of_gt hNreal, ne_of_gt hmreal, ne_of_gt hNmreal,
        ne_of_gt hN1real]
      nlinarith
    exact hscaled.trans_lt htarget

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

private theorem odd_normalized_proxy_center_ge_variance (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hmN : m < 2 * n + 1) :
    (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) ≤
      normalizedHypergeomProxy (2 * n + 1) n m := by
  have hv := normalizedHypergeomProxy_ge_variance (2 * n + 1) n m
    (by omega) (by omega) hm hmN
  have heq : 4 * (n : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - n) /
      (((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - 1)) =
      (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) := by
    push_cast
    field_simp [show (0 : ℝ) < 2 * n + 1 by positivity]
    ring
  rw [heq] at hv
  exact hv

private theorem odd_normalized_proxy_reduced_fixed_sample (n k m : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkN : k < 2 * n + 1)
    (hm : 0 < m) (hmn : m ≤ n) (hmN : m < 2 * n + 1) :
    normalizedHypergeomProxy (2 * n + 1) k m ≤
        normalizedHypergeomProxy (2 * n + 1) n m ∧
      (normalizedHypergeomProxy (2 * n + 1) k m =
        normalizedHypergeomProxy (2 * n + 1) n m ↔ k = n ∨ k = n + 1) := by
  have hcenter :
      (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) ≤
        normalizedHypergeomProxy (2 * n + 1) n m :=
    odd_normalized_proxy_center_ge_variance n m hn hm hmN
  by_cases hkn : k ≤ n
  · by_cases hkc : k = n
    · subst k
      exact ⟨le_rfl, by simp⟩
    · have hkn' : k < n := by omega
      have hlt := odd_normalized_proxy_offcenter_lt_central_variance n k m
        hn hk hkn' hm hmn hmN
      have hstrict : normalizedHypergeomProxy (2 * n + 1) k m <
          normalizedHypergeomProxy (2 * n + 1) n m := hlt.trans_le hcenter
      exact ⟨hstrict.le, ⟨fun heq => False.elim ((ne_of_lt hstrict) heq),
        fun heq => by rcases heq with heq | heq <;> omega⟩⟩
  · have hkn' : n < k := by omega
    have hcomp : 0 < 2 * n + 1 - k := by omega
    have hcompN : 2 * n + 1 - k ≤ n := by omega
    have hcomp_res := odd_normalized_proxy_reduced_fixed_sample n (2 * n + 1 - k) m
      hn hcomp (by omega) hm hmn hmN
    rw [normalizedHypergeomProxy_success_complement (2 * n + 1) k m
      hkN.le hmN.le (by omega)]
    constructor
    · exact hcomp_res.1
    · constructor
      · intro heq
        have heqc := (hcomp_res.2).mp heq
        omega
      · intro heq
        apply (hcomp_res.2).mpr
        omega

/-- Fixed-sample odd-population extremizers, with the exact two central
success counts and no asymptotic restriction. -/
theorem odd_normalized_proxy_fixed_sample_extremizers (n k m : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkN : k < 2 * n + 1)
    (hm : 0 < m) (hmN : m < 2 * n + 1) :
    normalizedHypergeomProxy (2 * n + 1) k m ≤
        normalizedHypergeomProxy (2 * n + 1) n m ∧
      (normalizedHypergeomProxy (2 * n + 1) k m =
        normalizedHypergeomProxy (2 * n + 1) n m ↔ k = n ∨ k = n + 1) := by
  by_cases hmn : m ≤ n
  · exact odd_normalized_proxy_reduced_fixed_sample n k m hn hk hkN hm hmn hmN
  · have hmcomp : 0 < 2 * n + 1 - m := by omega
    have hmcompN : 2 * n + 1 - m ≤ n := by omega
    have hred := odd_normalized_proxy_reduced_fixed_sample n k (2 * n + 1 - m)
      hn hk hkN hmcomp hmcompN (by omega)
    rw [normalizedHypergeomProxy_sample_complement (2 * n + 1) k m
      hkN.le hmN.le (by omega),
      normalizedHypergeomProxy_sample_complement (2 * n + 1) n m
        (by omega) hmN.le (by omega)]
    exact hred

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The unnormalized odd fixed-sample extremizer theorem corresponding to the
paper's main statement. -/
theorem hypergeomOptimalProxy_fixed_sample_extremizers_odd (n k m : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkN : k < 2 * n + 1)
    (hm : 0 < m) (hmN : m < 2 * n + 1) :
    hypergeomOptimalProxy (2 * n + 1) k m ≤
        hypergeomOptimalProxy (2 * n + 1) n m ∧
      (hypergeomOptimalProxy (2 * n + 1) k m =
        hypergeomOptimalProxy (2 * n + 1) n m ↔ k = n ∨ k = n + 1) := by
  have hnorm := odd_normalized_proxy_fixed_sample_extremizers n k m hn hk hkN hm hmN
  have hden : 0 < ((2 * n + 1 : ℕ) : ℝ) - m :=
    sub_pos.mpr (by exact_mod_cast hmN)
  have hscale : 0 < 4 * ((2 * n + 1 : ℕ) : ℝ) /
      ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m)) := by positivity
  have hle : hypergeomOptimalProxy (2 * n + 1) k m ≤
      hypergeomOptimalProxy (2 * n + 1) n m := by
    have h := hnorm.1
    change (4 * ((2 * n + 1 : ℕ) : ℝ) /
      ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m))) *
        hypergeomOptimalProxy (2 * n + 1) k m ≤
      (4 * ((2 * n + 1 : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m))) *
        hypergeomOptimalProxy (2 * n + 1) n m at h
    exact (mul_le_mul_iff_of_pos_left hscale).mp h
  refine ⟨hle, ?_⟩
  have heqnorm : normalizedHypergeomProxy (2 * n + 1) k m =
      normalizedHypergeomProxy (2 * n + 1) n m ↔ k = n ∨ k = n + 1 := hnorm.2
  constructor
  · intro heq
    apply heqnorm.mp
    change (4 * ((2 * n + 1 : ℕ) : ℝ) /
      ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m))) *
        hypergeomOptimalProxy (2 * n + 1) k m =
      (4 * ((2 * n + 1 : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m))) *
        hypergeomOptimalProxy (2 * n + 1) n m
    rw [heq]
  · intro heq
    have hnormeq := heqnorm.mpr heq
    change (4 * ((2 * n + 1 : ℕ) : ℝ) /
      ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m))) *
        hypergeomOptimalProxy (2 * n + 1) k m =
      (4 * ((2 * n + 1 : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m))) *
        hypergeomOptimalProxy (2 * n + 1) n m at hnormeq
    exact (mul_left_cancel₀ hscale.ne' hnormeq)

/-- The unnormalized even fixed-sample extremizer theorem. -/
theorem hypergeomOptimalProxy_fixed_sample_extremizers_even (q k m : ℕ)
    (hq : 0 < q) (hk : 0 < k) (hkN : k < 2 * q)
    (hm : 0 < m) (hmN : m < 2 * q) :
    hypergeomOptimalProxy (2 * q) k m ≤ hypergeomOptimalProxy (2 * q) q m ∧
      (hypergeomOptimalProxy (2 * q) k m = hypergeomOptimalProxy (2 * q) q m ↔ k = q) := by
  have hnorm := even_normalized_proxy_global_optimality q k m hq hk hkN hm hmN
  have hcenter := normalizedHypergeomProxy_even_attains q m hq hm (by omega)
  have hden : 0 < ((2 * q : ℕ) : ℝ) - m :=
    sub_pos.mpr (by exact_mod_cast hmN)
  have hscale : 0 < 4 * ((2 * q : ℕ) : ℝ) /
      ((m : ℝ) * (((2 * q : ℕ) : ℝ) - m)) := by positivity
  have hle : hypergeomOptimalProxy (2 * q) k m ≤ hypergeomOptimalProxy (2 * q) q m := by
    have h := hnorm.1
    change (4 * ((2 * q : ℕ) : ℝ) /
      ((m : ℝ) * (((2 * q : ℕ) : ℝ) - m))) * hypergeomOptimalProxy (2 * q) k m ≤
      ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) at h
    have hc : ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) =
        (4 * ((2 * q : ℕ) : ℝ) /
          ((m : ℝ) * (((2 * q : ℕ) : ℝ) - m))) * hypergeomOptimalProxy (2 * q) q m := by
      symm
      exact hcenter
    rw [hc] at h
    exact (mul_le_mul_iff_of_pos_left hscale).mp h
  refine ⟨hle, ?_⟩
  have heqnorm : normalizedHypergeomProxy (2 * q) k m =
      normalizedHypergeomProxy (2 * q) q m ↔ k = q := by
    rw [hcenter]
    simpa only [show (2 * k = 2 * q) ↔ k = q by omega] using hnorm.2
  constructor
  · intro heq
    apply heqnorm.mp
    simpa [normalizedHypergeomProxy] using congrArg
      (fun x => (4 * ((2 * q : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * q : ℕ) : ℝ) - m))) * x) heq
  · intro heq
    apply (mul_left_cancel₀ hscale.ne')
    exact heqnorm.mpr heq

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- Complete fixed-sample extremizer theorem in original population notation. -/
theorem hypergeomOptimalProxy_fixed_sample_extremizers (N k m : ℕ)
    (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N) :
    hypergeomOptimalProxy N k m ≤ hypergeomOptimalProxy N (N / 2) m ∧
      (hypergeomOptimalProxy N k m = hypergeomOptimalProxy N (N / 2) m ↔
        k = N / 2 ∨ k = N - N / 2) := by
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' N
  · subst N
    have hqpos : 0 < q := by omega
    have h := hypergeomOptimalProxy_fixed_sample_extremizers_even q k m
      hqpos hk (by omega) hm (by omega)
    have hhalf : (2 * q) / 2 = q := by omega
    refine ⟨?_, ?_⟩
    · simpa only [hhalf] using h.1
    · rw [hhalf]
      have hcomp : 2 * q - q = q := by omega
      rw [hcomp]
      simpa only [or_self] using h.2
  · subst N
    have hnpos : 0 < q := by omega
    have h := hypergeomOptimalProxy_fixed_sample_extremizers_odd q k m
      hnpos hk (by omega) hm (by omega)
    have hhalf : (2 * q + 1) / 2 = q := by omega
    have hcomp : 2 * q + 1 - q = q + 1 := by omega
    simpa only [hhalf, hcomp] using h

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The explicit odd scalar gap obtained from the cubic Bernoulli bound. -/
theorem odd_imbalance_factor_offcenter_gap (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n) :
    ((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 1 : ℕ) : ℝ) - 1) *
        imbalanceFactor (1 - 2 * (k : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) ≤
      ((((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ)) -
        (2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) - 3) /
          (((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - 1) *
            ((((2 * n + 1 : ℕ) : ℝ) ^ 2) + 3)) := by
  let N : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  have hn2 : 2 ≤ n := by omega
  have hN : (5 : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast (show 5 ≤ 2 * n + 1 by omega)
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hd0 : 0 < 3 / N := by positivity
  have hd1 : 3 / N < 1 := (div_lt_one hN0).mpr (by linarith)
  have hknle : k + 1 ≤ n := by omega
  have hknleR : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hknle
  have hd : 3 / N ≤ 1 - 2 * (k : ℝ) / N := by
    apply (div_le_iff₀ hN0).2
    field_simp [ne_of_gt hN0]
    dsimp [N]
    push_cast
    nlinarith [hknleR]
  have hdk1 : 1 - 2 * (k : ℝ) / N < 1 := by
    have : 0 < 2 * (k : ℝ) / N := by positivity
    linarith
  have hanti : imbalanceFactor (1 - 2 * (k : ℝ) / N) ≤ imbalanceFactor (3 / N) := by
    apply imbalanceFactor_strictAnti.antitoneOn
      ⟨hd0, hd1⟩ ⟨lt_of_lt_of_le hd0 hd, hdk1⟩ hd
  have hfactor := imbalanceFactor_cubic_upper (3 / N) hd0 hd1
  have hfactor' : imbalanceFactor (3 / N) ≤ N ^ 2 / (N ^ 2 + 3) := by
    have hden : 0 < N ^ 2 + 3 := by positivity
    have heq : 1 / (1 + (3 / N) ^ 2 / 3) = N ^ 2 / (N ^ 2 + 3) := by
      field_simp [ne_of_gt hN0]
    rw [heq] at hfactor
    exact hfactor
  have hscale : 0 < N / (N - 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hanti (le_of_lt hscale)
  have hmul2 := hmul.trans (mul_le_mul_of_nonneg_left hfactor' (le_of_lt hscale))
  have htarget : N / (N - 1) * (N ^ 2 / (N ^ 2 + 3)) =
      (N + 1) / N - (2 * N ^ 2 - 3) / (N * (N - 1) * (N ^ 2 + 3)) := by
    field_simp [ne_of_gt hN0, ne_of_gt hN1]
    ring
  dsimp [N] at hmul2 htarget ⊢
  rw [← htarget]
  exact hmul2

/-- The explicit even scalar gap obtained from the cubic Bernoulli bound. -/
theorem even_imbalance_factor_offcenter_gap (q k : ℕ)
    (hq : 0 < q) (hk : 0 < k) (hkq : k < q) :
    ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) *
        imbalanceFactor (1 - 2 * (k : ℝ) / ((2 * q : ℕ) : ℝ)) ≤
      ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) -
        4 * ((2 * q : ℕ) : ℝ) /
          ((((2 * q : ℕ) : ℝ) - 1) *
            (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4)) := by
  let N : ℝ := ((2 * q : ℕ) : ℝ)
  have hq2 : 2 ≤ q := by omega
  have hN : (4 : ℝ) ≤ N := by
    dsimp [N]
    exact_mod_cast (show 4 ≤ 2 * q by omega)
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N - 1 := by linarith
  have hd0 : 0 < 2 / N := by positivity
  have hd1 : 2 / N < 1 := (div_lt_one hN0).mpr (by linarith)
  have hkqle : k + 1 ≤ q := by omega
  have hkqleR : (k : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hkqle
  have hd : 2 / N ≤ 1 - 2 * (k : ℝ) / N := by
    apply (div_le_iff₀ hN0).2
    field_simp [ne_of_gt hN0]
    dsimp [N]
    push_cast
    nlinarith [hkqleR]
  have hdk1 : 1 - 2 * (k : ℝ) / N < 1 := by
    have : 0 < 2 * (k : ℝ) / N := by positivity
    linarith
  have hanti : imbalanceFactor (1 - 2 * (k : ℝ) / N) ≤ imbalanceFactor (2 / N) := by
    apply imbalanceFactor_strictAnti.antitoneOn
      ⟨hd0, hd1⟩ ⟨lt_of_lt_of_le hd0 hd, hdk1⟩ hd
  have hfactor := imbalanceFactor_cubic_upper (2 / N) hd0 hd1
  have hfactor' : imbalanceFactor (2 / N) ≤ 3 * N ^ 2 / (3 * N ^ 2 + 4) := by
    have heq : 1 / (1 + (2 / N) ^ 2 / 3) = 3 * N ^ 2 / (3 * N ^ 2 + 4) := by
      field_simp [ne_of_gt hN0]
      norm_num
    rw [heq] at hfactor
    exact hfactor
  have hscale : 0 < N / (N - 1) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hanti (le_of_lt hscale)
  have hmul2 := hmul.trans (mul_le_mul_of_nonneg_left hfactor' (le_of_lt hscale))
  have htarget : N / (N - 1) * (3 * N ^ 2 / (3 * N ^ 2 + 4)) =
      N / (N - 1) - 4 * N / ((N - 1) * (3 * N ^ 2 + 4)) := by
    field_simp [ne_of_gt hN0, ne_of_gt hN1]
    ring
  dsimp [N] at hmul2 htarget ⊢
  rw [← htarget]
  exact hmul2

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The quantitative odd gap for every reduced off-center success count. -/
theorem odd_normalized_proxy_reduced_fixed_sample_gap (n k m : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (hm : 0 < m) (hmn : m ≤ n) (hmN : m < 2 * n + 1) :
    normalizedHypergeomProxy (2 * n + 1) k m ≤
      (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) -
        (2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) - 3) /
          (((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - 1) *
            ((((2 * n + 1 : ℕ) : ℝ) ^ 2) + 3)) := by
  have hN : 2 * k < 2 * n + 1 := by omega
  by_cases hmk : m ≤ k
  · by_cases hm1 : m = 1
    · subst m
      rw [normalizedHypergeomProxy_singleton_subhalf (2 * n + 1) k hk hN]
      exact odd_imbalance_factor_offcenter_gap n k hn hk hkn
    · exact ((normalizedHypergeomProxy_inner_lt_bernoulli (2 * n + 1) k m
        (by omega) hmk hN).le.trans (odd_imbalance_factor_offcenter_gap n k hn hk hkn))
  · have hkm : k < m := by omega
    have hkN : k ≤ 2 * n + 1 := by omega
    have hNreal : (0 : ℝ) < (2 * n + 1 : ℕ) := by positivity
    have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hNmreal : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) - m := by
      exact sub_pos.mpr (by exact_mod_cast hmN)
    have hN1real : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) - 1 := by
      have : (1 : ℝ) < (2 * n + 1 : ℕ) := by exact_mod_cast (show 1 < 2 * n + 1 by omega)
      linarith
    have hkmR : (k : ℝ) < (m : ℝ) := by exact_mod_cast hkm
    have hsumR : (m : ℝ) + (k : ℝ) + 2 ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show m + k + 2 ≤ 2 * n + 1 by omega)
    have hNmkR : (2 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) - m - k := by
      linarith
    have hdiff1nat : k + 1 ≤ m := by omega
    have hdiff1R : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hdiff1nat
    have hdiff1 : (1 : ℝ) ≤ (m : ℝ) - k := by linarith
    have hprod2 : (2 : ℝ) ≤ ((m : ℝ) - k) *
        (((2 * n + 1 : ℕ) : ℝ) - m - k) := by
      have h := mul_le_mul hdiff1 hNmkR (by norm_num : (0 : ℝ) ≤ 2)
        (by linarith : (0 : ℝ) ≤ (m : ℝ) - k)
      nlinarith
    have hmin : (k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k) ≤
        (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) := by
      have hid : (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) -
          (k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k) =
          ((m : ℝ) - k) * (((2 * n + 1 : ℕ) : ℝ) - m - k) := by ring
      linarith
    have hcurv := hypergeomOptimalProxy_le_curvature (2 * n + 1) k m
      hkN (by omega)
    unfold sharpCurvatureConstant at hcurv
    rw [min_eq_left hmin] at hcurv
    have hscale : 0 ≤ 4 * ((2 * n + 1 : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m)) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hcurv hscale
    unfold normalizedHypergeomProxy
    have hgap : (2 : ℝ) ≤
        (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) -
          (k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k) := by
      have hid : (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) -
          (k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k) =
          ((m : ℝ) - k) * (((2 * n + 1 : ℕ) : ℝ) - m - k) := by ring
      rw [hid]
      exact hprod2
    have hmp_upper : (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) ≤
        (((2 * n + 1 : ℕ) : ℝ) ^ 2) / 4 := by
      nlinarith [sq_nonneg ((m : ℝ) - (((2 * n + 1 : ℕ) : ℝ) / 2))]
    have htarget :
        4 * ((2 * n + 1 : ℕ) : ℝ) /
            ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m)) *
          (((k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k)) /
            (4 * (((2 * n + 1 : ℕ) : ℝ) - 1))) ≤
        (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) -
          (2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) - 3) /
            (((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - 1) *
              ((((2 * n + 1 : ℕ) : ℝ) ^ 2) + 3)) := by
      have hBbound : (k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k) ≤
          (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) - 2 := by
        linarith [hgap]
      have hstep : (((2 * n + 1 : ℕ) : ℝ) ^ 2) *
          ((k : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - k)) *
          ((((2 * n + 1 : ℕ) : ℝ) ^ 2) + 3) ≤
          (((2 * n + 1 : ℕ) : ℝ) ^ 2) *
          ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) - 2) *
          ((((2 * n + 1 : ℕ) : ℝ) ^ 2) + 3) := by
        gcongr
      have hcoef : 0 ≤ 2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) + 6 -
          3 * ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m)) := by
        nlinarith [hmp_upper, sq_nonneg (((2 * n + 1 : ℕ) : ℝ))]
      have hcoefprod := mul_nonneg (sq_nonneg (((2 * n + 1 : ℕ) : ℝ))) hcoef
      field_simp [ne_of_gt hNreal, ne_of_gt hmreal, ne_of_gt hNmreal,
        ne_of_gt hN1real]
      nlinarith [hstep, hcoefprod]
    exact hscaled.trans htarget

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The quantitative even gap for every reduced off-center success count. -/
theorem even_normalized_proxy_reduced_fixed_sample_gap (q k m : ℕ)
    (hq : 0 < q) (hk : 0 < k) (hkq : k < q)
    (hm : 0 < m) (hmq : m ≤ q) (hmN : m < 2 * q) :
    normalizedHypergeomProxy (2 * q) k m ≤
      ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) -
        4 * ((2 * q : ℕ) : ℝ) /
          ((((2 * q : ℕ) : ℝ) - 1) *
            (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4)) := by
  have hN : 2 * k < 2 * q := by omega
  by_cases hmk : m ≤ k
  · by_cases hm1 : m = 1
    · subst m
      rw [normalizedHypergeomProxy_singleton_subhalf (2 * q) k hk hN]
      exact even_imbalance_factor_offcenter_gap q k hq hk hkq
    · exact ((normalizedHypergeomProxy_inner_lt_bernoulli (2 * q) k m
        (by omega) hmk hN).le.trans (even_imbalance_factor_offcenter_gap q k hq hk hkq))
  · have hkm : k < m := by omega
    have hkN : k ≤ 2 * q := by omega
    have hNreal : (0 : ℝ) < (2 * q : ℕ) := by positivity
    have hmreal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hNmreal : (0 : ℝ) < ((2 * q : ℕ) : ℝ) - m := by
      exact sub_pos.mpr (by exact_mod_cast hmN)
    have hN1real : (0 : ℝ) < ((2 * q : ℕ) : ℝ) - 1 := by
      have : (1 : ℝ) < (2 * q : ℕ) := by exact_mod_cast (show 1 < 2 * q by omega)
      linarith
    have hsumR : (m : ℝ) + (k : ℝ) + 1 ≤ ((2 * q : ℕ) : ℝ) := by
      exact_mod_cast (show m + k + 1 ≤ 2 * q by omega)
    have hNmkR : (1 : ℝ) ≤ ((2 * q : ℕ) : ℝ) - m - k := by
      linarith
    have hdiff1nat : k + 1 ≤ m := by omega
    have hdiff1R : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hdiff1nat
    have hdiff1 : (1 : ℝ) ≤ (m : ℝ) - k := by linarith
    have hprod1 : (1 : ℝ) ≤ ((m : ℝ) - k) *
        (((2 * q : ℕ) : ℝ) - m - k) := by
      have h := mul_le_mul hdiff1 hNmkR (by norm_num : (0 : ℝ) ≤ 1)
        (by linarith : (0 : ℝ) ≤ (m : ℝ) - k)
      nlinarith
    have hmin : (k : ℝ) * (((2 * q : ℕ) : ℝ) - k) ≤
        (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) := by
      have hid : (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) -
          (k : ℝ) * (((2 * q : ℕ) : ℝ) - k) =
          ((m : ℝ) - k) * (((2 * q : ℕ) : ℝ) - m - k) := by ring
      linarith
    have hcurv := hypergeomOptimalProxy_le_curvature (2 * q) k m
      hkN (by omega)
    unfold sharpCurvatureConstant at hcurv
    rw [min_eq_left hmin] at hcurv
    have hscale : 0 ≤ 4 * ((2 * q : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * q : ℕ) : ℝ) - m)) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hcurv hscale
    unfold normalizedHypergeomProxy
    have hgap : (1 : ℝ) ≤
        (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) -
          (k : ℝ) * (((2 * q : ℕ) : ℝ) - k) := by
      have hid : (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) -
          (k : ℝ) * (((2 * q : ℕ) : ℝ) - k) =
          ((m : ℝ) - k) * (((2 * q : ℕ) : ℝ) - m - k) := by ring
      rw [hid]
      exact hprod1
    have hmp_upper : (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) ≤
        (((2 * q : ℕ) : ℝ) ^ 2) / 4 := by
      nlinarith [sq_nonneg ((m : ℝ) - (((2 * q : ℕ) : ℝ) / 2))]
    have htarget :
        4 * ((2 * q : ℕ) : ℝ) /
            ((m : ℝ) * (((2 * q : ℕ) : ℝ) - m)) *
          (((k : ℝ) * (((2 * q : ℕ) : ℝ) - k)) /
            (4 * (((2 * q : ℕ) : ℝ) - 1))) ≤
        ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) -
          4 * ((2 * q : ℕ) : ℝ) /
            ((((2 * q : ℕ) : ℝ) - 1) *
              (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4)) := by
      have hBbound : (k : ℝ) * (((2 * q : ℕ) : ℝ) - k) ≤
          (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) - 1 := by
        linarith [hgap]
      have hstep : (((2 * q : ℕ) : ℝ) ^ 2) *
          ((k : ℝ) * (((2 * q : ℕ) : ℝ) - k)) *
          (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4) ≤
          (((2 * q : ℕ) : ℝ) ^ 2) *
          ((m : ℝ) * (((2 * q : ℕ) : ℝ) - m) - 1) *
          (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4) := by
        gcongr
      have hcoef : 0 ≤ 3 * (((2 * q : ℕ) : ℝ) ^ 2) + 4 -
          4 * ((m : ℝ) * (((2 * q : ℕ) : ℝ) - m)) := by
        nlinarith [hmp_upper, sq_nonneg (((2 * q : ℕ) : ℝ))]
      have hcoefprod := mul_nonneg (sq_nonneg (((2 * q : ℕ) : ℝ))) hcoef
      field_simp [ne_of_gt hNreal, ne_of_gt hmreal, ne_of_gt hNmreal,
        ne_of_gt hN1real]
      nlinarith [hstep, hcoefprod]
    exact hscaled.trans htarget

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The odd quantitative gap after both complement reductions. -/
theorem odd_normalized_proxy_fixed_sample_gap (n k m : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkN : k < 2 * n + 1)
    (hm : 0 < m) (hmN : m < 2 * n + 1)
    (hkc : k ≠ n) (hkc' : k ≠ n + 1) :
    normalizedHypergeomProxy (2 * n + 1) k m ≤
      (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) -
        (2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) - 3) /
          (((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - 1) *
            ((((2 * n + 1 : ℕ) : ℝ) ^ 2) + 3)) := by
  by_cases hmn : m ≤ n
  · by_cases hkn : k ≤ n
    · have hkn' : k < n := by omega
      exact odd_normalized_proxy_reduced_fixed_sample_gap n k m hn hk hkn' hm hmn hmN
    · have hkn' : n < k := by omega
      have hcomp : 0 < 2 * n + 1 - k := by omega
      have hcompN : 2 * n + 1 - k < n := by omega
      have hred := odd_normalized_proxy_reduced_fixed_sample_gap n (2 * n + 1 - k) m
        hn hcomp hcompN hm hmn hmN
      rw [normalizedHypergeomProxy_success_complement (2 * n + 1) k m
        hkN.le hmN.le (by omega)]
      exact hred
  · have hmcomp : 0 < 2 * n + 1 - m := by omega
    have hmcompN : 2 * n + 1 - m ≤ n := by omega
    rw [normalizedHypergeomProxy_sample_complement (2 * n + 1) k m
      hkN.le hmN.le (by omega)]
    exact odd_normalized_proxy_fixed_sample_gap n k (2 * n + 1 - m)
      hn hk hkN hmcomp (by omega) hkc hkc'

/-- The even quantitative gap after both complement reductions. -/
theorem even_normalized_proxy_fixed_sample_gap (q k m : ℕ)
    (hq : 0 < q) (hk : 0 < k) (hkN : k < 2 * q)
    (hm : 0 < m) (hmN : m < 2 * q)
    (hkc : k ≠ q) :
    normalizedHypergeomProxy (2 * q) k m ≤
      ((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) -
        4 * ((2 * q : ℕ) : ℝ) /
          ((((2 * q : ℕ) : ℝ) - 1) *
            (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4)) := by
  by_cases hmn : m ≤ q
  · by_cases hkn : k ≤ q
    · have hkn' : k < q := by omega
      exact even_normalized_proxy_reduced_fixed_sample_gap q k m hq hk hkn' hm hmn hmN
    · have hkn' : q < k := by omega
      have hcomp : 0 < 2 * q - k := by omega
      have hcompN : 2 * q - k < q := by omega
      have hred := even_normalized_proxy_reduced_fixed_sample_gap q (2 * q - k) m
        hq hcomp hcompN hm hmn hmN
      rw [normalizedHypergeomProxy_success_complement (2 * q) k m
        hkN.le hmN.le (by omega)]
      exact hred
  · have hmcomp : 0 < 2 * q - m := by omega
    rw [normalizedHypergeomProxy_sample_complement (2 * q) k m
      hkN.le hmN.le (by omega)]
    exact even_normalized_proxy_fixed_sample_gap q k (2 * q - m)
      hq hk hkN hmcomp (by omega) hkc

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The paper's even unnormalized finite-size gap. -/
theorem hypergeomOptimalProxy_fixed_sample_gap_even (q k m : ℕ)
    (hq : 0 < q) (hk : 0 < k) (hkN : k < 2 * q)
    (hm : 0 < m) (hmN : m < 2 * q) (hkc : k ≠ q) :
    hypergeomOptimalProxy (2 * q) k m ≤
      (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) /
          (4 * (((2 * q : ℕ) : ℝ) - 1)) -
        (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) /
          ((((2 * q : ℕ) : ℝ) - 1) *
            (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4)) := by
  have hnorm := even_normalized_proxy_fixed_sample_gap q k m hq hk hkN hm hmN hkc
  have hN0 : (0 : ℝ) < (2 * q : ℕ) := by positivity
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hNm0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) - m := by
    exact sub_pos.mpr (by exact_mod_cast hmN)
  have hB : 0 < (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) /
      (4 * ((2 * q : ℕ) : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hnorm (le_of_lt hB)
  change (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) /
      (4 * ((2 * q : ℕ) : ℝ)) *
      ((4 * ((2 * q : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * q : ℕ) : ℝ) - m))) *
        hypergeomOptimalProxy (2 * q) k m) ≤ _ at hmul
  have hinv : (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) /
      (4 * ((2 * q : ℕ) : ℝ)) *
      (4 * ((2 * q : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * q : ℕ) : ℝ) - m))) = 1 := by
    field_simp [ne_of_gt hN0, ne_of_gt hm0, ne_of_gt hNm0]
  rw [← mul_assoc, hinv, one_mul] at hmul
  have hright :
      (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) /
          (4 * ((2 * q : ℕ) : ℝ)) *
        (((2 * q : ℕ) : ℝ) / (((2 * q : ℕ) : ℝ) - 1) -
          4 * ((2 * q : ℕ) : ℝ) /
            ((((2 * q : ℕ) : ℝ) - 1) *
              (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4))) =
      (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) /
          (4 * (((2 * q : ℕ) : ℝ) - 1)) -
        (m : ℝ) * (((2 * q : ℕ) : ℝ) - m) /
          ((((2 * q : ℕ) : ℝ) - 1) *
            (3 * ((2 * q : ℕ) : ℝ) ^ 2 + 4)) := by
    field_simp [ne_of_gt hN0, ne_of_gt hNm0,
      show (0 : ℝ) < ((2 * q : ℕ) : ℝ) - 1 by
        exact sub_pos.mpr (by exact_mod_cast (show 1 < 2 * q by omega))]
  rw [hright] at hmul
  exact hmul

/-- The paper's odd unnormalized finite-size gap. -/
theorem hypergeomOptimalProxy_fixed_sample_gap_odd (n k m : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkN : k < 2 * n + 1)
    (hm : 0 < m) (hmN : m < 2 * n + 1)
    (hkc : k ≠ n) (hkc' : k ≠ n + 1) :
    hypergeomOptimalProxy (2 * n + 1) k m ≤
      (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) *
          ((((2 * n + 1 : ℕ) : ℝ) ^ 2) - 1) /
          (4 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) *
            (((2 * n + 1 : ℕ) : ℝ) - 1)) -
        (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) *
          (2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) - 3) /
          (4 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) *
            ((((2 * n + 1 : ℕ) : ℝ) ^ 2) + 3) *
            (((2 * n + 1 : ℕ) : ℝ) - 1)) := by
  have hnorm := odd_normalized_proxy_fixed_sample_gap n k m hn hk hkN hm hmN hkc hkc'
  have hN0 : (0 : ℝ) < (2 * n + 1 : ℕ) := by positivity
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hNm0 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) - m := by
    exact sub_pos.mpr (by exact_mod_cast hmN)
  have hB : 0 < (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) /
      (4 * ((2 * n + 1 : ℕ) : ℝ)) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hnorm (le_of_lt hB)
  change (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) /
      (4 * ((2 * n + 1 : ℕ) : ℝ)) *
      ((4 * ((2 * n + 1 : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m))) *
        hypergeomOptimalProxy (2 * n + 1) k m) ≤ _ at hmul
  have hinv : (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) /
      (4 * ((2 * n + 1 : ℕ) : ℝ)) *
      (4 * ((2 * n + 1 : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m))) = 1 := by
    field_simp [ne_of_gt hN0, ne_of_gt hm0, ne_of_gt hNm0]
  rw [← mul_assoc, hinv, one_mul] at hmul
  have hright :
      (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) /
          (4 * ((2 * n + 1 : ℕ) : ℝ)) *
        ((((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) -
          (2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) - 3) /
            (((2 * n + 1 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - 1) *
              ((((2 * n + 1 : ℕ) : ℝ) ^ 2) + 3))) =
      (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) *
          ((((2 * n + 1 : ℕ) : ℝ) ^ 2) - 1) /
          (4 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) *
            (((2 * n + 1 : ℕ) : ℝ) - 1)) -
        (m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m) *
          (2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) - 3) /
          (4 * (((2 * n + 1 : ℕ) : ℝ) ^ 2) *
            ((((2 * n + 1 : ℕ) : ℝ) ^ 2) + 3) *
            (((2 * n + 1 : ℕ) : ℝ) - 1)) := by
    field_simp [ne_of_gt hN0, ne_of_gt hm0, ne_of_gt hNm0,
      show (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) - 1 by
        exact sub_pos.mpr (by exact_mod_cast (show 1 < 2 * n + 1 by omega))]
    ring
  rw [hright] at hmul
  exact hmul

end
end ExactHoeffding
