import ExactHoeffding.GoalBFixedSample
import ExactHoeffding.RescaledActualProxy
import ExactHoeffding.RescaledMixedDerivative
import Mathlib.Analysis.Calculus.DerivativeTest

namespace ExactHoeffding
noncomputable section
open Set Filter SignType
open scoped Topology

private lemma exists_proxy_gt_zero_tilt_of_deriv_ne_zero {f : ℝ → ℝ} {d : ℝ}
    (hf : HasDerivAt f d 0) (hd : d ≠ 0) :
    ∃ t : ℝ, t ≠ 0 ∧ f t > f 0 := by
  by_cases hp : 0 < d
  · let g : ℝ → ℝ := fun x => f x - f 0
    have hg : HasDerivAt g d 0 := hf.sub_const _
    have hg0 : g 0 = 0 := by simp [g]
    have hder : deriv g 0 = d := hg.deriv
    have hs := eventually_nhdsWithin_sign_eq_of_deriv_pos
      (f := g) (x₀ := (0 : ℝ)) (by rw [hder]; exact hp) hg0
    have hprop : ∀ᶠ x in 𝓝 (0 : ℝ), 0 < x → 0 < g x := by
      filter_upwards [hs] with x hx hxp
      have hsg : sign (g x) = 1 := by
        rw [hx, sign_pos (sub_pos.mpr hxp)]
      exact (sign_eq_one_iff).mp hsg
    obtain ⟨t, ht, hgt⟩ := hprop.exists_gt
    refine ⟨t, ne_of_gt ht, ?_⟩
    simpa [g] using hgt ht
  · have hn : d < 0 := lt_of_le_of_ne (le_of_not_gt hp) hd
    let g : ℝ → ℝ := fun x => f x - f 0
    have hg : HasDerivAt g d 0 := hf.sub_const _
    have hg0 : g 0 = 0 := by simp [g]
    have hder : deriv g 0 = d := hg.deriv
    have hs := eventually_nhdsWithin_sign_eq_of_deriv_neg
      (f := g) (x₀ := (0 : ℝ)) (by rw [hder]; exact hn) hg0
    have hprop : ∀ᶠ x in 𝓝 (0 : ℝ), x < 0 → 0 < g x := by
      filter_upwards [hs] with x hx hxn
      have hsg : sign (g x) = 1 := by
        rw [hx, sign_pos (sub_pos.mpr hxn)]
      exact (sign_eq_one_iff).mp hsg
    obtain ⟨t, ht, hgt⟩ := hprop.exists_lt
    refine ⟨t, ne_of_lt ht, ?_⟩
    simpa [g] using hgt ht

private theorem actualHypergeomProxy_gt_variance_of_deriv_ne_zero
    (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) (hmpos : 1 ≤ m)
    (hderiv : HasDerivAt (actualHypergeomProxy N k m)
      (deriv (actualHypergeomProxy N k m) 0) 0)
    (hderiv_ne : deriv (actualHypergeomProxy N k m) 0 ≠ 0) :
    hypergeomCumulant2 N k m < hypergeomOptimalProxy N k m := by
  obtain ⟨t, ht, hgt⟩ :=
    exists_proxy_gt_zero_tilt_of_deriv_ne_zero hderiv hderiv_ne
  have hproxy : actualHypergeomProxy N k m t ≤ hypergeomOptimalProxy N k m := by
    unfold actualHypergeomProxy
    rw [if_neg ht]
    change 2 * Real.log (centeredHypergeomMGF N k m t) / t ^ 2 ≤ _
    rw [hypergeom_centered_log_identity N k m hk hm t]
    apply le_csSup (proxyQuotientSet_bddAbove
      (hypergeomCenteredLogMGF N k m) (sharpCurvatureConstant N k m)
      (hypergeom_uniform_log_laplace_domination N k m hk hm))
    exact ⟨t, ht, rfl⟩
  have hzero : actualHypergeomProxy N k m 0 = hypergeomCumulant2 N k m := by
    simp [actualHypergeomProxy]
  rw [hzero] at hgt
  exact hgt.trans_le hproxy

/-- At every odd central success count, the finite hypergeometric proxy is
strictly larger than its ordinary variance.  The proof uses the exact
nonzero first tilt derivative of the removable proxy; no asymptotic argument
is involved. -/
theorem hypergeomOptimalProxy_odd_center_gt_variance (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hmN : m < 2 * n + 1) :
    hypergeomCumulant2 (2 * n + 1) n m <
      hypergeomOptimalProxy (2 * n + 1) n m := by
  let N : ℕ := 2 * n + 1
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hk : n ≤ N := by dsimp [N]; omega
  have hmle : m ≤ N := by dsimp [N]; omega
  have hmpos : 1 ≤ m := by omega
  have hbal : 2 * (n : ℝ) + 1 = (N : ℝ) := by
    dsimp [N]
    push_cast
    ring
  have hfun : rescaledProxyExtension m 1 (1 / (N : ℝ)) =
      actualHypergeomProxy N n m := by
    funext t
    exact rescaledProxyExtension_hypergeom N n m 1 t hN hk hmle hmpos hbal
  have hder_ext := rescaledProxyExtension_hasDerivAt_tilt_zero m 1 (1 / (N : ℝ))
  have hder_ext' : HasDerivAt (rescaledProxyExtension m 1 (1 / (N : ℝ)))
      (deriv (rescaledProxyExtension m 1 (1 / (N : ℝ))) 0) 0 :=
    hder_ext.congr_deriv hder_ext.deriv.symm
  have hder : HasDerivAt (actualHypergeomProxy N n m)
      (deriv (rescaledProxyExtension m 1 (1 / (N : ℝ))) 0) 0 := by
    apply hder_ext'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun t => (congrFun hfun t).symm)
  have hNpos : (0 : ℝ) < N := by positivity
  have h1pos : 0 < 1 - (1 / (N : ℝ)) := by
    apply sub_pos.mpr
    have hfrac : (1 : ℝ) / N < 1 := by
      apply (div_lt_iff₀ hNpos).2
      norm_num
      exact_mod_cast (show 1 < N by omega)
    exact hfrac
  have h2pos : 0 < 1 - 2 * (1 / (N : ℝ)) := by
    apply sub_pos.mpr
    have hfrac : (2 : ℝ) / N < 1 := by
      apply (div_lt_iff₀ hNpos).2
      norm_num
      exact_mod_cast (show 2 < N by omega)
    convert hfrac using 1 <;> field_simp [hNpos.ne']
  have h1 : 1 - (1 / (N : ℝ)) ≠ 0 := h1pos.ne'
  have h2 : 1 - 2 * (1 / (N : ℝ)) ≠ 0 := h2pos.ne'
  have hformula := rescaledProxyExtension_deriv_tilt_zero m 1 (1 / (N : ℝ)) h1 h2
  have hder_ne : deriv (actualHypergeomProxy N n m) 0 ≠ 0 := by
    rw [hder.deriv, hformula]
    have hNr : (0 : ℝ) < N := by positivity
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hmNR : (m : ℝ) < N := by exact_mod_cast hmN
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hN2 : (2 : ℝ) < N := by exact_mod_cast (show 2 < N by omega)
    have hmn : (m : ℝ) ≠ N / 2 := by
      by_cases hmn' : m ≤ n
      · have hmRle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn'
        have hNr : (0 : ℝ) < N := by positivity
        intro heq
        dsimp [N] at heq
        push_cast at heq
        nlinarith
      · have hmn'' : n < m := by omega
        have hmnR : (n : ℝ) + 1 ≤ (m : ℝ) := by
          exact_mod_cast (show n + 1 ≤ m by omega)
        intro heq
        dsimp [N] at heq
        push_cast at heq
        nlinarith
    have hfactor : (1 - 2 * (m : ℝ) / N) ≠ 0 := by
      intro hz
      apply hmn
      field_simp at hz
      linarith
    have hpos1 : 0 < (m : ℝ) := hmR
    have hpos2 : 0 < (1 / N : ℝ) := by positivity
    have hpos3 : 0 < 1 - (1 / N : ℝ) ^ 2 := by
      have hx : 0 ≤ (1 / N : ℝ) := by positivity
      have hx1 : (1 / N : ℝ) < 1 := by
        apply (div_lt_iff₀ hNr).2
        norm_num
        exact_mod_cast (show 1 < N by omega)
      nlinarith
    have hpos4 : 0 < 1 - (m : ℝ) / N := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hNr).2
      simpa using hmNR
    have hden : 12 * (1 - (1 / N : ℝ)) * (1 - 2 * (1 / N : ℝ)) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) h1) h2
    have hnum' : (m : ℝ) * (1 / N) * (1 - (1 / N) ^ 2) *
        (1 - (m : ℝ) / N) * (1 - 2 * (m : ℝ) / N) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        hpos1.ne' (div_ne_zero (by norm_num) hNr.ne')) hpos3.ne')
        hpos4.ne') hfactor
    have hnum : (m : ℝ) * 1 * (1 / N) * (1 - 1 ^ 2 * (1 / N) ^ 2) *
        (1 - (m : ℝ) * (1 / N)) * (1 - 2 * (m : ℝ) * (1 / N)) ≠ 0 := by
      simpa [one_mul, one_pow, div_eq_mul_inv] using hnum'
    exact div_ne_zero hnum hden
  have hder' : HasDerivAt (actualHypergeomProxy N n m)
      (deriv (actualHypergeomProxy N n m) 0) 0 :=
    hder.congr_deriv hder.deriv.symm
  exact actualHypergeomProxy_gt_variance_of_deriv_ne_zero N n m hk hmle hmpos hder' hder_ne

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The odd central normalized proxy is strictly above the normalized
ordinary-variance benchmark appearing in the manuscript. -/
theorem odd_normalized_proxy_center_gt_variance (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hmN : m < 2 * n + 1) :
    (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) <
      normalizedHypergeomProxy (2 * n + 1) n m := by
  have hvar := hypergeomOptimalProxy_odd_center_gt_variance n m hn hm hmN
  have hNpos : (0 : ℝ) < (2 * n + 1 : ℕ) := by positivity
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmNR : (m : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by exact_mod_cast hmN
  have hscale : 0 < 4 * ((2 * n + 1 : ℕ) : ℝ) /
      ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m)) := by positivity
  have hmul := mul_lt_mul_of_pos_left hvar hscale
  rw [hypergeom_cumulant2_complete (2 * n + 1) n m (by omega) (by omega)] at hmul
  rw [Nat.cast_sub (show n ≤ 2 * n + 1 by omega),
    Nat.cast_sub (show m ≤ 2 * n + 1 by omega)] at hmul
  unfold normalizedHypergeomProxy
  have hNm : ((2 * n + 1 : ℕ) : ℝ) - m ≠ 0 :=
    (sub_pos.mpr hmNR).ne'
  have hN1pos : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) - 1 := by
    apply sub_pos.mpr
    exact_mod_cast (show 1 < 2 * n + 1 by omega)
  have hN1 : ((2 * n + 1 : ℕ) : ℝ) - 1 ≠ 0 := hN1pos.ne'
  have heq :
      (4 * ((2 * n + 1 : ℕ) : ℝ) /
        ((m : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - m))) *
        (((m : ℝ) * (n : ℝ) * (((2 * n + 1 : ℕ) : ℝ) - n) *
          (((2 * n + 1 : ℕ) : ℝ) - m)) /
          (((2 * n + 1 : ℕ) : ℝ) ^ 2 * (((2 * n + 1 : ℕ) : ℝ) - 1))) =
        (((2 * n + 1 : ℕ) : ℝ) + 1) /
          ((2 * n + 1 : ℕ) : ℝ) := by
    field_simp [hNpos.ne', hmR.ne', hNm, hN1]
    push_cast
    ring
  rw [heq] at hmul
  exact hmul

/-- The fixed-sample odd theorem in the manuscript's max-and-strictness form. -/
theorem odd_fixed_sample_max_strict (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hmN : m < 2 * n + 1) :
    (∀ k : ℕ, 0 < k → k < 2 * n + 1 →
      normalizedHypergeomProxy (2 * n + 1) k m ≤
          normalizedHypergeomProxy (2 * n + 1) n m ∧
        (normalizedHypergeomProxy (2 * n + 1) k m =
          normalizedHypergeomProxy (2 * n + 1) n m ↔ k = n ∨ k = n + 1)) ∧
      (((2 * n + 1 : ℕ) : ℝ) + 1) / ((2 * n + 1 : ℕ) : ℝ) <
        normalizedHypergeomProxy (2 * n + 1) n m := by
  refine ⟨?_, odd_normalized_proxy_center_gt_variance n m hn hm hmN⟩
  intro k hk hkN
  exact odd_normalized_proxy_fixed_sample_extremizers n k m hn hk hkN hm hmN

end
end ExactHoeffding
