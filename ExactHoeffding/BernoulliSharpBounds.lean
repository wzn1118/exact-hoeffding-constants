import ExactHoeffding.BernoulliOptimal
import ExactHoeffding.ParityProxyComparison

namespace ExactHoeffding

/-- The sharp Bernoulli proxy is at most the universal quarter coefficient;
strictness holds away from the balanced parameter and deterministic endpoints. -/
theorem bernoulliSharpBeta_le_quarter (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliSharpBeta p ≤ 1 / 4 := by
  by_cases h0 : p = 0
  · subst p
    norm_num [bernoulliSharpBeta]
  by_cases h1 : p = 1
  · subst p
    norm_num [bernoulliSharpBeta]
  by_cases hh : p = 1 / 2
  · subst p
    norm_num [bernoulliSharpBeta]
  by_cases hph : p < 1 / 2
  · have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm h0)
    have hlog : 0 < Real.log ((1-p)/p) := by
      apply Real.log_pos
      exact (lt_div_iff₀ hp).2 (by linarith)
    rw [bernoulliSharpBeta_eq_formula p hh]
    apply (div_le_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hlog)).2
    have hd0 : 0 < 1-2*p := by linarith
    have hd1 : 1-2*p < 1 := by linarith
    have h := logOdds_gt_twice (1-2*p) hd0 hd1
    have heq : logOdds (1-2*p) = Real.log ((1-p)/p) := by
      unfold logOdds
      congr 1
      field_simp
      ring
    rw [heq] at h
    nlinarith
  · have hph' : 1 / 2 < p := lt_of_le_of_ne (le_of_not_gt hph) (Ne.symm hh)
    have hp : p < 1 := lt_of_le_of_ne hp1 h1
    have hq : 0 < 1-p := sub_pos.mpr (by linarith)
    have hlog : Real.log ((1-p)/p) < 0 := by
      apply Real.log_neg
      · exact div_pos hq (by linarith)
      · exact (div_lt_iff₀ (by linarith : (0:ℝ)<p)).2 (by linarith)
    rw [bernoulliSharpBeta_eq_formula p hh]
    have hden : 2 * Real.log ((1-p)/p) < 0 := by linarith
    apply (div_le_iff_of_neg hden).2
    have hd0 : 0 < 2*p-1 := by linarith
    have hd1 : 2*p-1 < 1 := by linarith
    have h := logOdds_gt_twice (2*p-1) hd0 hd1
    have heq : logOdds (2*p-1) = -Real.log ((1-p)/p) := by
      unfold logOdds
      have hq : 0 < 1-p := sub_pos.mpr (by linarith)
      have hrat : (1+(2*p-1))/(1-(2*p-1)) = p/(1-p) := by
        rw [show 1-(2*p-1)=2*(1-p) by ring,
          show 1+(2*p-1)=2*p by ring]
        field_simp [hq.ne']
      rw [hrat, Real.log_div (by linarith : p ≠ 0) hq.ne', Real.log_div hq.ne' (by linarith : p ≠ 0)]
      ring
    rw [heq] at h
    nlinarith

/-- The inequality is strict for every nonbalanced interior Bernoulli law. -/
theorem bernoulliSharpBeta_lt_quarter {p : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hpne : p ≠ 1 / 2) :
    bernoulliSharpBeta p < 1 / 4 := by
  rw [bernoulliSharpBeta_eq_formula p hpne]
  by_cases hph : p < 1 / 2
  · have hlog : 0 < Real.log ((1-p)/p) := by
      apply Real.log_pos
      exact (lt_div_iff₀ hp0).2 (by linarith)
    apply (div_lt_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hlog)).2
    have hd0 : 0 < 1-2*p := by linarith
    have hd1 : 1-2*p < 1 := by linarith
    have h := logOdds_gt_twice (1-2*p) hd0 hd1
    have heq : logOdds (1-2*p) = Real.log ((1-p)/p) := by
      unfold logOdds
      congr 1
      field_simp
      ring
    rw [heq] at h
    nlinarith
  · have hph' : 1 / 2 < p := lt_of_le_of_ne (le_of_not_gt hph) (Ne.symm hpne)
    have hlog : Real.log ((1-p)/p) < 0 := by
      apply Real.log_neg
      · exact div_pos (sub_pos.mpr (by linarith)) hp0
      · exact (div_lt_iff₀ hp0).2 (by linarith)
    have hden : 2 * Real.log ((1-p)/p) < 0 := by linarith
    apply (div_lt_iff_of_neg hden).2
    have hd0 : 0 < 2*p-1 := by linarith
    have hd1 : 2*p-1 < 1 := by linarith
    have h := logOdds_gt_twice (2*p-1) hd0 hd1
    have heq : logOdds (2*p-1) = -Real.log ((1-p)/p) := by
      unfold logOdds
      have hq : 0 < 1-p := sub_pos.mpr (by linarith)
      have hrat : (1+(2*p-1))/(1-(2*p-1)) = p/(1-p) := by
        rw [show 1-(2*p-1)=2*(1-p) by ring,
          show 1+(2*p-1)=2*p by ring]
        field_simp [hq.ne']
      rw [hrat, Real.log_div hp0.ne' hq.ne', Real.log_div hq.ne' hp0.ne']
      ring
    rw [heq] at h
    nlinarith

end ExactHoeffding
