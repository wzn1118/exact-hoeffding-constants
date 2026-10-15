import ExactHoeffding.BernoulliProxy
import ExactHoeffding.SingletonOptimalProxy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The sharp Bernoulli quadratic proxy

The sub-half estimate is proved in `BernoulliProxy`.  This file adds the
reflection identity, the balanced second-order lower bound, and the endpoint
cases, yielding the sharp coefficient on the closed Bernoulli parameter
interval.
-/

open Filter Set
open scoped Topology

namespace ExactHoeffding

noncomputable def bernoulliSharpBeta (p : ℝ) : ℝ :=
  if p = (1 / 2 : ℝ) then
    1 / 4
  else
    (1 - 2 * p) / (2 * Real.log ((1 - p) / p))

theorem bernoulli_centered_log_mgf_reflection (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    bernoulliCenteredLogMGF p t =
      bernoulliCenteredLogMGF (1 - p) (-t) := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hq1 : 1 - p < 1 := by linarith
  have hM : 0 < bernoulliMGF (1 - p) (-t) :=
    bernoulli_mgf_pos (1 - p) (-t) hq hq1
  have hfactor : bernoulliMGF p t =
      Real.exp t * bernoulliMGF (1 - p) (-t) := by
    unfold bernoulliMGF
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    ring
  unfold bernoulliCenteredLogMGF
  rw [hfactor, Real.log_mul (Real.exp_pos t).ne' hM.ne', Real.log_exp]
  ring

theorem bernoulli_centered_log_mgf_zero_param (t : ℝ) :
    bernoulliCenteredLogMGF 0 t = 0 := by
  simp [bernoulliCenteredLogMGF, bernoulliMGF]

theorem bernoulli_centered_log_mgf_one_param (t : ℝ) :
    bernoulliCenteredLogMGF 1 t = 0 := by
  simp [bernoulliCenteredLogMGF, bernoulliMGF]

theorem bernoulliSharpBeta_zero : bernoulliSharpBeta 0 = 0 := by
  norm_num [bernoulliSharpBeta]

theorem bernoulliSharpBeta_one : bernoulliSharpBeta 1 = 0 := by
  norm_num [bernoulliSharpBeta]

theorem bernoulliSharpBeta_half :
    bernoulliSharpBeta (1 / 2 : ℝ) = 1 / 4 := by
  simp [bernoulliSharpBeta]

theorem bernoulliSharpBeta_eq_formula (p : ℝ) (hp : p ≠ 1 / 2) :
    bernoulliSharpBeta p =
      (1 - 2 * p) / (2 * Real.log ((1 - p) / p)) := by
  rw [bernoulliSharpBeta, if_neg hp]

theorem bernoulliSharpBeta_reflection (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hpne : p ≠ 1 / 2) :
    bernoulliSharpBeta (1 - p) = bernoulliSharpBeta p := by
  have hqne : 1 - p ≠ 1 / 2 := by
    intro h
    apply hpne
    linarith
  rw [bernoulliSharpBeta_eq_formula (1 - p) hqne,
    bernoulliSharpBeta_eq_formula p hpne]
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hlog : Real.log (p / (1 - p)) =
      -Real.log ((1 - p) / p) := by
    rw [Real.log_div hp.ne' hq.ne', Real.log_div hq.ne' hp.ne']
    ring
  have hlog_ne : Real.log ((1 - p) / p) ≠ 0 := by
    intro hz
    have he := congrArg Real.exp hz
    rw [Real.exp_log (div_pos hq hp), Real.exp_zero] at he
    apply hpne
    have : 1 - p = p := (div_eq_one_iff_eq hp.ne').mp he
    linarith
  rw [show 1 - (1 - p) = p by ring, hlog]
  field_simp [hlog_ne] <;> ring

theorem bernoulli_quadratic_bound_subhalf (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) (t : ℝ) :
    bernoulliCenteredLogMGF p t ≤
      bernoulliSharpBeta p * t ^ 2 / 2 := by
  have hpne : p ≠ 1 / 2 := by linarith
  rw [bernoulliSharpBeta_eq_formula p hpne]
  exact bernoulli_quadratic_bound_lt_half p hp hp1 t

theorem bernoulli_subhalf_contact (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) :
    bernoulliCenteredLogMGF p (2 * Real.log ((1 - p) / p)) =
      bernoulliSharpBeta p * (2 * Real.log ((1 - p) / p)) ^ 2 / 2 := by
  have hpne : p ≠ 1 / 2 := by linarith
  have hlog : 0 < Real.log ((1 - p) / p) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hp).2
    linarith
  rw [bernoulliSharpBeta_eq_formula p hpne,
    bernoulli_centered_log_mgf_cosh_representation p
      (2 * Real.log ((1 - p) / p)) hp (by linarith)]
  have harg :
      (2 * Real.log ((1 - p) / p) - Real.log ((1 - p) / p)) / 2 =
        Real.log ((1 - p) / p) / 2 := by ring
  rw [harg]
  field_simp [ne_of_gt hlog] <;> ring

theorem bernoulli_subhalf_isOptimal (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) :
    IsOptimalQuadraticProxy (bernoulliCenteredLogMGF p)
      (bernoulliSharpBeta p) := by
  have hlog : 0 < Real.log ((1 - p) / p) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hp).2
    linarith
  exact optimalQuadraticProxy_of_contact _ _
    (2 * Real.log ((1 - p) / p))
    (fun t => bernoulli_quadratic_bound_subhalf p hp hp1 t)
    (by positivity)
    (bernoulli_subhalf_contact p hp hp1)

theorem bernoulli_quadratic_bound_gt_half (p : ℝ)
    (hp : 0 < p) (hph : 1 / 2 < p) (hp1 : p < 1) (t : ℝ) :
    bernoulliCenteredLogMGF p t ≤
      bernoulliSharpBeta p * t ^ 2 / 2 := by
  have hq : 0 < 1 - p := by linarith
  have hqhalf : 1 - p < 1 / 2 := by linarith
  have hpne : p ≠ 1 / 2 := by linarith
  have hbound := bernoulli_quadratic_bound_subhalf (1 - p) hq hqhalf (-t)
  rw [bernoulli_centered_log_mgf_reflection p t hp hp1,
    ← bernoulliSharpBeta_reflection p hp hp1 hpne]
  simpa only [neg_sq] using hbound

theorem bernoulli_gt_half_contact (p : ℝ)
    (hp : 0 < p) (hph : 1 / 2 < p) (hp1 : p < 1) :
    bernoulliCenteredLogMGF p (2 * Real.log ((1 - p) / p)) =
      bernoulliSharpBeta p * (2 * Real.log ((1 - p) / p)) ^ 2 / 2 := by
  have hq : 0 < 1 - p := by linarith
  have hqhalf : 1 - p < 1 / 2 := by linarith
  have hpne : p ≠ 1 / 2 := by linarith
  have hlog : Real.log (p / (1 - p)) =
      -Real.log ((1 - p) / p) := by
    rw [Real.log_div hp.ne' hq.ne', Real.log_div hq.ne' hp.ne']
    ring
  have hcontact := bernoulli_subhalf_contact (1 - p) hq hqhalf
  rw [bernoulli_centered_log_mgf_reflection p
      (2 * Real.log ((1 - p) / p)) hp hp1]
  have harg :
      -(2 * Real.log ((1 - p) / p)) =
        2 * Real.log (p / (1 - p)) := by
    rw [hlog]
    ring
  rw [harg, ← bernoulliSharpBeta_reflection p hp hp1 hpne]
  simpa only [show 1 - (1 - p) = p by ring, hlog, mul_neg, neg_sq] using hcontact

theorem bernoulli_gt_half_isOptimal (p : ℝ)
    (hp : 0 < p) (hph : 1 / 2 < p) (hp1 : p < 1) :
    IsOptimalQuadraticProxy (bernoulliCenteredLogMGF p)
      (bernoulliSharpBeta p) := by
  have hlog : Real.log ((1 - p) / p) < 0 := by
    apply Real.log_neg
    · exact div_pos (by linarith) hp
    · apply (div_lt_iff₀ hp).2
      linarith
  exact optimalQuadraticProxy_of_contact _ _
    (2 * Real.log ((1 - p) / p))
    (fun t => bernoulli_quadratic_bound_gt_half p hp hph hp1 t)
    (by nlinarith)
    (bernoulli_gt_half_contact p hp hph hp1)

theorem bernoulli_half_quadratic_limit :
    Tendsto
      (fun t => bernoulliCenteredLogMGF (1 / 2 : ℝ) t / t ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 ((1 / 4 : ℝ) / 2)) := by
  have hlim := hypergeom_centered_quadratic_limit 2 1 1 (by decide) (by decide)
  have hvar := hypergeomTiltVariance_zero_balanced_marks 1 1 (by decide) (by decide)
  norm_num at hvar
  rw [hypergeomCenteredLogMGF_singleton 2 1 (by decide) (by decide), hvar] at hlim
  norm_num only [Nat.cast_ofNat, Nat.cast_one] at hlim ⊢
  exact hlim

theorem bernoulli_half_isOptimal :
    IsOptimalQuadraticProxy (bernoulliCenteredLogMGF (1 / 2 : ℝ))
      (1 / 4 : ℝ) := by
  refine ⟨bernoulli_half_quadratic_bound, ?_⟩
  intro D hD
  exact quadraticProxy_lower_of_quotient_limit _ _ _
    bernoulli_half_quadratic_limit hD

theorem bernoulli_zero_isOptimal :
    IsOptimalQuadraticProxy (bernoulliCenteredLogMGF 0)
      (bernoulliSharpBeta 0) := by
  rw [bernoulliSharpBeta_zero]
  apply optimalQuadraticProxy_of_contact _ _ 1
  · intro t
    simp [bernoulli_centered_log_mgf_zero_param]
  · norm_num
  · simp [bernoulli_centered_log_mgf_zero_param]

theorem bernoulli_one_isOptimal :
    IsOptimalQuadraticProxy (bernoulliCenteredLogMGF 1)
      (bernoulliSharpBeta 1) := by
  rw [bernoulliSharpBeta_one]
  apply optimalQuadraticProxy_of_contact _ _ 1
  · intro t
    simp [bernoulli_centered_log_mgf_one_param]
  · norm_num
  · simp [bernoulli_centered_log_mgf_one_param]

theorem bernoulli_sharp_quadratic_bound (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsQuadraticProxy (bernoulliCenteredLogMGF p)
      (bernoulliSharpBeta p) := by
  by_cases h0 : p = 0
  · subst p
    exact (bernoulli_zero_isOptimal).1
  by_cases h1 : p = 1
  · subst p
    exact (bernoulli_one_isOptimal).1
  by_cases hh : p = 1 / 2
  · subst p
    simpa only [bernoulliSharpBeta_half] using
      (bernoulli_half_isOptimal).1
  by_cases hlt : p < 1 / 2
  · exact fun t => bernoulli_quadratic_bound_subhalf p
      (lt_of_le_of_ne hp (Ne.symm h0)) hlt t
  have hph : 1 / 2 < p := by
    have hle : 1 / 2 ≤ p := le_of_not_gt hlt
    exact lt_of_le_of_ne hle (by intro h; exact hh h.symm)
  exact fun t => bernoulli_quadratic_bound_gt_half p
    (lt_of_le_of_ne hp (Ne.symm h0)) hph
    (lt_of_le_of_ne hp1 h1) t

theorem bernoulli_sharp_quadratic_optimal (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsOptimalQuadraticProxy (bernoulliCenteredLogMGF p)
      (bernoulliSharpBeta p) := by
  by_cases h0 : p = 0
  · subst p
    exact bernoulli_zero_isOptimal
  by_cases h1 : p = 1
  · subst p
    exact bernoulli_one_isOptimal
  by_cases hh : p = 1 / 2
  · subst p
    simpa only [bernoulliSharpBeta_half] using bernoulli_half_isOptimal
  by_cases hlt : p < 1 / 2
  · exact bernoulli_subhalf_isOptimal p
      (lt_of_le_of_ne hp (Ne.symm h0)) hlt
  · have hph : 1 / 2 < p := by
      have hle : 1 / 2 ≤ p := le_of_not_gt hlt
      exact lt_of_le_of_ne hle (by intro h; exact hh h.symm)
    exact bernoulli_gt_half_isOptimal p
      (lt_of_le_of_ne hp (Ne.symm h0)) hph
      (lt_of_le_of_ne hp1 h1)

end ExactHoeffding
