import ExactHoeffding.ArtanhRatio
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The strict scalar coefficient behind compact finite-population contraction

The first inverse-population correction in the fixed-sample comparison is
proportional to

`d / ((1-d^2) * artanh d) - 1`.

This file isolates the strict positivity of that coefficient on the open
imbalance interval.  The proof uses the strict convexity of the logarithmic
odds function and its exact derivative, so the sign is independent of any
finite-population comparison theorem.
-/

namespace ExactHoeffding

noncomputable section

open Filter Set
open scoped Topology

/-- The scalar factor occurring in the first compact-population correction. -/
def artanhContractionFactor (d : ℝ) : ℝ :=
  d / ((1 - d ^ 2) * Real.artanh d) - 1

/-- Strict secant-versus-tangent inequality for logarithmic odds. -/
theorem logOdds_secant_lt_derivative (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    logOdds d / d < 2 / (1 - d ^ 2) := by
  have hs := logOdds_strictConvex.slope_lt_of_hasDerivAt
    (show (0 : ℝ) ∈ Ico 0 1 by simp)
    (show d ∈ Ico 0 1 from ⟨hd.le, hd1⟩)
    hd
    (logOdds_hasDerivAt d ⟨by linarith, hd1⟩)
  have hz : logOdds 0 = 0 := by simp [logOdds]
  simpa [slope_def_field, hz] using hs


/-- The inverse-tangent ratio has its removable value one at the balanced
point. -/
theorem artanh_hasDerivAt_zero : HasDerivAt Real.artanh 1 0 := by
  have hnum : HasDerivAt (fun x : ℝ => 1 + x) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add 1
  have hden : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 :=
    (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hquot : HasDerivAt (fun x : ℝ => (1 + x) / (1 - x)) 2 0 := by
    have h := hnum.div hden (by norm_num)
    convert h using 1 <;> try rfl
    norm_num
  have hlog : HasDerivAt
      (fun x : ℝ => Real.log ((1 + x) / (1 - x))) 2 0 := by
    have h := hquot.log (by norm_num)
    convert h using 1 <;> norm_num
  have hhalf : HasDerivAt
      (fun x : ℝ => (1 / 2 : ℝ) * Real.log ((1 + x) / (1 - x))) 1 0 := by
    have h := hlog.const_mul (1 / 2 : ℝ)
    have hc : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    rw [hc] at h
    exact h
  apply hhalf.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (show (-1 : ℝ) < 0 by norm_num)
    (show (0 : ℝ) < 1 by norm_num)] with x hx
  exact Real.artanh_eq_half_log ⟨hx.1, hx.2⟩

/-- The ratio `artanh d / d` extends continuously to one at zero. -/
theorem artanh_ratio_limit_zero :
    Tendsto (fun d : ℝ => Real.artanh d / d)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have h := artanh_hasDerivAt_zero.tendsto_slope
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  simp only [slope_def_field, sub_zero, Real.artanh_zero]

/-- Multiplication by the finite-population correction preserves the
removable ratio at zero. -/
theorem weighted_artanh_ratio_limit_zero :
    Tendsto (fun d : ℝ => (1 - d ^ 2) * (Real.artanh d / d))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hlin : Tendsto (fun d : ℝ => d)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    change Tendsto id (𝓝[≠] (0 : ℝ)) (𝓝 0)
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  have hquad : Tendsto (fun d : ℝ => d ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hlin.pow 2
  have hleft : Tendsto (fun d : ℝ => 1 - d ^ 2)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hquad
  simpa only [one_mul] using hleft.mul artanh_ratio_limit_zero

/-- The quotient occurring in the contraction factor has removable value
one at zero. -/
theorem artanh_ratio_denominator_limit_zero :
    Tendsto (fun d : ℝ => d / ((1 - d ^ 2) * Real.artanh d))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hden := weighted_artanh_ratio_limit_zero
  have hinv : Tendsto
      (fun d : ℝ => ((1 - d ^ 2) * (Real.artanh d / d))⁻¹)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)⁻¹) :=
    hden.inv₀ (by norm_num)
  have heq :
      (fun d : ℝ => d / ((1 - d ^ 2) * Real.artanh d)) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun d : ℝ => ((1 - d ^ 2) * (Real.artanh d / d))⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    field_simp [hd]
  rw [show (1 : ℝ)⁻¹ = 1 by norm_num] at hinv
  exact hinv.congr' heq.symm

/-- The unnormalised scalar gap vanishes continuously at the balanced
point. -/
theorem artanhContractionFactor_limit_zero :
    Tendsto artanhContractionFactor (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have h := artanh_ratio_denominator_limit_zero
  have hsub : Tendsto
      (fun d : ℝ => d / ((1 - d ^ 2) * Real.artanh d) - (1 : ℝ))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa using h.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
        (𝓝[≠] (0 : ℝ)) (𝓝 1))
  change Tendsto
      (fun d : ℝ => d / ((1 - d ^ 2) * Real.artanh d) - (1 : ℝ))
      (𝓝[≠] (0 : ℝ)) (𝓝 0)
  exact hsub

/-- The strict quadratic logarithmic-odds gap used by the compact
finite-population correction. -/
theorem logOdds_quadratic_strict (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    (1 - d ^ 2) * logOdds d < 2 * d := by
  have hsec := logOdds_secant_lt_derivative d hd hd1
  have hsq : 0 < 1 - d ^ 2 := by nlinarith
  have hmul := (div_lt_div_iff₀ hd hsq).mp hsec
  nlinarith only [hmul]

/-- The strict contraction factor is positive at every nonzero imbalance. -/
theorem artanhContractionFactor_pos (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    0 < artanhContractionFactor d := by
  have hlog : 0 < logOdds d := by
    unfold logOdds
    apply Real.log_pos
    apply (lt_div_iff₀ (by linarith : (0 : ℝ) < 1 - d)).2
    linarith
  have hsq : 0 < 1 - d ^ 2 := by nlinarith
  have hgap := logOdds_quadratic_strict d hd hd1
  have hart : 0 < Real.artanh d := by
    rw [Real.artanh_eq_half_log ⟨by linarith, hd1.le⟩]
    exact mul_pos (by norm_num) hlog
  have hden : 0 < (1 - d ^ 2) * Real.artanh d :=
    mul_pos hsq hart
  unfold artanhContractionFactor
  apply sub_pos.mpr
  apply (lt_div_iff₀ hden).2
  have hrel : 2 * Real.artanh d = logOdds d := by
    rw [Real.artanh_eq_half_log ⟨by linarith, hd1.le⟩]
    simp only [logOdds]
    ring
  rw [← hrel] at hgap
  nlinarith only [hgap]

/-- The factor has the equivalent positive numerator form used in the
first-order compact comparison. -/
theorem artanhContractionFactor_eq_gap (d : ℝ)
    (hd : 0 < d) (hd1 : d < 1) :
    artanhContractionFactor d =
      (d - (1 - d ^ 2) * Real.artanh d) /
        ((1 - d ^ 2) * Real.artanh d) := by
  have hsq : 1 - d ^ 2 ≠ 0 := by nlinarith [sq_nonneg d]
  have hlog : 0 < logOdds d := by
    unfold logOdds
    apply Real.log_pos
    apply (lt_div_iff₀ (by linarith : (0 : ℝ) < 1 - d)).2
    linarith
  have hart : Real.artanh d ≠ 0 := by
    have : 0 < Real.artanh d := by
      rw [Real.artanh_eq_half_log ⟨by linarith, hd1.le⟩]
      exact mul_pos (by norm_num) hlog
    exact ne_of_gt this
  unfold artanhContractionFactor
  field_simp [hsq, hart]

end

end ExactHoeffding
