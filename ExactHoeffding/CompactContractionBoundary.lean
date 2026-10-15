import ExactHoeffding.AnalyticContractionCoefficient
import Mathlib.Analysis.Calculus.LHopital

/-! # The balanced boundary value of the analytic contraction coefficient -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

/-- The derivative of inverse hyperbolic tangent throughout its open domain. -/
theorem artanh_hasDerivAt_open (d : ℝ) (hd : d ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt Real.artanh (1 / (1 - d ^ 2)) d := by
  have h := (logOdds_hasDerivAt d hd).const_mul (1 / 2 : ℝ)
  rw [show (1 / 2 : ℝ) * (2 / (1 - d ^ 2)) = 1 / (1 - d ^ 2) by ring] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hd] with x hx
  exact Real.artanh_eq_half_log ⟨hx.1.le, hx.2.le⟩

/-- The positive numerator of the contraction gap has cubic leading term. -/
theorem artanh_contraction_numerator_cubic_limit :
    Tendsto (fun d : ℝ => (d - (1 - d ^ 2) * Real.artanh d) / d ^ 3)
      (𝓝[≠] 0) (𝓝 (2 / 3 : ℝ)) := by
  let f : ℝ → ℝ := fun d => d - (1 - d ^ 2) * Real.artanh d
  have hderiv (d : ℝ) (hd : d ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt f (2 * d * Real.artanh d) d := by
    have h := (hasDerivAt_id d).sub
      (((hasDerivAt_id d).pow 2).const_sub 1 |>.mul (artanh_hasDerivAt_open d hd))
    have hne : 1 - d ^ 2 ≠ 0 := by nlinarith [hd.1, hd.2]
    norm_num only [Pi.pow_apply, id_eq, pow_one, Nat.cast_ofNat, mul_one] at h
    change HasDerivAt f (1 - ((-(2 * d)) * Real.artanh d +
      (1 - d ^ 2) * (1 / (1 - d ^ 2)))) d at h
    have heq : 1 - ((-(2 * d)) * Real.artanh d +
        (1 - d ^ 2) * (1 / (1 - d ^ 2))) = 2 * d * Real.artanh d := by
      field_simp [hne]
      <;> ring
    rwa [heq] at h
  have hsmall : ∀ᶠ d : ℝ in 𝓝[≠] 0, d ∈ Ioo (-1 : ℝ) 1 :=
    eventually_nhdsWithin_of_eventually_nhds (isOpen_Ioo.mem_nhds (by norm_num))
  have hquot : Tendsto (fun d : ℝ => (2 * d * Real.artanh d) / (3 * d ^ 2))
      (𝓝[≠] 0) (𝓝 (2 / 3 : ℝ)) := by
    have h := artanh_ratio_limit_zero.const_mul (2 / 3 : ℝ)
    norm_num only [mul_one] at h
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with d hd
    field_simp [hd]
  exact HasDerivAt.lhopital_zero_nhdsNE
    (hsmall.mono fun d hd => hderiv d hd)
    (Filter.Eventually.of_forall fun d => by
      simpa only [Nat.cast_ofNat, Nat.reduceSub] using hasDerivAt_pow 3 d)
    (by
      filter_upwards [self_mem_nhdsWithin] with d hd
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (show d ≠ 0 from hd)))
    (by
      have h := (hderiv 0 (by norm_num)).continuousAt.tendsto
      simpa [f] using h.mono_left nhdsWithin_le_nhds)
    (by
      have h : Tendsto (fun d : ℝ => d ^ 3) (𝓝 0) (𝓝 0) := by
        simpa using (tendsto_id.pow 3 : Tendsto (fun d : ℝ => d ^ 3) (𝓝 0) (𝓝 ((0 : ℝ) ^ 3)))
      exact h.mono_left nhdsWithin_le_nhds)
    hquot

/-- The removable quadratic coefficient of the strict contraction factor. -/
theorem artanhContractionFactor_quadratic_limit_zero :
    Tendsto (fun d : ℝ => artanhContractionFactor d / d ^ 2)
      (𝓝[≠] 0) (𝓝 (2 / 3 : ℝ)) := by
  have h := artanh_contraction_numerator_cubic_limit.div
    weighted_artanh_ratio_limit_zero (by norm_num)
  norm_num only [div_one] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds
      (isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num))] with d hd hs
  have hd0 : d ≠ 0 := hd
  have hsq : 1 - d ^ 2 ≠ 0 := by nlinarith [hs.1, hs.2]
  have hart : Real.artanh d ≠ 0 := by
    intro hz
    rcases Real.artanh_eq_zero_iff.mp hz with hleft | hzero | hright
    · linarith [hs.1]
    · exact hd0 hzero
    · linarith [hs.2]
  dsimp only [Pi.div_apply]
  unfold artanhContractionFactor
  field_simp [hd0, hart, hsq]

/-- The coefficient on the limiting success-proportion axis. -/
def compactContractionBoundary (m : ℕ) (d : ℝ) : ℝ :=
  if d = 0 then 2 * ((m : ℝ) - 1) / 3
  else ((m : ℝ) - 1) * (d / Real.artanh d) / d ^ 2 * artanhContractionFactor d

theorem compactContractionBoundary_limit_zero (m : ℕ) :
    Tendsto (fun d : ℝ => ((m : ℝ) - 1) * (d / Real.artanh d) / d ^ 2 *
      artanhContractionFactor d) (𝓝[≠] 0) (𝓝 (2 * ((m : ℝ) - 1) / 3)) := by
  have hratio := artanh_ratio_limit_zero.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simp only [inv_one, inv_div] at hratio
  have h := (hratio.const_mul ((m : ℝ) - 1)).mul
    artanhContractionFactor_quadratic_limit_zero
  convert h using 1
  · funext d; ring
  · ring

@[simp] theorem compactContractionBoundary_zero (m : ℕ) :
    compactContractionBoundary m 0 = 2 * ((m : ℝ) - 1) / 3 := by
  simp [compactContractionBoundary]

theorem compactContractionBoundary_continuousAt_zero (m : ℕ) :
    ContinuousAt (compactContractionBoundary m) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simp only [compactContractionBoundary_zero]
  apply (compactContractionBoundary_limit_zero m).congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  simp [compactContractionBoundary, show d ≠ 0 from hd]

/-- Positivity includes the removable balanced point. -/
theorem compactContractionBoundary_pos (m : ℕ) (hm : 2 ≤ m)
    (d : ℝ) (hd : 0 ≤ d) (hd1 : d < 1) : 0 < compactContractionBoundary m d := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  by_cases hz : d = 0
  · simp only [hz, compactContractionBoundary_zero]
    positivity
  · have hd0 : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
    rw [compactContractionBoundary, if_neg hz]
    exact mul_pos (div_pos (mul_pos (by linarith)
      (div_pos hd0 (Real.artanh_pos ⟨hd0, hd1⟩))) (sq_pos_of_ne_zero hz))
      (artanhContractionFactor_pos d hd0 hd1)

theorem compactContractionBoundary_continuousAt_pos (m : ℕ) (d : ℝ)
    (hd : 0 < d) (hd1 : d < 1) : ContinuousAt (compactContractionBoundary m) d := by
  have ha := (artanh_hasDerivAt_open d ⟨by linarith, hd1⟩).continuousAt
  have hane : Real.artanh d ≠ 0 := (Real.artanh_pos ⟨hd, hd1⟩).ne'
  have hsq : 1 - d ^ 2 ≠ 0 := by nlinarith
  have hgap : ContinuousAt artanhContractionFactor d := by
    unfold artanhContractionFactor
    exact (continuousAt_id.div
      ((continuousAt_const.sub (continuousAt_id.pow 2)).mul ha)
      (mul_ne_zero hsq hane)).sub continuousAt_const
  have hraw : ContinuousAt (fun x : ℝ => ((m : ℝ) - 1) *
      (x / Real.artanh x) / x ^ 2 * artanhContractionFactor x) d :=
    ((continuousAt_const.mul (continuousAt_id.div ha hane)).div
    (continuousAt_id.pow 2) (pow_ne_zero 2 hd.ne')).mul hgap
  apply hraw.congr_of_eventuallyEq
  filter_upwards [continuousAt_id.eventually_ne hd.ne'] with x hx
  exact if_neg hx

theorem compactContractionBoundary_continuousOn (m : ℕ) (d₀ : ℝ) (hd₁ : d₀ < 1) :
    ContinuousOn (compactContractionBoundary m) (Icc 0 d₀) := by
  intro d hd
  by_cases hz : d = 0
  · subst d
    exact (compactContractionBoundary_continuousAt_zero m).continuousWithinAt
  · exact (compactContractionBoundary_continuousAt_pos m d
      (lt_of_le_of_ne hd.1 (Ne.symm hz)) (lt_of_le_of_lt hd.2 hd₁)).continuousWithinAt

/-- The strictly positive limiting contraction coefficient is uniformly
bounded below on every compact subinterval up to the balanced endpoint. -/
theorem compactContractionBoundary_uniform_pos (m : ℕ) (hm : 2 ≤ m)
    (d₀ : ℝ) (hd₀ : 0 ≤ d₀) (hd₁ : d₀ < 1)
    :
    ∃ c : ℝ, 0 < c ∧ ∀ d ∈ Icc 0 d₀, c ≤ compactContractionBoundary m d := by
  obtain ⟨d, hd, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr hd₀) (compactContractionBoundary_continuousOn m d₀ hd₁)
  exact ⟨compactContractionBoundary m d,
    compactContractionBoundary_pos m hm d hd.1 (lt_of_le_of_lt hd.2 hd₁), hmin⟩

end
end ExactHoeffding
