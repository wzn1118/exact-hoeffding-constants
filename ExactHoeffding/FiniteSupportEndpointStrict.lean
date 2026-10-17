import ExactHoeffding.FiniteSupportLawEnvelope

/-! # Strict variance-envelope comparison at support endpoints

A positive gap at a fixed interior target persists to every more distant
target. The proof writes the gap as a nonnegative tilt-coordinate integral.
A finite one-sided limit of the envelope integral then gives a strict
endpoint comparison without regularity assumptions on the envelope there.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

private def endpointGapCoefficient (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (s : ℝ) : ℝ := 1 - D.variance s / Q (D.mean s)

private lemma endpointGapCoefficient_continuous
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo D.lo D.hi))
    (hQpos : ∀ u ∈ Ioo D.lo D.hi, 0 < Q u) :
    Continuous (endpointGapCoefficient D Q) := by
  have hm : Continuous D.mean := continuous_iff_continuousAt.mpr
    (fun s => (D.mean_deriv s).continuousAt)
  have hcomp : Continuous (fun s => Q (D.mean s)) := by
    apply continuousOn_univ.mp
    exact hQ.comp hm.continuousOn (fun s _ => D.mean_range s)
  exact continuous_const.sub
    (D.variance_continuous.div hcomp (fun s => (hQpos _ (D.mean_range s)).ne'))

private lemma endpointGapCoefficient_nonneg
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQpos : ∀ u ∈ Ioo D.lo D.hi, 0 < Q u)
    (hV : ∀ s : ℝ, D.variance s ≤ Q (D.mean s)) (s : ℝ) :
    0 ≤ endpointGapCoefficient D Q s := by
  dsimp [endpointGapCoefficient]
  exact sub_nonneg.mpr ((div_le_one (hQpos _ (D.mean_range s))).mpr (hV s))

private lemma endpoint_candidate_hasDerivAt
    (D : FiniteSupportTiltCurve) (v s : ℝ) :
    HasDerivAt (fun z : ℝ => z * v - D.logMGF z) (v - D.mean s) s := by
  have hd := (hasDerivAt_id s).const_mul v |>.sub (D.logMGF_deriv s)
  have hfun : (fun z : ℝ => z * v - D.logMGF z) =
      ((fun y : ℝ => v * id y) - D.logMGF) := by
    funext z
    dsimp
    ring
  rw [hfun]
  exact hd.congr_deriv (by ring)

/-- The right gap is a tilt-coordinate integral of the relative variance
slack. This formula only uses the envelope on the open support interval. -/
theorem finiteSupportLegendreRate_sub_meanEnvelopeRateRight_eq_integral_open
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo D.lo D.hi))
    (hQpos : ∀ u ∈ Ioo D.lo D.hi, 0 < Q u)
    {v : ℝ} (hmu : D.mu < v) (hhi : v < D.hi) :
    finiteSupportLegendreRate D v - finiteSupportMeanEnvelopeRateRight D Q v =
      ∫ s : ℝ in 0..finiteSupportMeanInverse D v,
        (v - D.mean s) * (1 - D.variance s / Q (D.mean s)) := by
  let t := finiteSupportMeanInverse D v
  have htmean : D.mean t = v := finiteSupportMeanInverse_spec D
    (D.hlomu.trans hmu) hhi
  have hm : Continuous D.mean := continuous_iff_continuousAt.mpr
    (fun s => (D.mean_deriv s).continuousAt)
  have hcomp : Continuous (fun s => Q (D.mean s)) := by
    apply continuousOn_univ.mp
    exact hQ.comp hm.continuousOn (fun s _ => D.mean_range s)
  let A : ℝ → ℝ := fun s => (v - D.mean s) / Q (D.mean s) * D.variance s
  let B : ℝ → ℝ := fun s => v - D.mean s
  have hA : Continuous A :=
    ((continuous_const.sub hm).div hcomp
      (fun s => (hQpos _ (D.mean_range s)).ne')).mul D.variance_continuous
  have hB : Continuous B := continuous_const.sub hm
  have hAi : IntervalIntegrable A MeasureTheory.volume 0 t := hA.intervalIntegrable _ _
  have hBi : IntervalIntegrable B MeasureTheory.volume 0 t := hB.intervalIntegrable _ _
  have hchange0 := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := t) (f := D.mean) (f' := D.variance)
    (g := fun u : ℝ => (v - u) / Q u) hm.continuousOn
    (fun s _ => D.mean_deriv s) (fun s _ => (D.variance_pos s).le)
  have hchange : finiteSupportMeanEnvelopeRateRight D Q v =
      ∫ s : ℝ in 0..t, A s := by
    simpa [finiteSupportMeanEnvelopeRateRight, A, D.mean_zero, htmean,
      Function.comp_def] using hchange0.symm
  have hfund0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => endpoint_candidate_hasDerivAt D v s) hBi
  have hfund : (∫ s : ℝ in 0..t, B s) = finiteSupportLegendreRate D v := by
    rw [finiteSupportLegendreRate_at_mean D (D.hlomu.trans hmu) hhi]
    dsimp [B] at hfund0 ⊢
    rw [hfund0, D.logMGF_zero]
    ring
  rw [hchange, ← hfund, ← intervalIntegral.integral_sub hBi hAi]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp [B, A]
  ring

/-- Left counterpart of the tilt-coordinate gap identity. -/
theorem finiteSupportLegendreRate_sub_meanEnvelopeRateLeft_eq_integral_open
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo D.lo D.hi))
    (hQpos : ∀ u ∈ Ioo D.lo D.hi, 0 < Q u)
    {v : ℝ} (hlo : D.lo < v) (hmu : v < D.mu) :
    finiteSupportLegendreRate D v - finiteSupportMeanEnvelopeRateLeft D Q v =
      ∫ s : ℝ in finiteSupportMeanInverse D v..0,
        (D.mean s - v) * (1 - D.variance s / Q (D.mean s)) := by
  let t := finiteSupportMeanInverse D v
  have htmean : D.mean t = v := finiteSupportMeanInverse_spec D hlo
    (hmu.trans D.hmuhi)
  have hm : Continuous D.mean := continuous_iff_continuousAt.mpr
    (fun s => (D.mean_deriv s).continuousAt)
  have hcomp : Continuous (fun s => Q (D.mean s)) := by
    apply continuousOn_univ.mp
    exact hQ.comp hm.continuousOn (fun s _ => D.mean_range s)
  let A : ℝ → ℝ := fun s => (D.mean s - v) / Q (D.mean s) * D.variance s
  let B : ℝ → ℝ := fun s => D.mean s - v
  have hA : Continuous A :=
    ((hm.sub continuous_const).div hcomp
      (fun s => (hQpos _ (D.mean_range s)).ne')).mul D.variance_continuous
  have hB : Continuous B := hm.sub continuous_const
  have hAi : IntervalIntegrable A MeasureTheory.volume t 0 := hA.intervalIntegrable _ _
  have hBi : IntervalIntegrable B MeasureTheory.volume t 0 := hB.intervalIntegrable _ _
  have hchange0 := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := t) (b := (0 : ℝ)) (f := D.mean) (f' := D.variance)
    (g := fun u : ℝ => (u - v) / Q u) hm.continuousOn
    (fun s _ => D.mean_deriv s) (fun s _ => (D.variance_pos s).le)
  have hchange : finiteSupportMeanEnvelopeRateLeft D Q v =
      ∫ s : ℝ in t..0, A s := by
    simpa [finiteSupportMeanEnvelopeRateLeft, A, D.mean_zero, htmean,
      Function.comp_def] using hchange0.symm
  have hUi : IntervalIntegrable (fun s : ℝ => v - D.mean s)
      MeasureTheory.volume t 0 := (continuous_const.sub hm).intervalIntegrable _ _
  have hfund0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => endpoint_candidate_hasDerivAt D v s) hUi
  have hfund : (∫ s : ℝ in t..0, B s) = finiteSupportLegendreRate D v := by
    rw [finiteSupportLegendreRate_at_mean D hlo (hmu.trans D.hmuhi)]
    have hneg : (∫ s : ℝ in t..0, B s) =
        -(∫ s : ℝ in t..0, v - D.mean s) := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro s _
      dsimp [B]
      ring
    rw [hneg, hfund0, D.logMGF_zero]
    ring
  rw [hchange, ← hfund, ← intervalIntegral.integral_sub hBi hAi]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp [B, A]
  ring

/-- The right rate gap cannot shrink as the target moves outward. -/
theorem finiteSupportLegendreRate_sub_meanEnvelopeRateRight_mono_open
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo D.lo D.hi))
    (hQpos : ∀ u ∈ Ioo D.lo D.hi, 0 < Q u)
    (hV : ∀ s : ℝ, D.variance s ≤ Q (D.mean s))
    {v₀ v : ℝ} (hmu : D.mu < v₀) (hvv : v₀ ≤ v) (hhi : v < D.hi) :
    finiteSupportLegendreRate D v₀ - finiteSupportMeanEnvelopeRateRight D Q v₀ ≤
      finiteSupportLegendreRate D v - finiteSupportMeanEnvelopeRateRight D Q v := by
  let t₀ := finiteSupportMeanInverse D v₀
  let t := finiteSupportMeanInverse D v
  have hmono : StrictMono D.mean := strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
  have ht₀mean : D.mean t₀ = v₀ := finiteSupportMeanInverse_spec D
    (D.hlomu.trans hmu) (hvv.trans_lt hhi)
  have htmean : D.mean t = v := finiteSupportMeanInverse_spec D
    (D.hlomu.trans (hmu.trans_le hvv)) hhi
  have h0t₀ : 0 ≤ t₀ := by
    apply hmono.le_iff_le.mp
    rw [D.mean_zero, ht₀mean]
    exact hmu.le
  have ht₀t : t₀ ≤ t := hmono.le_iff_le.mp (by simpa [ht₀mean, htmean] using hvv)
  let G : ℝ → ℝ → ℝ := fun w s => (w - D.mean s) * endpointGapCoefficient D Q s
  have hm : Continuous D.mean := continuous_iff_continuousAt.mpr
    (fun s => (D.mean_deriv s).continuousAt)
  have hG : ∀ w, Continuous (G w) := fun w =>
    (continuous_const.sub hm).mul (endpointGapCoefficient_continuous D Q hQ hQpos)
  rw [finiteSupportLegendreRate_sub_meanEnvelopeRateRight_eq_integral_open D Q hQ hQpos
    hmu (hvv.trans_lt hhi),
    finiteSupportLegendreRate_sub_meanEnvelopeRateRight_eq_integral_open D Q hQ hQpos
    (hmu.trans_le hvv) hhi]
  change (∫ s : ℝ in 0..t₀, G v₀ s) ≤ ∫ s : ℝ in 0..t, G v s
  have hfirst : (∫ s : ℝ in 0..t₀, G v₀ s) ≤ ∫ s : ℝ in 0..t₀, G v s := by
    apply intervalIntegral.integral_mono_on h0t₀
      ((hG v₀).intervalIntegrable _ _) ((hG v).intervalIntegrable _ _)
    intro s _
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right hvv _)
      (endpointGapCoefficient_nonneg D Q hQpos hV s)
  have hnonneg : 0 ≤ ∫ s : ℝ in t₀..t, G v s := by
    apply intervalIntegral.integral_nonneg ht₀t
    intro s hs
    have hms : D.mean s ≤ v := by
      simpa [htmean] using hmono.monotone hs.2
    exact mul_nonneg (sub_nonneg.mpr hms)
      (endpointGapCoefficient_nonneg D Q hQpos hV s)
  have hadd : (∫ s : ℝ in 0..t₀, G v s) + (∫ s : ℝ in t₀..t, G v s) =
      ∫ s : ℝ in 0..t, G v s :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hG v).intervalIntegrable 0 t₀) ((hG v).intervalIntegrable t₀ t)
  linarith only [hfirst, hnonneg, hadd]

/-- The left rate gap cannot shrink as the target moves outward. -/
theorem finiteSupportLegendreRate_sub_meanEnvelopeRateLeft_mono_open
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo D.lo D.hi))
    (hQpos : ∀ u ∈ Ioo D.lo D.hi, 0 < Q u)
    (hV : ∀ s : ℝ, D.variance s ≤ Q (D.mean s))
    {v₀ v : ℝ} (hlo : D.lo < v) (hvv : v ≤ v₀) (hmu : v₀ < D.mu) :
    finiteSupportLegendreRate D v₀ - finiteSupportMeanEnvelopeRateLeft D Q v₀ ≤
      finiteSupportLegendreRate D v - finiteSupportMeanEnvelopeRateLeft D Q v := by
  let t₀ := finiteSupportMeanInverse D v₀
  let t := finiteSupportMeanInverse D v
  have hmono : StrictMono D.mean := strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
  have ht₀mean : D.mean t₀ = v₀ := finiteSupportMeanInverse_spec D (hlo.trans_le hvv)
    (hmu.trans D.hmuhi)
  have htmean : D.mean t = v := finiteSupportMeanInverse_spec D hlo
    ((hvv.trans_lt hmu).trans D.hmuhi)
  have ht₀0 : t₀ ≤ 0 := by
    apply hmono.le_iff_le.mp
    rw [D.mean_zero, ht₀mean]
    exact hmu.le
  have htt₀ : t ≤ t₀ := hmono.le_iff_le.mp (by simpa [ht₀mean, htmean] using hvv)
  let G : ℝ → ℝ → ℝ := fun w s => (D.mean s - w) * endpointGapCoefficient D Q s
  have hm : Continuous D.mean := continuous_iff_continuousAt.mpr
    (fun s => (D.mean_deriv s).continuousAt)
  have hG : ∀ w, Continuous (G w) := fun w =>
    (hm.sub continuous_const).mul (endpointGapCoefficient_continuous D Q hQ hQpos)
  rw [finiteSupportLegendreRate_sub_meanEnvelopeRateLeft_eq_integral_open D Q hQ hQpos
    (hlo.trans_le hvv) hmu,
    finiteSupportLegendreRate_sub_meanEnvelopeRateLeft_eq_integral_open D Q hQ hQpos
    hlo (hvv.trans_lt hmu)]
  change (∫ s : ℝ in t₀..0, G v₀ s) ≤ ∫ s : ℝ in t..0, G v s
  have hfirst : (∫ s : ℝ in t₀..0, G v₀ s) ≤ ∫ s : ℝ in t₀..0, G v s := by
    apply intervalIntegral.integral_mono_on ht₀0
      ((hG v₀).intervalIntegrable _ _) ((hG v).intervalIntegrable _ _)
    intro s _
    exact mul_le_mul_of_nonneg_right (sub_le_sub_left hvv _)
      (endpointGapCoefficient_nonneg D Q hQpos hV s)
  have hnonneg : 0 ≤ ∫ s : ℝ in t..t₀, G v s := by
    apply intervalIntegral.integral_nonneg htt₀
    intro s hs
    have hms : v ≤ D.mean s := by
      simpa [htmean] using hmono.monotone hs.1
    exact mul_nonneg (sub_nonneg.mpr hms)
      (endpointGapCoefficient_nonneg D Q hQpos hV s)
  have hadd : (∫ s : ℝ in t..t₀, G v s) + (∫ s : ℝ in t₀..0, G v s) =
      ∫ s : ℝ in t..0, G v s :=
    intervalIntegral.integral_add_adjacent_intervals
      ((hG v).intervalIntegrable t t₀) ((hG v).intervalIntegrable t₀ 0)
  linarith only [hfirst, hnonneg, hadd]

end
end ExactHoeffding
