import ExactHoeffding.FiniteSupportMeanEnvelope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith

/-!
# Strict finite-support mean-coordinate envelope comparison

The non-strict comparison is complemented here by the exact strictness
criterion.  A strict variance gap at one interior tilt produces a strict
rate gap after the monotone tilted-mean change of variables.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

private theorem strict_mean_local
    (D : FiniteSupportTiltCurve) : StrictMono D.mean := by
  exact strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos

private theorem continuous_mean_local
    (D : FiniteSupportTiltCurve) : Continuous D.mean := by
  exact continuous_iff_continuousAt.mpr (fun t =>
    (D.mean_deriv t).continuousAt)

private theorem candidate_deriv_local
    (D : FiniteSupportTiltCurve) (v s : ℝ) :
    HasDerivAt (fun z : ℝ => z * v - D.logMGF z)
      (v - D.mean s) s := by
  have h := (hasDerivAt_id s).const_mul v |>.sub (D.logMGF_deriv s)
  have hfun :
      (fun z : ℝ => z * v - D.logMGF z) =
        ((fun y : ℝ => v * id y) - D.logMGF) := by
    funext z
    dsimp
    ring
  rw [hfun]
  exact h.congr_deriv (by ring)


/-- A strict variance gap on the positive tilt segment gives a strict
right-sided Legendre comparison. -/
theorem finiteSupportLegendreRate_gt_meanEnvelopeRateRight_of_strict
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Set.Icc D.lo D.hi, 0 < Q u)
    (hV : ∀ t : ℝ, D.variance t ≤ Q (D.mean t))
    {v : ℝ} (hvμ : D.mu < v) (hvhi : v < D.hi)
    (hstrict : ∃ c ∈ Set.Ioo (0 : ℝ)
        (finiteSupportMeanInverse D v),
        D.variance c < Q (D.mean c)) :
    finiteSupportMeanEnvelopeRateRight D Q v <
      finiteSupportLegendreRate D v := by
  let t : ℝ := finiteSupportMeanInverse D v
  have htmean : D.mean t = v := finiteSupportMeanInverse_spec D
    (lt_trans D.hlomu hvμ) hvhi
  have ht0 : 0 < t := by
    by_contra hnt
    have hle : t ≤ 0 := le_of_not_gt hnt
    have hmean : D.mean t ≤ D.mean 0 :=
      (strict_mean_local D).monotone hle
    linarith [htmean, D.mean_zero, hvμ]
  obtain ⟨c, hc, hgap⟩ := hstrict
  have hcg : c < t := hc.2
  have hmc : D.mean c < v := by
    have hmono := strict_mean_local D
    have hmean : D.mean c < D.mean t := hmono hcg
    linarith [htmean]
  have hmean_cont : Continuous D.mean := continuous_mean_local D
  let A : ℝ → ℝ := fun s =>
    ((v - D.mean s) / Q (D.mean s)) * D.variance s
  let B : ℝ → ℝ := fun s => v - D.mean s
  have hAB : ∀ s ∈ Set.Icc (0 : ℝ) t, A s ≤ B s := by
    intro s hs
    have hms : D.mean s ∈ Set.Icc D.lo D.hi :=
      ⟨(D.mean_range s).1.le, (D.mean_range s).2.le⟩
    have hq : 0 < Q (D.mean s) := hQpos _ hms
    have hdiff : 0 ≤ v - D.mean s := by
      have hmono := strict_mean_local D
      have hmean : D.mean s ≤ D.mean t := hmono.monotone hs.2
      linarith [htmean]
    have hv := hV s
    dsimp [A, B]
    have hdiv : (v - D.mean s) * D.variance s / Q (D.mean s) ≤
        v - D.mean s := by
      apply (div_le_iff₀ hq).2
      exact mul_le_mul_of_nonneg_left hv hdiff
    calc
      (v - D.mean s) / Q (D.mean s) * D.variance s =
          (v - D.mean s) * D.variance s / Q (D.mean s) := by ring
      _ ≤ v - D.mean s := hdiv
  have hAc : A c < B c := by
    dsimp [A, B]
    have hms : D.mean c ∈ Set.Icc D.lo D.hi :=
      ⟨(D.mean_range c).1.le, (D.mean_range c).2.le⟩
    have hq : 0 < Q (D.mean c) := hQpos _ hms
    have hdiff : 0 < v - D.mean c := by linarith [hmc]
    have hmul := mul_lt_mul_of_pos_left hgap hdiff
    calc
      (v - D.mean c) / Q (D.mean c) * D.variance c =
          (v - D.mean c) * D.variance c / Q (D.mean c) := by ring
      _ < v - D.mean c := by
        apply (div_lt_iff₀ hq).2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hAcont : ContinuousOn A (Set.Icc (0 : ℝ) t) := by
    have hmc' : ContinuousOn (fun s : ℝ => Q (D.mean s))
        (Set.Icc (0 : ℝ) t) :=
      hQ.continuousOn.comp hmean_cont.continuousOn (fun _ _ => mem_univ _)
    have hqne : ∀ s ∈ Set.Icc (0 : ℝ) t, Q (D.mean s) ≠ 0 := by
      intro s hs
      exact ne_of_gt (hQpos _ ⟨(D.mean_range s).1.le,
        (D.mean_range s).2.le⟩)
    dsimp [A]
    exact ((continuousOn_const.sub hmean_cont.continuousOn).div hmc' hqne).mul
      D.variance_continuous.continuousOn
  have hBcont : ContinuousOn B (Set.Icc (0 : ℝ) t) := by
    dsimp [B]
    exact continuousOn_const.sub hmean_cont.continuousOn
  have hAcont' : ContinuousOn A (uIcc (0 : ℝ) t) := by
    simpa [uIcc_of_le ht0.le] using hAcont
  have hBcont' : ContinuousOn B (uIcc (0 : ℝ) t) := by
    simpa [uIcc_of_le ht0.le] using hBcont
  have hAi : IntervalIntegrable A MeasureTheory.volume 0 t :=
    hAcont'.intervalIntegrable
  have hBi : IntervalIntegrable B MeasureTheory.volume 0 t :=
    hBcont'.intervalIntegrable
  have hABoc : ∀ s ∈ Set.Ioc (0 : ℝ) t, A s ≤ B s := by
    intro s hs
    exact hAB s ⟨hs.1.le, hs.2⟩
  have hineq :
      (∫ s : ℝ in (0 : ℝ)..t, A s) <
        ∫ s : ℝ in (0 : ℝ)..t, B s := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (a := (0 : ℝ)) (b := t) ht0
      hAcont hBcont hABoc
    exact ⟨c, ⟨hc.1.le, hc.2.le⟩, hAc⟩
  have hchange0 := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := t) (f := D.mean) (f' := D.variance)
    (g := fun s : ℝ => (v - s) / Q s)
    hmean_cont.continuousOn
    (fun s hs => D.mean_deriv s)
    (fun s hs => (D.variance_pos s).le)
  have hchange :
      finiteSupportMeanEnvelopeRateRight D Q v =
        ∫ s : ℝ in (0 : ℝ)..t, A s := by
    dsimp [finiteSupportMeanEnvelopeRateRight, A]
    calc
      (∫ s : ℝ in D.mu..v, (v - s) / Q s) =
          ∫ s : ℝ in D.mean 0..D.mean t, (v - s) / Q s := by
            rw [D.mean_zero, htmean]
      _ = ∫ s : ℝ in (0 : ℝ)..t,
          ((fun r : ℝ => (v - r) / Q r) ∘ D.mean) s * D.variance s :=
        hchange0.symm
      _ = ∫ s : ℝ in (0 : ℝ)..t,
          ((v - D.mean s) / Q (D.mean s)) * D.variance s := by rfl
  have hUi : IntervalIntegrable (fun s : ℝ => v - D.mean s)
      MeasureTheory.volume 0 t := by
    have hnegB : (fun s : ℝ => v - D.mean s) = B := by
      funext s
      dsimp [B]
    rw [hnegB]
    exact hBi
  have hfund0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => candidate_deriv_local D v s) hUi
  have hfund :
      (∫ s : ℝ in (0 : ℝ)..t, B s) = t * v - D.logMGF t := by
    dsimp [B] at hfund0 ⊢
    rw [hfund0, D.logMGF_zero]
    ring
  have hrate : t * v - D.logMGF t ≤ finiteSupportLegendreRate D v := by
    exact le_of_eq (finiteSupportLegendreRate_at_mean D
      (lt_trans D.hlomu hvμ) hvhi).symm
  calc
    finiteSupportMeanEnvelopeRateRight D Q v =
        ∫ s : ℝ in (0 : ℝ)..t, A s := hchange
    _ < ∫ s : ℝ in (0 : ℝ)..t, B s := hineq
    _ = t * v - D.logMGF t := hfund
    _ ≤ finiteSupportLegendreRate D v := hrate


/-- A strict variance gap on the negative tilt segment gives a strict
left-sided Legendre comparison. -/
theorem finiteSupportLegendreRate_gt_meanEnvelopeRateLeft_of_strict
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Set.Icc D.lo D.hi, 0 < Q u)
    (hV : ∀ t : ℝ, D.variance t ≤ Q (D.mean t))
    {v : ℝ} (hvlo : D.lo < v) (hvμ : v < D.mu)
    (hstrict : ∃ c ∈ Set.Ioo (finiteSupportMeanInverse D v) (0 : ℝ),
        D.variance c < Q (D.mean c)) :
    finiteSupportMeanEnvelopeRateLeft D Q v <
      finiteSupportLegendreRate D v := by
  let t : ℝ := finiteSupportMeanInverse D v
  have htmean : D.mean t = v := finiteSupportMeanInverse_spec D
    hvlo (lt_trans hvμ D.hmuhi)
  have ht0 : t < 0 := by
    by_contra hnt
    have hle : 0 ≤ t := le_of_not_gt hnt
    have hmean : D.mean 0 ≤ D.mean t :=
      (strict_mean_local D).monotone hle
    linarith [htmean, D.mean_zero, hvμ]
  obtain ⟨c, hc, hgap⟩ := hstrict
  have hmc : v < D.mean c := by
    have hmono := strict_mean_local D
    have hmean : D.mean t < D.mean c := hmono hc.1
    linarith [htmean]
  have hmean_cont : Continuous D.mean := continuous_mean_local D
  let A : ℝ → ℝ := fun s =>
    ((D.mean s - v) / Q (D.mean s)) * D.variance s
  let B : ℝ → ℝ := fun s => D.mean s - v
  have hAB : ∀ s ∈ Set.Icc t (0 : ℝ), A s ≤ B s := by
    intro s hs
    have hms : D.mean s ∈ Set.Icc D.lo D.hi :=
      ⟨(D.mean_range s).1.le, (D.mean_range s).2.le⟩
    have hq : 0 < Q (D.mean s) := hQpos _ hms
    have hdiff : 0 ≤ D.mean s - v := by
      have hmono := strict_mean_local D
      have hmean : D.mean t ≤ D.mean s := hmono.monotone hs.1
      linarith [htmean]
    have hv := hV s
    dsimp [A, B]
    have hdiv : (D.mean s - v) * D.variance s / Q (D.mean s) ≤
        D.mean s - v := by
      apply (div_le_iff₀ hq).2
      exact mul_le_mul_of_nonneg_left hv hdiff
    calc
      (D.mean s - v) / Q (D.mean s) * D.variance s =
          (D.mean s - v) * D.variance s / Q (D.mean s) := by ring
      _ ≤ D.mean s - v := hdiv
  have hAc : A c < B c := by
    dsimp [A, B]
    have hms : D.mean c ∈ Set.Icc D.lo D.hi :=
      ⟨(D.mean_range c).1.le, (D.mean_range c).2.le⟩
    have hq : 0 < Q (D.mean c) := hQpos _ hms
    have hdiff : 0 < D.mean c - v := by linarith [hmc]
    have hmul := mul_lt_mul_of_pos_left hgap hdiff
    calc
      (D.mean c - v) / Q (D.mean c) * D.variance c =
          (D.mean c - v) * D.variance c / Q (D.mean c) := by ring
      _ < D.mean c - v := by
        apply (div_lt_iff₀ hq).2
        simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  have hAcont : ContinuousOn A (Set.Icc t (0 : ℝ)) := by
    have hmc' : ContinuousOn (fun s : ℝ => Q (D.mean s))
        (Set.Icc t (0 : ℝ)) :=
      hQ.continuousOn.comp hmean_cont.continuousOn (fun _ _ => mem_univ _)
    have hqne : ∀ s ∈ Set.Icc t (0 : ℝ), Q (D.mean s) ≠ 0 := by
      intro s hs
      exact ne_of_gt (hQpos _ ⟨(D.mean_range s).1.le,
        (D.mean_range s).2.le⟩)
    dsimp [A]
    exact ((hmean_cont.continuousOn.sub continuousOn_const).div hmc' hqne).mul
      D.variance_continuous.continuousOn
  have hBcont : ContinuousOn B (Set.Icc t (0 : ℝ)) := by
    dsimp [B]
    exact hmean_cont.continuousOn.sub continuousOn_const
  have hAcont' : ContinuousOn A (uIcc t (0 : ℝ)) := by
    simpa [uIcc_of_le ht0.le] using hAcont
  have hBcont' : ContinuousOn B (uIcc t (0 : ℝ)) := by
    simpa [uIcc_of_le ht0.le] using hBcont
  have hAi : IntervalIntegrable A MeasureTheory.volume t 0 :=
    hAcont'.intervalIntegrable
  have hBi : IntervalIntegrable B MeasureTheory.volume t 0 :=
    hBcont'.intervalIntegrable
  have hABoc : ∀ s ∈ Set.Ioc t (0 : ℝ), A s ≤ B s := by
    intro s hs
    exact hAB s ⟨hs.1.le, hs.2⟩
  have hineq :
      (∫ s : ℝ in t..(0 : ℝ), A s) <
        ∫ s : ℝ in t..(0 : ℝ), B s := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (a := t) (b := (0 : ℝ)) ht0
      hAcont hBcont hABoc
    exact ⟨c, ⟨hc.1.le, hc.2.le⟩, hAc⟩
  have hchange0 := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := t) (b := (0 : ℝ)) (f := D.mean) (f' := D.variance)
    (g := fun s : ℝ => (s - v) / Q s)
    hmean_cont.continuousOn
    (fun s hs => D.mean_deriv s)
    (fun s hs => (D.variance_pos s).le)
  have hchange :
      finiteSupportMeanEnvelopeRateLeft D Q v =
        ∫ s : ℝ in t..(0 : ℝ), A s := by
    dsimp [finiteSupportMeanEnvelopeRateLeft, A]
    calc
      (∫ s : ℝ in v..D.mu, (s - v) / Q s) =
          ∫ s : ℝ in D.mean t..D.mean 0, (s - v) / Q s := by
            rw [htmean, D.mean_zero]
      _ = ∫ s : ℝ in t..(0 : ℝ),
          ((fun r : ℝ => (r - v) / Q r) ∘ D.mean) s * D.variance s :=
        hchange0.symm
      _ = ∫ s : ℝ in t..(0 : ℝ),
          ((D.mean s - v) / Q (D.mean s)) * D.variance s := by rfl
  have hUi : IntervalIntegrable (fun s : ℝ => v - D.mean s)
      MeasureTheory.volume t 0 := by
    have hnegB : (fun s : ℝ => v - D.mean s) = -B := by
      funext s
      dsimp [B]
      ring
    rw [hnegB]
    exact hBi.neg
  have hfund0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => candidate_deriv_local D v s) hUi
  have hfund :
      (∫ s : ℝ in t..(0 : ℝ), B s) = t * v - D.logMGF t := by
    have hneg :
        (∫ s : ℝ in t..(0 : ℝ), B s) =
          - (∫ s : ℝ in t..(0 : ℝ), v - D.mean s) := by
      simp only [B]
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext s
      ring
    rw [hneg, hfund0, D.logMGF_zero]
    ring
  have hrate : t * v - D.logMGF t ≤ finiteSupportLegendreRate D v := by
    exact le_of_eq (finiteSupportLegendreRate_at_mean D
      hvlo (lt_trans hvμ D.hmuhi)).symm
  calc
    finiteSupportMeanEnvelopeRateLeft D Q v =
        ∫ s : ℝ in t..(0 : ℝ), A s := hchange
    _ < ∫ s : ℝ in t..(0 : ℝ), B s := hineq
    _ = t * v - D.logMGF t := hfund
    _ ≤ finiteSupportLegendreRate D v := hrate

end
end ExactHoeffding
