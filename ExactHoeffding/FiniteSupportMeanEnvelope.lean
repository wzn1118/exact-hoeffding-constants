import ExactHoeffding.FiniteMeanLegendre
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith

/-!
# General finite-support mean-coordinate envelope theorem

This file isolates the analytic argument in the variance-envelope theorem from
any integer support parametrization.  A finite exponential family supplies a
strictly increasing tilted-mean curve, its positive tilted variance, endpoint
limits, and the logarithmic-MGF derivative.  The comparison is then proved
from the change of variables along that curve; no rate comparison is assumed.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- Analytic data carried by a nondegenerate finite-support exponential family. -/
structure FiniteSupportTiltCurve where
  lo : ℝ
  hi : ℝ
  mu : ℝ
  mean : ℝ → ℝ
  variance : ℝ → ℝ
  logMGF : ℝ → ℝ
  hlomu : lo < mu
  hmuhi : mu < hi
  mean_zero : mean 0 = mu
  mean_range : ∀ t : ℝ, lo < mean t ∧ mean t < hi
  mean_deriv : ∀ t : ℝ, HasDerivAt mean (variance t) t
  variance_pos : ∀ t : ℝ, 0 < variance t
  variance_continuous : Continuous variance
  mean_atBot : Tendsto mean atBot (𝓝 lo)
  mean_atTop : Tendsto mean atTop (𝓝 hi)
  logMGF_zero : logMGF 0 = 0
  logMGF_deriv : ∀ t : ℝ, HasDerivAt logMGF (mean t) t

/-- The Legendre rate attached to the logarithmic-MGF in a tilt curve. -/
noncomputable def finiteSupportLegendreRate
    (D : FiniteSupportTiltCurve) (v : ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ => t * v - D.logMGF t))

/-- The right mean-coordinate variance-envelope rate. -/
noncomputable def finiteSupportMeanEnvelopeRateRight
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ u : ℝ in D.mu..v, (v - u) / Q u

/-- The left mean-coordinate variance-envelope rate. -/
noncomputable def finiteSupportMeanEnvelopeRateLeft
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ u : ℝ in v..D.mu, (u - v) / Q u

private theorem finiteSupport_mean_strictMono
    (D : FiniteSupportTiltCurve) : StrictMono D.mean := by
  exact strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos

private theorem finiteSupport_mean_continuous
    (D : FiniteSupportTiltCurve) : Continuous D.mean := by
  exact continuous_iff_continuousAt.mpr (fun t =>
    (D.mean_deriv t).continuousAt)

private theorem finiteSupport_logMGF_continuous
    (D : FiniteSupportTiltCurve) : Continuous D.logMGF := by
  exact continuous_iff_continuousAt.mpr (fun t =>
    (D.logMGF_deriv t).continuousAt)

private theorem finiteSupport_candidate_hasDerivAt
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

private theorem finiteSupport_mean_inverse_exists
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    ∃! t : ℝ, D.mean t = v := by
  have hcont : Continuous D.mean := finiteSupport_mean_continuous D
  have hbot := (tendsto_order.1 D.mean_atBot).2 v hvlo
  have htop := (tendsto_order.1 D.mean_atTop).1 v hvhi
  obtain ⟨a, ha⟩ := eventually_atBot.mp hbot
  obtain ⟨b, hb⟩ := eventually_atTop.mp htop
  let left : ℝ := a
  let right : ℝ := max b (a + 1)
  have hleft : D.mean left < v := ha left le_rfl
  have hright : v < D.mean right := by
    have hbr : b ≤ right := le_max_left _ _
    exact hb right hbr
  have hlr : left ≤ right := by
    dsimp [left, right]
    exact le_trans (by linarith) (le_max_right _ _)
  have him := intermediate_value_Icc hlr hcont.continuousOn
    ⟨le_of_lt hleft, le_of_lt hright⟩
  obtain ⟨t, ht, htv⟩ := him
  refine ⟨t, htv, ?_⟩
  intro s hs
  exact (finiteSupport_mean_strictMono D).injective (hs.trans htv.symm)

/-- The unique tilt attaining an interior mean. -/
noncomputable def finiteSupportMeanInverse
    (D : FiniteSupportTiltCurve) (v : ℝ) : ℝ :=
  if hv : v ∈ Ioo D.lo D.hi then
    Classical.choose (finiteSupport_mean_inverse_exists D hv.1 hv.2)
  else 0

@[simp] theorem finiteSupportMeanInverse_spec
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    D.mean (finiteSupportMeanInverse D v) = v := by
  dsimp [finiteSupportMeanInverse]
  rw [dif_pos ⟨hvlo, hvhi⟩]
  exact (Classical.choose_spec
    (finiteSupport_mean_inverse_exists D hvlo hvhi)).1

theorem finiteSupportMeanInverse_unique
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) {t : ℝ} :
    D.mean t = v ↔ t = finiteSupportMeanInverse D v := by
  constructor
  · intro ht
    exact (finiteSupport_mean_strictMono D).injective (ht.trans
      (finiteSupportMeanInverse_spec D hvlo hvhi).symm)
  · intro ht
    rw [ht, finiteSupportMeanInverse_spec D hvlo hvhi]

private theorem finiteSupport_candidate_max_at_mean
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    ∀ s : ℝ,
      s * v - D.logMGF s ≤
        finiteSupportMeanInverse D v * v -
          D.logMGF (finiteSupportMeanInverse D v) := by
  let t₀ : ℝ := finiteSupportMeanInverse D v
  have htmean : D.mean t₀ = v := finiteSupportMeanInverse_spec D hvlo hvhi
  have hFc : Continuous (fun s : ℝ => s * v - D.logMGF s) := by
    exact (continuous_id.mul continuous_const).sub
      (finiteSupport_logMGF_continuous D)
  have hleft : MonotoneOn
      (fun s : ℝ => s * v - D.logMGF s) (Iic t₀) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic t₀)
      hFc.continuousOn
      (fun s hs => (finiteSupport_candidate_hasDerivAt D v s).hasDerivWithinAt)
    intro s hs
    rw [interior_Iic] at hs
    have hmean : D.mean s ≤ v := by
      exact ((finiteSupport_mean_strictMono D hs).le).trans_eq htmean
    linarith
  have hright : AntitoneOn
      (fun s : ℝ => s * v - D.logMGF s) (Ici t₀) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici t₀)
      hFc.continuousOn
      (fun s hs => (finiteSupport_candidate_hasDerivAt D v s).hasDerivWithinAt)
    intro s hs
    rw [interior_Ici] at hs
    have hmean : v ≤ D.mean s := by
      exact htmean ▸ (finiteSupport_mean_strictMono D hs).le
    linarith
  intro s
  by_cases hs : s ≤ t₀
  · exact hleft (mem_Iic.mpr hs) (mem_Iic.mpr le_rfl) hs
  · have hst : t₀ ≤ s := le_of_not_ge hs
    exact hright (mem_Ici.mpr le_rfl) (mem_Ici.mpr hst) hst

private theorem finiteSupport_rate_bddAbove
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    BddAbove (Set.range (fun t : ℝ => t * v - D.logMGF t)) := by
  refine ⟨finiteSupportMeanInverse D v * v -
      D.logMGF (finiteSupportMeanInverse D v), ?_⟩
  rintro z ⟨t, rfl⟩
  exact finiteSupport_candidate_max_at_mean D hvlo hvhi t

/-- At every interior mean the Legendre supremum is attained at the inverse
    tilted mean. -/
theorem finiteSupportLegendreRate_at_mean
    (D : FiniteSupportTiltCurve) {v : ℝ}
    (hvlo : D.lo < v) (hvhi : v < D.hi) :
    finiteSupportLegendreRate D v =
      finiteSupportMeanInverse D v * v -
        D.logMGF (finiteSupportMeanInverse D v) := by
  have hB := finiteSupport_rate_bddAbove D hvlo hvhi
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ⟨0, ?_⟩⟩
      simp [finiteSupportLegendreRate, D.logMGF_zero]
    · rintro z ⟨s, rfl⟩
      exact finiteSupport_candidate_max_at_mean D hvlo hvhi s
  · exact le_csSup hB ⟨finiteSupportMeanInverse D v, rfl⟩

/-- The right-side mean-coordinate comparison. -/
theorem finiteSupportLegendreRate_ge_meanEnvelopeRateRight
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Set.Icc D.lo D.hi, 0 < Q u)
    (hV : ∀ t : ℝ, D.variance t ≤ Q (D.mean t))
    {v : ℝ} (hvmu : D.mu ≤ v) (hvhi : v < D.hi) :
    finiteSupportMeanEnvelopeRateRight D Q v ≤
      finiteSupportLegendreRate D v := by
  by_cases hv : v = D.mu
  · subst v
    have hinv : finiteSupportMeanInverse D D.mu = 0 := by
      exact ((finiteSupportMeanInverse_unique D D.hlomu D.hmuhi (t := 0)).1
        (by simpa [D.mean_zero])).symm
    rw [finiteSupportMeanEnvelopeRateRight, intervalIntegral.integral_same]
    rw [finiteSupportLegendreRate_at_mean D D.hlomu D.hmuhi]
    rw [hinv, D.logMGF_zero]
    simp
  · have hvmu' : D.mu < v := lt_of_le_of_ne hvmu (Ne.symm hv)
    let t : ℝ := finiteSupportMeanInverse D v
    have htmean : D.mean t = v := finiteSupportMeanInverse_spec D
      (lt_trans D.hlomu hvmu') hvhi
    have ht0 : 0 < t := by
      by_contra hnt
      have hle : t ≤ 0 := le_of_not_gt hnt
      have hmean : D.mean t ≤ D.mean 0 :=
        (finiteSupport_mean_strictMono D).monotone hle
      linarith [htmean, D.mean_zero, hvmu']
    have hmean_cont : Continuous D.mean := finiteSupport_mean_continuous D
    let A : ℝ → ℝ := fun s =>
      ((v - D.mean s) / Q (D.mean s)) * D.variance s
    let B : ℝ → ℝ := fun s => v - D.mean s
    have hAB : ∀ s ∈ Icc (0 : ℝ) t, A s ≤ B s := by
      intro s hs
      have hms : D.mean s ∈ Icc D.lo D.hi :=
        ⟨(D.mean_range s).1.le, (D.mean_range s).2.le⟩
      have hq : 0 < Q (D.mean s) := hQpos _ hms
      have hdiff : 0 ≤ v - D.mean s := by
        have hmono := finiteSupport_mean_strictMono D
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
    have hAcont : ContinuousOn A (Icc (0 : ℝ) t) := by
      have hmc : ContinuousOn (fun s : ℝ => Q (D.mean s)) (Icc (0 : ℝ) t) :=
        hQ.continuousOn.comp hmean_cont.continuousOn (fun _ _ => mem_univ _)
      have hqne : ∀ s ∈ Icc (0 : ℝ) t, Q (D.mean s) ≠ 0 := by
        intro s hs
        exact ne_of_gt (hQpos _ ⟨(D.mean_range s).1.le,
          (D.mean_range s).2.le⟩)
      dsimp [A]
      exact ((continuousOn_const.sub hmean_cont.continuousOn).div hmc hqne).mul
        D.variance_continuous.continuousOn
    have hBcont : ContinuousOn B (Icc (0 : ℝ) t) := by
      dsimp [B]
      exact continuousOn_const.sub hmean_cont.continuousOn
    have hAcont' : ContinuousOn A (uIcc (0 : ℝ) t) := by
      simpa [uIcc_of_le (le_of_lt ht0)] using hAcont
    have hBcont' : ContinuousOn B (uIcc (0 : ℝ) t) := by
      simpa [uIcc_of_le (le_of_lt ht0)] using hBcont
    have hAi : IntervalIntegrable A MeasureTheory.volume 0 t :=
      hAcont'.intervalIntegrable
    have hBi : IntervalIntegrable B MeasureTheory.volume 0 t :=
      hBcont'.intervalIntegrable
    have hineq :
        (∫ s : ℝ in (0 : ℝ)..t, A s) ≤
          ∫ s : ℝ in (0 : ℝ)..t, B s := by
      apply intervalIntegral.integral_mono_on (le_of_lt ht0) hAi hBi
      exact hAB
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
    have hfund0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => finiteSupport_candidate_hasDerivAt D v s) hBi
    have hfund :
        (∫ s : ℝ in (0 : ℝ)..t, B s) = t * v - D.logMGF t := by
      dsimp [B] at hfund0 ⊢
      rw [hfund0, D.logMGF_zero]
      ring
    have hrate : t * v - D.logMGF t ≤ finiteSupportLegendreRate D v := by
      exact le_csSup (finiteSupport_rate_bddAbove D
        (lt_trans D.hlomu hvmu') hvhi) ⟨t, rfl⟩
    calc
      finiteSupportMeanEnvelopeRateRight D Q v =
          ∫ s : ℝ in (0 : ℝ)..t, A s := hchange
      _ ≤ ∫ s : ℝ in (0 : ℝ)..t, B s := hineq
      _ = t * v - D.logMGF t := hfund
      _ ≤ finiteSupportLegendreRate D v := hrate

/-- The left-side mean-coordinate comparison. -/
theorem finiteSupportLegendreRate_ge_meanEnvelopeRateLeft
    (D : FiniteSupportTiltCurve) (Q : ℝ → ℝ)
    (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Set.Icc D.lo D.hi, 0 < Q u)
    (hV : ∀ t : ℝ, D.variance t ≤ Q (D.mean t))
    {v : ℝ} (hvlo : D.lo < v) (hvmu : v ≤ D.mu) :
    finiteSupportMeanEnvelopeRateLeft D Q v ≤
      finiteSupportLegendreRate D v := by
  by_cases hv : v = D.mu
  · subst v
    have hinv : finiteSupportMeanInverse D D.mu = 0 := by
      exact ((finiteSupportMeanInverse_unique D D.hlomu D.hmuhi (t := 0)).1
        (by simpa [D.mean_zero])).symm
    rw [finiteSupportMeanEnvelopeRateLeft, intervalIntegral.integral_same]
    rw [finiteSupportLegendreRate_at_mean D D.hlomu D.hmuhi]
    rw [hinv, D.logMGF_zero]
    simp
  · have hvmu' : v < D.mu := lt_of_le_of_ne hvmu hv
    let t : ℝ := finiteSupportMeanInverse D v
    have htmean : D.mean t = v := finiteSupportMeanInverse_spec D
      hvlo (lt_trans hvmu' D.hmuhi)
    have ht0 : t < 0 := by
      by_contra hnt
      have hle : 0 ≤ t := le_of_not_gt hnt
      have hmean : D.mean 0 ≤ D.mean t :=
        (finiteSupport_mean_strictMono D).monotone hle
      linarith [htmean, D.mean_zero, hvmu']
    have hmean_cont : Continuous D.mean := finiteSupport_mean_continuous D
    let A : ℝ → ℝ := fun s =>
      ((D.mean s - v) / Q (D.mean s)) * D.variance s
    let B : ℝ → ℝ := fun s => D.mean s - v
    have hAB : ∀ s ∈ Icc t (0 : ℝ), A s ≤ B s := by
      intro s hs
      have hms : D.mean s ∈ Icc D.lo D.hi :=
        ⟨(D.mean_range s).1.le, (D.mean_range s).2.le⟩
      have hq : 0 < Q (D.mean s) := hQpos _ hms
      have hdiff : 0 ≤ D.mean s - v := by
        have hmono := finiteSupport_mean_strictMono D
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
    have hAcont : ContinuousOn A (Icc t (0 : ℝ)) := by
      have hmc : ContinuousOn (fun s : ℝ => Q (D.mean s)) (Icc t (0 : ℝ)) :=
        hQ.continuousOn.comp hmean_cont.continuousOn (fun _ _ => mem_univ _)
      have hqne : ∀ s ∈ Icc t (0 : ℝ), Q (D.mean s) ≠ 0 := by
        intro s hs
        exact ne_of_gt (hQpos _ ⟨(D.mean_range s).1.le,
          (D.mean_range s).2.le⟩)
      dsimp [A]
      exact ((hmean_cont.continuousOn.sub continuousOn_const).div hmc hqne).mul
        D.variance_continuous.continuousOn
    have hBcont : ContinuousOn B (Icc t (0 : ℝ)) := by
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
    have hineq :
        (∫ s : ℝ in t..(0 : ℝ), A s) ≤
          ∫ s : ℝ in t..(0 : ℝ), B s := by
      apply intervalIntegral.integral_mono_on ht0.le hAi hBi
      exact hAB
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
    have hnegB : (fun s : ℝ => v - D.mean s) = -B := by
      funext s
      dsimp [B]
      ring
    have hUi : IntervalIntegrable (fun s : ℝ => v - D.mean s)
        MeasureTheory.volume t 0 := by
      rw [hnegB]
      exact hBi.neg
    have hfund0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => finiteSupport_candidate_hasDerivAt D v s) hUi
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
      exact le_csSup (finiteSupport_rate_bddAbove D
        hvlo (lt_trans hvmu' D.hmuhi)) ⟨t, rfl⟩
    calc
      finiteSupportMeanEnvelopeRateLeft D Q v =
          ∫ s : ℝ in t..(0 : ℝ), A s := hchange
      _ ≤ ∫ s : ℝ in t..(0 : ℝ), B s := hineq
      _ = t * v - D.logMGF t := hfund
      _ ≤ finiteSupportLegendreRate D v := hrate

end
end ExactHoeffding
