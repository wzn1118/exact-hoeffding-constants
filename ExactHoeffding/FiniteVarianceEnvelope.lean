import ExactHoeffding.AuxiliaryCurvature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite-law variance-envelope integration

This file records the part of the variance-envelope argument that is
independent of a Legendre-transform inverse.  For a normalized finite law,
the centered log-MGF is bounded by the interval integral of any continuous
upper envelope for the tilted variance, evaluated along the tilted-mean
curve.  A strict pointwise gap at an interior point gives a strict integral
gap.
-/

namespace ExactHoeffding

noncomputable section

/-- The mean of a normalized finite law after exponential tilting. -/
def finiteEnvelopeTiltMean {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  finiteTiltFirst s w x t / finiteMGF s w x t

/-- The second derivative of the finite log-MGF, used as tilted variance. -/
def finiteEnvelopeTiltVariance {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv (fun u => Real.log (finiteMGF s w x u))) t

private theorem finiteEnvelopeTiltMean_hasDerivAt
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (finiteEnvelopeTiltMean s w x)
      (finiteEnvelopeTiltVariance s w x t) t := by
  unfold finiteEnvelopeTiltMean finiteEnvelopeTiltVariance
  rw [finiteLogMGF_second_deriv s w x hw hs t]
  exact finiteTiltedMean_hasDerivAt s w x hw hs t

private theorem finiteEnvelopeTiltMean_continuous
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    Continuous (finiteEnvelopeTiltMean s w x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (finiteEnvelopeTiltMean_hasDerivAt s w x hw hs t).continuousAt

private theorem finiteEnvelopeTiltVariance_continuous
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    Continuous (finiteEnvelopeTiltVariance s w x) := by
  have hψ : ContDiff ℝ 3 (fun u => Real.log (finiteMGF s w x u)) :=
    finiteLogMGF_contDiff s w x hw hs 3
  have hψ1 : ContDiff ℝ 2 (deriv (fun u => Real.log (finiteMGF s w x u))) :=
    hψ.deriv'
  have hψ2 : ContDiff ℝ 1
      (deriv (deriv (fun u => Real.log (finiteMGF s w x u)))) :=
    hψ1.deriv'
  exact hψ2.continuous

/-- The finite-law variance-envelope integral comparison in its exact
centered-curvature form.  The envelope is imposed on the actual tilted mean
curve; no rate comparison is assumed. -/
theorem finiteLogMGF_variance_envelope_integral_div
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * x i = 0)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hV : ∀ u : ℝ,
      finiteEnvelopeTiltVariance s w x u ≤
        Q (finiteEnvelopeTiltMean s w x u))
    (t : ℝ) (ht : t ≠ 0) :
    2 * Real.log (finiteMGF s w x t) / t ^ 2 ≤
      2 * ∫ u : ℝ in (0 : ℝ)..1,
        (1 - u) * Q (finiteEnvelopeTiltMean s w x (u * t)) := by
  let μt := finiteEnvelopeTiltMean s w x
  let Vt := finiteEnvelopeTiltVariance s w x
  let φ : ℝ → ℝ := fun u => (1 - u) * Vt (u * t)
  let Φ : ℝ → ℝ := fun u => (1 - u) * Q (μt (u * t))
  have hcomp : Continuous (fun u : ℝ => u * t) :=
    continuous_id.mul continuous_const
  have hμc : Continuous μt :=
    finiteEnvelopeTiltMean_continuous s w x hw hs
  have hVc : Continuous Vt :=
    finiteEnvelopeTiltVariance_continuous s w x hw hs
  have hφc : Continuous φ := by
    dsimp [φ]
    exact (continuous_const.sub continuous_id).mul (hVc.comp hcomp)
  have hΦc : Continuous Φ := by
    dsimp [Φ]
    exact (continuous_const.sub continuous_id).mul (hQ.comp (hμc.comp hcomp))
  have hle : ∀ u ∈ Set.Icc (0 : ℝ) 1, φ u ≤ Φ u := by
    intro u hu
    dsimp [φ, Φ, Vt, μt]
    exact mul_le_mul_of_nonneg_left (hV (u * t)) (by linarith [hu.2])
  have hI : (∫ u : ℝ in (0 : ℝ)..1, φ u) ≤
      ∫ u : ℝ in (0 : ℝ)..1, Φ u := by
    apply intervalIntegral.integral_mono_on
      (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
      (by norm_num) (hφc.intervalIntegrable 0 1) (hΦc.intervalIntegrable 0 1)
    exact hle
  have hcurv := finiteLogMGF_integrated_curvature s w x hw hs hmean t ht
  dsimp [φ, Φ, Vt, μt] at hI ⊢
  calc
    2 * Real.log (finiteMGF s w x t) / t ^ 2 =
        2 * ∫ u : ℝ in (0 : ℝ)..1,
          (1 - u) * deriv (deriv (fun v => Real.log (finiteMGF s w x v))) (u * t) := hcurv
    _ ≤ 2 * ∫ u : ℝ in (0 : ℝ)..1,
        (1 - u) * Q (finiteTiltFirst s w x (u * t) /
          finiteMGF s w x (u * t)) := by
      have hI' :
          (∫ u : ℝ in (0 : ℝ)..1,
            (1 - u) * deriv (deriv (fun v => Real.log (finiteMGF s w x v))) (u * t)) ≤
          ∫ u : ℝ in (0 : ℝ)..1,
            (1 - u) * Q (finiteTiltFirst s w x (u * t) /
              finiteMGF s w x (u * t)) := by
        simpa [finiteEnvelopeTiltVariance, finiteEnvelopeTiltMean] using hI
      exact mul_le_mul_of_nonneg_left hI' (by norm_num)

/-- The same comparison without division by the nonzero tilt. -/
theorem finiteLogMGF_variance_envelope_integral
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * x i = 0)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hV : ∀ u : ℝ,
      finiteEnvelopeTiltVariance s w x u ≤
        Q (finiteEnvelopeTiltMean s w x u)) (t : ℝ) :
    Real.log (finiteMGF s w x t) ≤
      t ^ 2 * ∫ u : ℝ in (0 : ℝ)..1,
        (1 - u) * Q (finiteEnvelopeTiltMean s w x (u * t)) := by
  by_cases ht : t = 0
  · subst t
    simp [finiteMGF_zero_of_normalized s w x hs]
  · have h := finiteLogMGF_variance_envelope_integral_div
      s w x hw hs hmean Q hQ hV t ht
    have hsq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have h' := (div_le_iff₀ hsq).mp h
    nlinarith [h']

/-- Strictness of the finite-law variance-envelope integral.  It is enough
that the variance gap is strict at one interior point of the tilt segment;
continuity then gives a positive-length strict interval. -/
theorem finiteLogMGF_variance_envelope_integral_strict
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * x i = 0)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hV : ∀ u : ℝ,
      finiteEnvelopeTiltVariance s w x u ≤
        Q (finiteEnvelopeTiltMean s w x u))
    (t : ℝ) (ht : t ≠ 0)
    (hstrict : ∃ c ∈ Set.Ioo (0 : ℝ) 1,
      finiteEnvelopeTiltVariance s w x (c * t) <
        Q (finiteEnvelopeTiltMean s w x (c * t))) :
    Real.log (finiteMGF s w x t) <
      t ^ 2 * ∫ u : ℝ in (0 : ℝ)..1,
        (1 - u) * Q (finiteEnvelopeTiltMean s w x (u * t)) := by
  let μt := finiteEnvelopeTiltMean s w x
  let Vt := finiteEnvelopeTiltVariance s w x
  let φ : ℝ → ℝ := fun u => (1 - u) * Vt (u * t)
  let Φ : ℝ → ℝ := fun u => (1 - u) * Q (μt (u * t))
  have hcomp : Continuous (fun u : ℝ => u * t) :=
    continuous_id.mul continuous_const
  have hμc : Continuous μt :=
    finiteEnvelopeTiltMean_continuous s w x hw hs
  have hVc : Continuous Vt :=
    finiteEnvelopeTiltVariance_continuous s w x hw hs
  have hφc : Continuous φ := by
    dsimp [φ]
    exact (continuous_const.sub continuous_id).mul (hVc.comp hcomp)
  have hΦc : Continuous Φ := by
    dsimp [Φ]
    exact (continuous_const.sub continuous_id).mul (hQ.comp (hμc.comp hcomp))
  have hle : ∀ u ∈ Set.Ioc (0 : ℝ) 1, φ u ≤ Φ u := by
    intro u hu
    dsimp [φ, Φ, Vt, μt]
    exact mul_le_mul_of_nonneg_left (hV (u * t)) (by linarith [hu.2])
  obtain ⟨c, hc, hgap⟩ := hstrict
  have hgap' : φ c < Φ c := by
    dsimp [φ, Φ]
    exact mul_lt_mul_of_pos_left hgap (by linarith [hc.2])
  have hI : (∫ u : ℝ in (0 : ℝ)..1, φ u) <
      ∫ u : ℝ in (0 : ℝ)..1, Φ u := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (a := (0 : ℝ)) (b := 1) (by norm_num)
      hφc.continuousOn hΦc.continuousOn hle
    exact ⟨c, ⟨hc.1.le, hc.2.le⟩, hgap'⟩
  have hcurv := finiteLogMGF_integrated_curvature s w x hw hs hmean t ht
  have hsq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  dsimp [φ, Φ, Vt, μt] at hI ⊢
  calc
    Real.log (finiteMGF s w x t) =
        t ^ 2 * ∫ u : ℝ in (0 : ℝ)..1,
          (1 - u) * deriv (deriv (fun v => Real.log (finiteMGF s w x v))) (u * t) := by
            have hEq := hcurv
            have hmul := congrArg (fun z : ℝ => z * (t ^ 2 / 2)) hEq
            field_simp at hmul ⊢
            nlinarith [hmul]
    _ < t ^ 2 * ∫ u : ℝ in (0 : ℝ)..1,
        (1 - u) * Q (finiteTiltFirst s w x (u * t) /
          finiteMGF s w x (u * t)) := by
      have hI' :
          (∫ u : ℝ in (0 : ℝ)..1,
            (1 - u) * deriv (deriv (fun v => Real.log (finiteMGF s w x v))) (u * t)) <
          ∫ u : ℝ in (0 : ℝ)..1,
            (1 - u) * Q (finiteTiltFirst s w x (u * t) /
              finiteMGF s w x (u * t)) := by
        simpa [finiteEnvelopeTiltVariance, finiteEnvelopeTiltMean] using hI
      exact mul_lt_mul_of_pos_left hI' hsq

end
end ExactHoeffding
