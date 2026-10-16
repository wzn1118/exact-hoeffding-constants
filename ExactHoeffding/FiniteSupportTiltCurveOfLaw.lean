import ExactHoeffding.FiniteSupportMeanEnvelope
import ExactHoeffding.TiltedEndpoints
import Mathlib.Tactic.Linarith

/-!
# Finite-support realization of the mean-curve interface

A finite weighted law with distinguished positive minimum and maximum atoms
realizes the abstract tilted-mean curve.  The only analytic input retained as
an explicit hypothesis is strict positivity of the tilted variance; this is
the nondegeneracy condition used by the envelope argument.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

structure FiniteSupportLawData (ι : Type*) [DecidableEq ι] where
  support : Finset ι
  weight : ι → ℝ
  value : ι → ℝ
  weight_nonneg : ∀ i ∈ support, 0 ≤ weight i
  weight_total : ∑ i ∈ support, weight i = 1
  loIndex : ι
  hiIndex : ι
  lo_hi_ne : loIndex ≠ hiIndex
  lo_mem : loIndex ∈ support
  hi_mem : hiIndex ∈ support
  lo_weight_pos : 0 < weight loIndex
  hi_weight_pos : 0 < weight hiIndex
  lo_strict : ∀ i ∈ support, i ≠ loIndex → value loIndex < value i
  hi_strict : ∀ i ∈ support, i ≠ hiIndex → value i < value hiIndex

noncomputable def FiniteSupportLawData.mean0
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) : ℝ :=
  ∑ i ∈ L.support, L.weight i * L.value i

noncomputable def FiniteSupportLawData.centeredValue
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (i : ι) : ℝ :=
  L.value i - L.mean0

noncomputable def FiniteSupportLawData.mean
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) : ℝ :=
  finiteEnvelopeTiltMean L.support L.weight L.centeredValue t

noncomputable def FiniteSupportLawData.variance
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) : ℝ :=
  finiteEnvelopeTiltVariance L.support L.weight L.centeredValue t

noncomputable def FiniteSupportLawData.logMGF
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) : ℝ :=
  Real.log (finiteMGF L.support L.weight L.centeredValue t)

private theorem law_mgf_pos
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) :
    0 < finiteMGF L.support L.weight L.centeredValue t := by
  exact finiteMGF_pos_of_normalized L.support L.weight L.centeredValue
    L.weight_nonneg L.weight_total t

private theorem law_mean_deriv
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) :
    HasDerivAt L.mean (L.variance t) t := by
  unfold FiniteSupportLawData.mean FiniteSupportLawData.variance
    finiteEnvelopeTiltMean finiteEnvelopeTiltVariance
  rw [finiteLogMGF_second_deriv L.support L.weight L.centeredValue
    L.weight_nonneg L.weight_total t]
  exact finiteTiltedMean_hasDerivAt L.support L.weight L.centeredValue
    L.weight_nonneg L.weight_total t

private theorem law_variance_continuous
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    Continuous L.variance := by
  unfold FiniteSupportLawData.variance finiteEnvelopeTiltVariance
  have hψ : ContDiff ℝ 3
      (fun u => Real.log (finiteMGF L.support L.weight L.centeredValue u)) :=
    finiteLogMGF_contDiff L.support L.weight L.centeredValue
      L.weight_nonneg L.weight_total 3
  have hψ1 : ContDiff ℝ 2
      (deriv (fun u => Real.log (finiteMGF L.support L.weight L.centeredValue u))) :=
    hψ.deriv'
  have hψ2 : ContDiff ℝ 1
      (deriv (deriv (fun u => Real.log (finiteMGF L.support L.weight L.centeredValue u)))) :=
    hψ1.deriv'
  exact hψ2.continuous

private theorem law_mean_zero
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    L.mean 0 = 0 := by
  unfold FiniteSupportLawData.mean finiteEnvelopeTiltMean
  rw [finiteMGF_zero_of_normalized L.support L.weight L.centeredValue
    L.weight_total]
  simp only [finiteTiltFirst, FiniteSupportLawData.centeredValue,
    FiniteSupportLawData.mean0, zero_mul, Real.exp_zero, mul_one, div_one]
  calc
    (∑ i ∈ L.support, L.weight i *
        (L.value i - L.mean0)) =
        (∑ i ∈ L.support, L.weight i * L.value i) -
          (∑ i ∈ L.support, L.weight i * L.mean0) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ = L.mean0 - (∑ i ∈ L.support, L.weight i) * L.mean0 := by
          rw [← Finset.sum_mul]
          rfl
    _ = 0 := by
          rw [L.weight_total]
          dsimp [FiniteSupportLawData.mean0]
          ring

private theorem law_left_right_distinct
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    L.loIndex ≠ L.hiIndex := L.lo_hi_ne

private theorem law_mean_range
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) :
    L.value L.loIndex - L.mean0 < L.mean t ∧
      L.mean t < L.value L.hiIndex - L.mean0 := by
  have hM : 0 < finiteMGF L.support L.weight L.centeredValue t :=
    law_mgf_pos L t
  have hleft_nonneg : ∀ i ∈ L.support,
      0 ≤ L.weight i *
        ((L.centeredValue i - L.centeredValue L.loIndex) *
          Real.exp (t * L.centeredValue i)) := by
    intro i hi
    have hxi : 0 ≤ L.centeredValue i - L.centeredValue L.loIndex := by
      dsimp [FiniteSupportLawData.centeredValue]
      by_cases hli : i = L.loIndex
      · subst i
        simp
      · linarith [L.lo_strict i hi hli]
    exact mul_nonneg (L.weight_nonneg i hi)
      (mul_nonneg hxi (Real.exp_pos _).le)
  have hleft_pos : 0 < ∑ i ∈ L.support,
      L.weight i *
        ((L.centeredValue i - L.centeredValue L.loIndex) *
          Real.exp (t * L.centeredValue i)) := by
    apply Finset.sum_pos'
    · exact hleft_nonneg
    · refine ⟨L.hiIndex, L.hi_mem, ?_⟩
      have hne : L.hiIndex ≠ L.loIndex := Ne.symm (law_left_right_distinct L)
      have hgap : 0 < L.centeredValue L.hiIndex - L.centeredValue L.loIndex := by
        dsimp [FiniteSupportLawData.centeredValue]
        exact sub_pos.mpr (lt_of_not_ge (fun h => by
          have h₁ := L.lo_strict L.hiIndex L.hi_mem hne
          linarith))
      exact mul_pos L.hi_weight_pos
        (mul_pos hgap (Real.exp_pos _))
  have hleft_sum :
      (∑ i ∈ L.support, L.weight i *
          (L.centeredValue i * Real.exp (t * L.centeredValue i))) -
        L.centeredValue L.loIndex * finiteMGF L.support L.weight
          L.centeredValue t =
      ∑ i ∈ L.support, L.weight i *
        ((L.centeredValue i - L.centeredValue L.loIndex) *
          Real.exp (t * L.centeredValue i)) := by
    simp only [finiteMGF, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hleft_num :
      L.centeredValue L.loIndex * finiteMGF L.support L.weight
          L.centeredValue t <
        finiteTiltFirst L.support L.weight L.centeredValue t := by
    have hleft_pos' := hleft_pos
    rw [← hleft_sum] at hleft_pos'
    dsimp [finiteTiltFirst]
    linarith
  have hright_nonneg : ∀ i ∈ L.support,
      0 ≤ L.weight i *
        ((L.centeredValue L.hiIndex - L.centeredValue i) *
          Real.exp (t * L.centeredValue i)) := by
    intro i hi
    have hxi : 0 ≤ L.centeredValue L.hiIndex - L.centeredValue i := by
      dsimp [FiniteSupportLawData.centeredValue]
      by_cases hri : i = L.hiIndex
      · subst i
        simp
      · linarith [L.hi_strict i hi hri]
    exact mul_nonneg (L.weight_nonneg i hi)
      (mul_nonneg hxi (Real.exp_pos _).le)
  have hright_pos : 0 < ∑ i ∈ L.support,
      L.weight i *
        ((L.centeredValue L.hiIndex - L.centeredValue i) *
          Real.exp (t * L.centeredValue i)) := by
    apply Finset.sum_pos'
    · exact hright_nonneg
    · refine ⟨L.loIndex, L.lo_mem, ?_⟩
      have hne : L.loIndex ≠ L.hiIndex := law_left_right_distinct L
      have hgap : 0 < L.centeredValue L.hiIndex - L.centeredValue L.loIndex := by
        dsimp [FiniteSupportLawData.centeredValue]
        exact sub_pos.mpr (lt_of_not_ge (fun h => by
          have h₁ := L.lo_strict L.hiIndex L.hi_mem
            (Ne.symm (law_left_right_distinct L))
          linarith))
      exact mul_pos L.lo_weight_pos
        (mul_pos hgap (Real.exp_pos _))
  have hright_sum :
      L.centeredValue L.hiIndex * finiteMGF L.support L.weight
          L.centeredValue t -
        (∑ i ∈ L.support, L.weight i *
          (L.centeredValue i * Real.exp (t * L.centeredValue i))) =
      ∑ i ∈ L.support, L.weight i *
        ((L.centeredValue L.hiIndex - L.centeredValue i) *
          Real.exp (t * L.centeredValue i)) := by
    simp only [finiteMGF, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright_num :
      finiteTiltFirst L.support L.weight L.centeredValue t <
        L.centeredValue L.hiIndex * finiteMGF L.support L.weight
          L.centeredValue t := by
    have hright_pos' := hright_pos
    rw [← hright_sum] at hright_pos'
    dsimp [finiteTiltFirst]
    linarith
  constructor
  · unfold FiniteSupportLawData.mean finiteEnvelopeTiltMean
    have h := (lt_div_iff₀ hM).2 hleft_num
    dsimp [FiniteSupportLawData.centeredValue] at h ⊢
    exact h
  · unfold FiniteSupportLawData.mean finiteEnvelopeTiltMean
    have h := (div_lt_iff₀ hM).2 hright_num
    dsimp [FiniteSupportLawData.centeredValue] at h ⊢
    exact h

private theorem law_mean_atBot
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    Tendsto L.mean atBot
      (𝓝 (L.value L.loIndex - L.mean0)) := by
  have h := finite_tilted_expectation_tendsto_atBot
    L.support L.weight L.centeredValue L.centeredValue L.loIndex L.lo_mem
    (ne_of_gt L.lo_weight_pos)
    (fun i hi hne => by
      dsimp [FiniteSupportLawData.centeredValue]
      linarith [L.lo_strict i hi hne])
  change Tendsto (fun t : ℝ =>
      finiteTiltFirst L.support L.weight L.centeredValue t /
        finiteMGF L.support L.weight L.centeredValue t) atBot
      (𝓝 (L.value L.loIndex - L.mean0))
  simpa [FiniteSupportLawData.mean, finiteEnvelopeTiltMean,
    finiteTiltFirst, finiteMGF, FiniteSupportLawData.centeredValue, mul_assoc] using h

private theorem law_mean_atTop
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    Tendsto L.mean atTop
      (𝓝 (L.value L.hiIndex - L.mean0)) := by
  have h := finite_tilted_expectation_tendsto_atTop
    L.support L.weight L.centeredValue L.centeredValue L.hiIndex L.hi_mem
    (ne_of_gt L.hi_weight_pos)
    (fun i hi hne => by
      dsimp [FiniteSupportLawData.centeredValue]
      linarith [L.hi_strict i hi hne])
  change Tendsto (fun t : ℝ =>
      finiteTiltFirst L.support L.weight L.centeredValue t /
        finiteMGF L.support L.weight L.centeredValue t) atTop
      (𝓝 (L.value L.hiIndex - L.mean0))
  simpa [FiniteSupportLawData.mean, finiteEnvelopeTiltMean,
    finiteTiltFirst, finiteMGF, FiniteSupportLawData.centeredValue, mul_assoc] using h

/-- The centered finite law realizes the abstract mean-curve interface when
its tilted variance is strictly positive. -/
noncomputable def FiniteSupportLawData.toTiltCurve
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (hvar : ∀ t : ℝ, 0 < L.variance t) : FiniteSupportTiltCurve := by
  refine
    { lo := L.value L.loIndex - L.mean0
      hi := L.value L.hiIndex - L.mean0
      mu := 0
      mean := L.mean
      variance := L.variance
      logMGF := L.logMGF
      hlomu := ?_
      hmuhi := ?_
      mean_zero := law_mean_zero L
      mean_range := ?_
      mean_deriv := law_mean_deriv L
      variance_pos := hvar
      variance_continuous := law_variance_continuous L
      mean_atBot := law_mean_atBot L
      mean_atTop := law_mean_atTop L
      logMGF_zero := ?_
      logMGF_deriv := ?_ }
  · have h := (law_mean_range L 0).1
    rw [law_mean_zero L] at h
    exact h
  · have h := (law_mean_range L 0).2
    rw [law_mean_zero L] at h
    exact h
  · intro t
    exact law_mean_range L t
  · unfold FiniteSupportLawData.logMGF
    rw [finiteMGF_zero_of_normalized L.support L.weight L.centeredValue
      L.weight_total, Real.log_one]
  · intro t
    unfold FiniteSupportLawData.logMGF
    exact finiteLogMGF_hasDerivAt L.support L.weight L.centeredValue
      L.weight_nonneg L.weight_total t

/-- Every nondegenerate finite weighted law in this interface produces the
abstract tilt curve used by the Legendre and envelope theorems. -/
theorem finiteSupportLawData_toTiltCurve
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (hvar : ∀ t : ℝ, 0 < L.variance t) :
    Nonempty (FiniteSupportTiltCurve) := by
  exact ⟨L.toTiltCurve hvar⟩

end
end ExactHoeffding
