import ExactHoeffding.FiniteSupportLawTails

/-! # Exact endpoint Legendre rates of a finite law

At either support endpoint the Legendre candidates converge, along the
corresponding infinite tilts, to the negative logarithm of that endpoint
atom. The atom bound and the supremum property give equality.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

private theorem candidate_eq_neg_log_shift
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (i : ι) (t : ℝ) :
    t * L.centeredValue i - L.logMGF t =
      -Real.log (finiteMGF L.support L.weight
        (fun j => L.centeredValue j - L.centeredValue i) t) := by
  have hshift := finiteMGF_shift L.support L.weight L.centeredValue t
    (-L.centeredValue i)
  have hpos := finiteMGF_pos_of_normalized L.support L.weight L.centeredValue
    L.weight_nonneg L.weight_total t
  have hshift' : finiteMGF L.support L.weight
      (fun j => L.centeredValue j - L.centeredValue i) t =
      Real.exp (t * (-L.centeredValue i)) *
        finiteMGF L.support L.weight L.centeredValue t := by
    simpa only [sub_eq_add_neg] using hshift
  rw [hshift', Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp]
  unfold FiniteSupportLawData.logMGF
  ring

private theorem candidates_bddAbove_at_atom
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (i : ι) (hi : i ∈ L.support) (hw : 0 < L.weight i) :
    BddAbove (Set.range (fun t : ℝ =>
      t * L.centeredValue i - L.logMGF t)) := by
  refine ⟨-Real.log (L.weight i), ?_⟩
  rintro z ⟨t, rfl⟩
  have hterm : L.weight i * Real.exp (t * L.centeredValue i) ≤
      finiteMGF L.support L.weight L.centeredValue t := by
    unfold finiteMGF
    exact Finset.single_le_sum
      (s := L.support)
      (f := fun j => L.weight j * Real.exp (t * L.centeredValue j))
      (fun j hj => mul_nonneg (L.weight_nonneg j hj) (Real.exp_pos _).le) hi
  have hlog := Real.log_le_log (mul_pos hw (Real.exp_pos _)) hterm
  rw [Real.log_mul hw.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  unfold FiniteSupportLawData.logMGF
  linarith

/-- The upper endpoint Legendre candidate converges to the logarithmic atom
cost under positive infinite tilts. -/
theorem FiniteSupportLawData.rateCandidate_tendsto_atTop
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    Tendsto (fun t : ℝ => t * L.centeredValue L.hiIndex - L.logMGF t)
      atTop (𝓝 (-Real.log (L.weight L.hiIndex))) := by
  have hmax : ∀ i ∈ L.support, i ≠ L.hiIndex →
      L.centeredValue i < L.centeredValue L.hiIndex := by
    intro i hi hne
    exact sub_lt_sub_right (L.hi_strict i hi hne) L.mean0
  have hsum := finite_exp_sum_tendsto_atTop L.support L.weight L.centeredValue
    L.hiIndex L.hi_mem hmax
  have hlog := (hsum.log L.hi_weight_pos.ne').neg
  simpa only [candidate_eq_neg_log_shift, finiteMGF] using hlog

/-- The lower endpoint Legendre candidate converges to the logarithmic atom
cost under negative infinite tilts. -/
theorem FiniteSupportLawData.rateCandidate_tendsto_atBot
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    Tendsto (fun t : ℝ => t * L.centeredValue L.loIndex - L.logMGF t)
      atBot (𝓝 (-Real.log (L.weight L.loIndex))) := by
  have hmin : ∀ i ∈ L.support, i ≠ L.loIndex →
      L.centeredValue L.loIndex < L.centeredValue i := by
    intro i hi hne
    exact sub_lt_sub_right (L.lo_strict i hi hne) L.mean0
  have hsum := finite_exp_sum_tendsto_atBot L.support L.weight L.centeredValue
    L.loIndex L.lo_mem hmin
  have hlog := (hsum.log L.lo_weight_pos.ne').neg
  simpa only [candidate_eq_neg_log_shift, finiteMGF] using hlog

/-- The Legendre rate at the upper support endpoint is its exact atom cost. -/
theorem FiniteSupportLawData.legendreRate_hi
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
      (L.value L.hiIndex - L.mean0) = -Real.log (L.weight L.hiIndex) := by
  apply le_antisymm
  · exact L.legendreRate_le_neg_log_weight L.hiIndex L.hi_mem L.hi_weight_pos
  · have hB := candidates_bddAbove_at_atom L L.hiIndex L.hi_mem L.hi_weight_pos
    apply le_of_tendsto L.rateCandidate_tendsto_atTop
    apply Filter.Eventually.of_forall
    intro t
    exact le_csSup hB ⟨t, rfl⟩

/-- The Legendre rate at the lower support endpoint is its exact atom cost. -/
theorem FiniteSupportLawData.legendreRate_lo
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
      (L.value L.loIndex - L.mean0) = -Real.log (L.weight L.loIndex) := by
  apply le_antisymm
  · exact L.legendreRate_le_neg_log_weight L.loIndex L.lo_mem L.lo_weight_pos
  · have hB := candidates_bddAbove_at_atom L L.loIndex L.lo_mem L.lo_weight_pos
    apply le_of_tendsto L.rateCandidate_tendsto_atBot
    apply Filter.Eventually.of_forall
    intro t
    exact le_csSup hB ⟨t, rfl⟩

end
end ExactHoeffding
