import ExactHoeffding.FiniteSupportChernoffEnvelope
import ExactHoeffding.FiniteSupportLawVariance
import ExactHoeffding.Chernoff

/-! # Actual tail probabilities of a finite weighted law

The exponential Markov inequalities are proved from the weights. Optimizing
at the inverse tilted mean gives the exact Legendre rate in the interior;
the two endpoint atoms give the corresponding closed-support bounds.
-/

namespace ExactHoeffding
noncomputable section

open Set

/-- Upper-tail probability of the centered finite law. -/
def FiniteSupportLawData.upperTail {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (v : ℝ) : ℝ :=
  ∑ i ∈ L.support, if v ≤ L.centeredValue i then L.weight i else 0

/-- Lower-tail probability of the centered finite law. -/
def FiniteSupportLawData.lowerTail {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (v : ℝ) : ℝ :=
  ∑ i ∈ L.support, if L.centeredValue i ≤ v then L.weight i else 0

theorem FiniteSupportLawData.upperTail_nonneg {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (v : ℝ) : 0 ≤ L.upperTail v := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact L.weight_nonneg i hi
  · exact le_rfl

theorem FiniteSupportLawData.lowerTail_nonneg {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (v : ℝ) : 0 ≤ L.lowerTail v := by
  apply Finset.sum_nonneg
  intro i hi
  split_ifs
  · exact L.weight_nonneg i hi
  · exact le_rfl

theorem FiniteSupportLawData.upperTail_le_one {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (v : ℝ) : L.upperTail v ≤ 1 := by
  rw [← L.weight_total]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs
  · exact le_rfl
  · exact L.weight_nonneg i hi

theorem FiniteSupportLawData.lowerTail_le_one {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (v : ℝ) : L.lowerTail v ≤ 1 := by
  rw [← L.weight_total]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs
  · exact le_rfl
  · exact L.weight_nonneg i hi

/-- Exponential Markov bound at every nonnegative tilt, derived from the
actual finite weights and centered values. -/
theorem FiniteSupportLawData.upperTail_le_exp {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (v t : ℝ) (ht : 0 ≤ t) :
    L.upperTail v ≤ Real.exp (-t * v + L.logMGF t) := by
  have hm := finite_markov_exp_bound L.support L.weight L.centeredValue
    (fun i => v ≤ L.centeredValue i) L.weight_nonneg t v ht
    (fun _ _ hi => hi)
  have hpos := finiteMGF_pos_of_normalized L.support L.weight L.centeredValue
    L.weight_nonneg L.weight_total t
  calc
    L.upperTail v ≤ Real.exp (-t * v) *
        finiteMGF L.support L.weight L.centeredValue t := hm
    _ = Real.exp (-t * v + L.logMGF t) := by
      rw [Real.exp_add]
      unfold FiniteSupportLawData.logMGF
      rw [Real.exp_log hpos]

/-- Exponential Markov bound at every nonpositive tilt. Reflection of the
values reduces it to the finite positive-tilt inequality. -/
theorem FiniteSupportLawData.lowerTail_le_exp {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (v t : ℝ) (ht : t ≤ 0) :
    L.lowerTail v ≤ Real.exp (-t * v + L.logMGF t) := by
  have hm := finite_markov_exp_bound L.support L.weight
    (fun i => -L.centeredValue i) (fun i => L.centeredValue i ≤ v)
    L.weight_nonneg (-t) (-v) (neg_nonneg.mpr ht)
    (fun _ _ hi => neg_le_neg hi)
  have hflip : finiteMGF L.support L.weight (fun i => -L.centeredValue i) (-t) =
      finiteMGF L.support L.weight L.centeredValue t := by
    simp only [finiteMGF, neg_mul_neg]
  have hsign : -(-t) * (-v) = -t * v := by ring
  rw [hflip, hsign] at hm
  have hpos := finiteMGF_pos_of_normalized L.support L.weight L.centeredValue
    L.weight_nonneg L.weight_total t
  calc
    L.lowerTail v ≤ Real.exp (-t * v) *
        finiteMGF L.support L.weight L.centeredValue t := hm
    _ = Real.exp (-t * v + L.logMGF t) := by
      rw [Real.exp_add]
      unfold FiniteSupportLawData.logMGF
      rw [Real.exp_log hpos]

/-- The actual upper tail has the optimized Legendre bound at every interior
threshold at or above the centered mean. -/
theorem FiniteSupportLawData.upperTail_le_exp_neg_rate_interior
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hv0 : 0 ≤ v) (hvhi : v < L.value L.hiIndex - L.mean0) :
    L.upperTail v ≤
      Real.exp (-finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v) := by
  apply finiteSupport_upper_tail_of_markov_interior
    (L.toTiltCurve L.variance_pos) L.upperTail hv0 hvhi
  intro t ht
  exact L.upperTail_le_exp v t ht

/-- The actual lower tail has the optimized Legendre bound at every interior
threshold at or below the centered mean. -/
theorem FiniteSupportLawData.lowerTail_le_exp_neg_rate_interior
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hvlo : L.value L.loIndex - L.mean0 < v) (hv0 : v ≤ 0) :
    L.lowerTail v ≤
      Real.exp (-finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v) := by
  apply finiteSupport_lower_tail_of_markov_interior
    (L.toTiltCurve L.variance_pos) L.lowerTail hvlo hv0
  intro t ht
  exact L.lowerTail_le_exp v t ht

/-- The rate at any positive atom is at most the negative logarithm of its
weight. The estimate bounds every Legendre candidate before taking `sSup`. -/
theorem FiniteSupportLawData.legendreRate_le_neg_log_weight
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι)
    (i : ι) (hi : i ∈ L.support) (hw : 0 < L.weight i) :
    finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) (L.centeredValue i) ≤
      -Real.log (L.weight i) := by
  unfold finiteSupportLegendreRate
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  have hterm : L.weight i * Real.exp (t * L.centeredValue i) ≤
      finiteMGF L.support L.weight L.centeredValue t := by
    unfold finiteMGF
    exact Finset.single_le_sum
      (s := L.support)
      (f := fun j => L.weight j * Real.exp (t * L.centeredValue j))
      (fun j hj => mul_nonneg (L.weight_nonneg j hj) (Real.exp_pos _).le) hi
  have hlog := Real.log_le_log (mul_pos hw (Real.exp_pos _)) hterm
  rw [Real.log_mul hw.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  change t * L.centeredValue i -
    Real.log (finiteMGF L.support L.weight L.centeredValue t) ≤ -Real.log (L.weight i)
  linarith

/-- At the maximum centered value, the upper tail is exactly its atom. -/
theorem FiniteSupportLawData.upperTail_at_hi {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) :
    L.upperTail (L.value L.hiIndex - L.mean0) = L.weight L.hiIndex := by
  unfold FiniteSupportLawData.upperTail
  calc
    _ = ∑ i ∈ L.support, if i = L.hiIndex then L.weight i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases heq : i = L.hiIndex
      · subst i
        simp [FiniteSupportLawData.centeredValue]
      · have hlt := L.hi_strict i hi heq
        have hn : ¬ L.value L.hiIndex - L.mean0 ≤ L.centeredValue i := by
          dsimp [FiniteSupportLawData.centeredValue]
          linarith
        simp [heq, hn]
    _ = L.weight L.hiIndex := by simp [L.hi_mem]

/-- At the minimum centered value, the lower tail is exactly its atom. -/
theorem FiniteSupportLawData.lowerTail_at_lo {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) :
    L.lowerTail (L.value L.loIndex - L.mean0) = L.weight L.loIndex := by
  unfold FiniteSupportLawData.lowerTail
  calc
    _ = ∑ i ∈ L.support, if i = L.loIndex then L.weight i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases heq : i = L.loIndex
      · subst i
        simp [FiniteSupportLawData.centeredValue]
      · have hlt := L.lo_strict i hi heq
        have hn : ¬ L.centeredValue i ≤ L.value L.loIndex - L.mean0 := by
          dsimp [FiniteSupportLawData.centeredValue]
          linarith
        simp [heq, hn]
    _ = L.weight L.loIndex := by simp [L.lo_mem]

/-- Actual Chernoff bound at the upper support endpoint. -/
theorem FiniteSupportLawData.upperTail_le_exp_neg_rate_endpoint
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    L.upperTail (L.value L.hiIndex - L.mean0) ≤
      Real.exp (-finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.hiIndex - L.mean0)) := by
  rw [L.upperTail_at_hi]
  have hrate := L.legendreRate_le_neg_log_weight L.hiIndex L.hi_mem L.hi_weight_pos
  calc
    L.weight L.hiIndex = Real.exp (Real.log (L.weight L.hiIndex)) :=
      (Real.exp_log L.hi_weight_pos).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      change finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.hiIndex - L.mean0) ≤ -Real.log (L.weight L.hiIndex) at hrate
      linarith)

/-- Actual Chernoff bound at the lower support endpoint. -/
theorem FiniteSupportLawData.lowerTail_le_exp_neg_rate_endpoint
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) :
    L.lowerTail (L.value L.loIndex - L.mean0) ≤
      Real.exp (-finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.loIndex - L.mean0)) := by
  rw [L.lowerTail_at_lo]
  have hrate := L.legendreRate_le_neg_log_weight L.loIndex L.lo_mem L.lo_weight_pos
  calc
    L.weight L.loIndex = Real.exp (Real.log (L.weight L.loIndex)) :=
      (Real.exp_log L.lo_weight_pos).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by
      change finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.loIndex - L.mean0) ≤ -Real.log (L.weight L.loIndex) at hrate
      linarith)

/-- Upper-tail Legendre bound on the complete closed upper half-support. -/
theorem FiniteSupportLawData.upperTail_le_exp_neg_rate
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hv0 : 0 ≤ v) (hvhi : v ≤ L.value L.hiIndex - L.mean0) :
    L.upperTail v ≤
      Real.exp (-finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v) := by
  rcases hvhi.eq_or_lt with heq | hlt
  · rw [heq]
    exact L.upperTail_le_exp_neg_rate_endpoint
  · exact L.upperTail_le_exp_neg_rate_interior hv0 hlt

/-- Lower-tail Legendre bound on the complete closed lower half-support. -/
theorem FiniteSupportLawData.lowerTail_le_exp_neg_rate
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) {v : ℝ}
    (hvlo : L.value L.loIndex - L.mean0 ≤ v) (hv0 : v ≤ 0) :
    L.lowerTail v ≤
      Real.exp (-finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v) := by
  rcases hvlo.eq_or_lt with heq | hlt
  · rw [← heq]
    exact L.lowerTail_le_exp_neg_rate_endpoint
  · exact L.lowerTail_le_exp_neg_rate_interior hlt hv0

end
end ExactHoeffding
