import ExactHoeffding.TwoLevelOptimization
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ExactHoeffding

def fixedSumSquareSet {N : ℕ} (y : Fin N → ℝ) : Set (Fin N → ℝ) :=
  {v | (∑ i, v i) = ∑ i, y i ∧ (∑ i, (v i) ^ 2) = ∑ i, (y i) ^ 2}

theorem fixedSumSquareSet_isCompact {N : ℕ} (y : Fin N → ℝ) :
    IsCompact (fixedSumSquareSet y) := by
  have hsum : Continuous (fun v : Fin N → ℝ => ∑ i, v i) :=
    continuous_finsetSum Finset.univ (fun i _ => continuous_apply i)
  have hsq : Continuous (fun v : Fin N → ℝ => ∑ i, (v i) ^ 2) :=
    continuous_finsetSum Finset.univ (fun i _ => (continuous_apply i).pow 2)
  have hclosed : IsClosed (fixedSumSquareSet y) :=
    (isClosed_eq hsum continuous_const).inter (isClosed_eq hsq continuous_const)
  let Q := ∑ i : Fin N, (y i) ^ 2
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ => sq_nonneg (y i))
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin N => -(Q + 1)) (fun _ => Q + 1))).of_isClosed_subset hclosed
  intro v hv
  have hvQ : (∑ i : Fin N, (v i) ^ 2) = Q := hv.2
  constructor <;> intro i
  · have hi : (v i) ^ 2 ≤ Q := by
      rw [← hvQ]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    nlinarith [sq_nonneg (v i + 1), sq_nonneg (v i - 1)]
  · have hi : (v i) ^ 2 ≤ Q := by
      rw [← hvQ]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
    nlinarith [sq_nonneg (v i + 1), sq_nonneg (v i - 1)]

theorem sliceExponential_continuous (N k : ℕ) :
    Continuous (fun y : Fin N → ℝ => sliceExponential Finset.univ y k) := by
  simp_rw [sliceExponential_nat]
  apply continuous_finsetSum
  intro S hS
  exact Real.continuous_exp.comp (continuous_finsetSum S (fun i _ => continuous_apply i))

/-- The two-level reduction with an actual maximizer, not an assumed extremizer. -/
theorem exists_two_level_slice_dominator (N k : ℕ) (hk0 : 0 < k) (hkN : k < N)
    (y : Fin N → ℝ) :
    ∃ v : Fin N → ℝ,
      (∑ i, v i) = ∑ i, y i ∧ (∑ i, (v i) ^ 2) = ∑ i, (y i) ^ 2 ∧
      (Finset.univ.image v).card ≤ 2 ∧
      sliceExponential Finset.univ y k ≤ sliceExponential Finset.univ v k := by
  classical
  have hy : y ∈ fixedSumSquareSet y := ⟨rfl, rfl⟩
  obtain ⟨v, hv, hmax⟩ := (fixedSumSquareSet_isCompact y).exists_isMaxOn ⟨y, hy⟩
    (sliceExponential_continuous N k).continuousOn
  have htwo := sliceExponential_maximizer_at_most_two N k hk0 hkN v (by
    intro w hsum hsq
    apply hmax
    exact ⟨hsum.trans hv.1, hsq.trans hv.2⟩)
  exact ⟨v, hv.1, hv.2, htwo, hmax hy⟩

end ExactHoeffding
