import ExactHoeffding.Support
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card

/-!
# Exact hypergeometric counting on uniform finite slices

A sample is an actual subset of fixed cardinality. Splitting it into marked
and unmarked elements proves the coefficient formula before normalization.
-/

namespace ExactHoeffding

/-- The samples of size `m` with exactly `i` marked elements. -/
def sliceSamples {α : Type*} [DecidableEq α] (T K : Finset α) (m i : ℕ) :
    Finset (Finset α) :=
  (T.powersetCard m).filter (fun S => (S ∩ K).card = i)

private theorem union_marked_parts {α : Type*} [DecidableEq α]
    (T K A B : Finset α) (hA : A ⊆ K) (hB : B ⊆ T \ K) :
    (A ∪ B) ∩ K = A ∧ (A ∪ B) \ K = B := by
  constructor
  · ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxK⟩
      · exact hx
      · exact False.elim ((Finset.mem_sdiff.mp (hB hx)).2 hxK)
    · intro hx
      exact ⟨Or.inl hx, hA hx⟩
  · ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hx | hx, hxK⟩
      · exact False.elim (hxK (hA hx))
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, (Finset.mem_sdiff.mp (hB hx)).2⟩

/-- Splitting a sample into its marked and unmarked parts is a genuine
bijection with the product of the two fixed-cardinality subset families. -/
theorem sliceSamples_card_product {α : Type*} [DecidableEq α]
    (T K : Finset α) (hKT : K ⊆ T) (m i : ℕ) (him : i ≤ m) :
    (sliceSamples T K m i).card =
      (K.powersetCard i ×ˢ (T \ K).powersetCard (m - i)).card := by
  apply Finset.card_nbij'
    (fun S => (S ∩ K, S \ K)) (fun p => p.1 ∪ p.2)
  · intro S hS
    rcases Finset.mem_filter.mp hS with ⟨hsize, hmarked⟩
    rcases Finset.mem_powersetCard.mp hsize with ⟨hST, hSm⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hmarked⟩
    · apply Finset.mem_powersetCard.mpr
      constructor
      · intro x hx
        exact Finset.mem_sdiff.mpr ⟨hST (Finset.mem_sdiff.mp hx).1,
          (Finset.mem_sdiff.mp hx).2⟩
      · have hc := Finset.card_sdiff_add_card_inter S K
        change (S \ K).card = m - i
        rw [hmarked, hSm] at hc
        omega
  · rintro ⟨A, B⟩ hp
    rcases Finset.mem_product.mp hp with ⟨hA, hB⟩
    rcases Finset.mem_powersetCard.mp hA with ⟨hAK, hAi⟩
    rcases Finset.mem_powersetCard.mp hB with ⟨hBT, hBi⟩
    have hd : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxB
      exact (Finset.mem_sdiff.mp (hBT hxB)).2 (hAK hxA)
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      constructor
      · exact Finset.union_subset (hAK.trans hKT) (hBT.trans Finset.sdiff_subset)
      · rw [Finset.card_union_of_disjoint hd, hAi, hBi]
        omega
    · rw [(union_marked_parts T K A B hAK hBT).1, hAi]
  · intro S hS
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    by_cases hx : x ∈ K <;> simp [hx]
  · rintro ⟨A, B⟩ hp
    rcases Finset.mem_product.mp hp with ⟨hA, hB⟩
    have hparts := union_marked_parts T K A B
      (Finset.mem_powersetCard.mp hA).1 (Finset.mem_powersetCard.mp hB).1
    exact Prod.ext hparts.1 hparts.2

/-- The exact hypergeometric coefficient is the cardinality of the slice fiber. -/
theorem sliceSamples_card {α : Type*} [DecidableEq α]
    (T K : Finset α) (hKT : K ⊆ T) (m i : ℕ) (him : i ≤ m) :
    (sliceSamples T K m i).card =
      Nat.choose K.card i * Nat.choose (T.card - K.card) (m - i) := by
  rw [sliceSamples_card_product T K hKT m i him, Finset.card_product,
    Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_sdiff_of_subset hKT]

/-- There are no samples with more marked elements than total draws. -/
theorem sliceSamples_eq_empty_of_lt {α : Type*} [DecidableEq α]
    (T K : Finset α) (m i : ℕ) (hmi : m < i) : sliceSamples T K m i = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  rcases Finset.mem_filter.mp hS with ⟨hsize, hmarked⟩
  have hcard := (Finset.mem_powersetCard.mp hsize).2
  have hle := Finset.card_le_card (Finset.inter_subset_left : S ∩ K ⊆ S)
  omega

/-- Uniform sampling from all `m`-subsets, evaluated on an intersection count. -/
noncomputable def uniformSliceIntersectionMass {α : Type*} [DecidableEq α]
    (T K : Finset α) (m i : ℕ) : ℝ :=
  ((sliceSamples T K m i).card : ℝ) / ((T.powersetCard m).card : ℝ)

/-- Exact equality on all natural indices, including zero outside the support. -/
theorem uniformSliceIntersectionMass_eq_hypergeomPMF {α : Type*} [DecidableEq α]
    (T K : Finset α) (hKT : K ⊆ T) (m i : ℕ) :
    uniformSliceIntersectionMass T K m i = hypergeomPMFValue T.card K.card m i := by
  by_cases him : i ≤ m
  · unfold uniformSliceIntersectionMass hypergeomPMFValue hypergeomMass hypergeomCount
    rw [if_pos him, sliceSamples_card T K hKT m i him, Finset.card_powersetCard]
  · rw [uniformSliceIntersectionMass, sliceSamples_eq_empty_of_lt T K m i (by omega)]
    simp [hypergeomPMFValue, him]

/-- The original `Fin N` model of a fixed marked set and a uniform sample. -/
theorem fin_uniformSliceIntersectionMass_eq_hypergeomPMF (N m i : ℕ)
    (K : Finset (Fin N)) :
    uniformSliceIntersectionMass Finset.univ K m i = hypergeomPMFValue N K.card m i := by
  simpa only [Finset.card_univ, Fintype.card_fin] using
    uniformSliceIntersectionMass_eq_hypergeomPMF Finset.univ K
      (Finset.subset_univ K) m i

/-- For an admissible sample size, these actual sampling probabilities sum to one. -/
theorem uniformSliceIntersectionMass_sum {α : Type*} [DecidableEq α]
    (T K : Finset α) (hKT : K ⊆ T) (m : ℕ) (hm : m ≤ T.card) :
    ∑ i ∈ Finset.range (m + 1), uniformSliceIntersectionMass T K m i = 1 := by
  simp_rw [uniformSliceIntersectionMass_eq_hypergeomPMF T K hKT]
  exact hypergeomPMFValue_sum_range T.card K.card m (Finset.card_le_card hKT) hm

/-- Any function of the sample intersection has the exact finite
hypergeometric expectation, directly from the partition into count fibers. -/
theorem uniformSlice_expectation {α : Type*} [DecidableEq α]
    (T K : Finset α) (hKT : K ⊆ T) (m : ℕ) (f : ℕ → ℝ) :
    (∑ S ∈ T.powersetCard m, f (S ∩ K).card) / ((T.powersetCard m).card : ℝ) =
      ∑ i ∈ Finset.range (m + 1), hypergeomPMFValue T.card K.card m i * f i := by
  have hmap : ∀ S ∈ T.powersetCard m, (S ∩ K).card ∈ Finset.range (m + 1) := by
    intro S hS
    have hcard := (Finset.mem_powersetCard.mp hS).2
    have hle := Finset.card_le_card (Finset.inter_subset_left : S ∩ K ⊆ S)
    exact Finset.mem_range.mpr (by omega)
  have hfiber := Finset.sum_fiberwise_of_maps_to' hmap f
  have hsum : (∑ S ∈ T.powersetCard m, f (S ∩ K).card) =
      ∑ i ∈ Finset.range (m + 1), ((sliceSamples T K m i).card : ℝ) * f i := by
    symm
    simpa only [sliceSamples, Finset.sum_const, nsmul_eq_mul] using hfiber
  rw [hsum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← uniformSliceIntersectionMass_eq_hypergeomPMF T K hKT m i]
  unfold uniformSliceIntersectionMass
  ring

/-- The MGF of the actual uniform subset intersection equals the existing
hypergeometric MGF used throughout the analytic proof. -/
theorem uniformSlice_mgf {α : Type*} [DecidableEq α]
    (T K : Finset α) (hKT : K ⊆ T) (m : ℕ) (t : ℝ) :
    (∑ S ∈ T.powersetCard m, Real.exp (t * ((S ∩ K).card : ℝ))) /
        ((T.powersetCard m).card : ℝ) = hypergeomMGF T.card K.card m t := by
  rw [uniformSlice_expectation T K hKT m (fun i => Real.exp (t * i))]
  unfold hypergeomMGF finiteMGF
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp only [hypergeomPMFValue, if_pos him]

end ExactHoeffding
