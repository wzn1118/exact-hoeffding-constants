import ExactHoeffding.SliceSampling
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.Perm

/-!
# Uniform permutations induce uniform fixed-cardinality subsets

The fibers of the sample-image map have equal cardinality by explicit
postcomposition with a permutation transporting one sample to another.
-/

namespace ExactHoeffding

private theorem map_perm_trans {α : Type*} (S : Finset α) (σ ρ : Equiv.Perm α) :
    S.map (σ.trans ρ).toEmbedding = (S.map σ.toEmbedding).map ρ.toEmbedding := by
  rw [Finset.map_map]
  rfl

/-- All permutations taking a fixed set `S` to the indicated set `A`. -/
noncomputable def permutationSliceFiber {α : Type*} [Fintype α] [DecidableEq α]
    (S A : Finset α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter (fun σ => S.map σ.toEmbedding = A)

/-- Every same-cardinality image fiber has the size of the original-set fiber. -/
theorem permutationSliceFiber_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (S A : Finset α) (hA : A.card = S.card) :
    (permutationSliceFiber S A).card = (permutationSliceFiber S S).card := by
  classical
  obtain ⟨ρ, hρ⟩ := Equiv.Perm.exists_map_finset_eq A S hA
  have hρinv : S.map ρ.symm.toEmbedding = A := by
    rw [← hρ, Finset.map_map]
    simp
  apply Finset.card_nbij' (fun σ => σ.trans ρ) (fun σ => σ.trans ρ.symm)
  · intro σ hσ
    have hs := (Finset.mem_filter.mp hσ).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [map_perm_trans, hs, hρ]⟩
  · intro σ hσ
    have hs := (Finset.mem_filter.mp hσ).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [map_perm_trans, hs, hρinv]⟩
  · intro σ hσ
    ext x
    simp
  · intro σ hσ
    ext x
    simp

theorem permutationSliceFiber_self_pos {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) : 0 < (permutationSliceFiber S S).card := by
  classical
  apply Finset.card_pos.mpr
  refine ⟨Equiv.refl α, ?_⟩
  simp [permutationSliceFiber]

/-- The full permutation space partitions into equally large subset fibers. -/
theorem permutation_card_eq_slice_mul_fiber {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) :
    Fintype.card (Equiv.Perm α) =
      ((Finset.univ : Finset α).powersetCard S.card).card *
        (permutationSliceFiber S S).card := by
  classical
  have hmap : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm α)),
      S.map σ.toEmbedding ∈ (Finset.univ : Finset α).powersetCard S.card := by
    intro σ hσ
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_map _⟩
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  rw [Finset.card_univ] at hfiber
  calc
    _ = ∑ A ∈ (Finset.univ : Finset α).powersetCard S.card,
        (permutationSliceFiber S A).card := hfiber
    _ = ∑ _A ∈ (Finset.univ : Finset α).powersetCard S.card,
        (permutationSliceFiber S S).card := by
      apply Finset.sum_congr rfl
      intro A hA
      exact permutationSliceFiber_card_eq S A (Finset.mem_powersetCard.mp hA).2
    _ = _ := by simp

/-- Exact intersection-count mass under the uniform measure on permutations. -/
noncomputable def permutationIntersectionMass {α : Type*} [Fintype α] [DecidableEq α]
    (S K : Finset α) (i : ℕ) : ℝ :=
  (((Finset.univ : Finset (Equiv.Perm α)).filter
    (fun σ => ((S.map σ.toEmbedding) ∩ K).card = i)).card : ℝ) /
      (Fintype.card (Equiv.Perm α) : ℝ)

theorem permutation_intersection_count {α : Type*} [Fintype α] [DecidableEq α]
    (S K : Finset α) (i : ℕ) :
    ((Finset.univ : Finset (Equiv.Perm α)).filter
      (fun σ => ((S.map σ.toEmbedding) ∩ K).card = i)).card =
      (sliceSamples Finset.univ K S.card i).card * (permutationSliceFiber S S).card := by
  classical
  let p : Finset (Equiv.Perm α) := Finset.univ.filter
    (fun σ => ((S.map σ.toEmbedding) ∩ K).card = i)
  have hmap : ∀ σ ∈ p, S.map σ.toEmbedding ∈ sliceSamples Finset.univ K S.card i := by
    intro σ hσ
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_map _⟩,
      (Finset.mem_filter.mp hσ).2⟩
  have hfiber := Finset.card_eq_sum_card_fiberwise hmap
  change p.card = _
  rw [hfiber]
  calc
    _ = ∑ _A ∈ sliceSamples Finset.univ K S.card i,
        (permutationSliceFiber S S).card := by
      apply Finset.sum_congr rfl
      intro A hA
      have hAsize := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hA).1).2
      have hAcount := (Finset.mem_filter.mp hA).2
      have heq : p.filter (fun σ => S.map σ.toEmbedding = A) =
          permutationSliceFiber S A := by
        ext σ
        simp only [p, permutationSliceFiber, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · exact fun h => h.2
        · intro h
          exact ⟨by rw [h]; exact hAcount, h⟩
      rw [heq, permutationSliceFiber_card_eq S A hAsize]
    _ = _ := by simp

theorem permutationIntersectionMass_eq_uniformSlice {α : Type*} [Fintype α]
    [DecidableEq α] (S K : Finset α) (i : ℕ) :
    permutationIntersectionMass S K i = uniformSliceIntersectionMass Finset.univ K S.card i := by
  classical
  unfold permutationIntersectionMass uniformSliceIntersectionMass
  rw [permutation_intersection_count, permutation_card_eq_slice_mul_fiber S]
  push_cast
  have hf : ((permutationSliceFiber S S).card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (permutationSliceFiber_self_pos S)
  exact mul_div_mul_right _ _ hf

/-- The actual uniform-permutation model has the totalized hypergeometric law. -/
theorem permutationIntersectionMass_eq_hypergeomPMF (N : ℕ)
    (S K : Finset (Fin N)) (i : ℕ) :
    permutationIntersectionMass S K i = hypergeomPMFValue N K.card S.card i := by
  rw [permutationIntersectionMass_eq_uniformSlice]
  exact fin_uniformSliceIntersectionMass_eq_hypergeomPMF N S.card i K

/-- Finite uniform permutation expectation, grouped by the actual count. -/
theorem uniformPermutation_expectation {α : Type*} [Fintype α] [DecidableEq α]
    (S K : Finset α) (f : ℕ → ℝ) :
    (∑ σ : Equiv.Perm α, f ((S.map σ.toEmbedding) ∩ K).card) /
        (Fintype.card (Equiv.Perm α) : ℝ) =
      ∑ i ∈ Finset.range (S.card + 1), permutationIntersectionMass S K i * f i := by
  classical
  have hmap : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm α)),
      ((S.map σ.toEmbedding) ∩ K).card ∈ Finset.range (S.card + 1) := by
    intro σ hσ
    have hle := Finset.card_le_card
      (Finset.inter_subset_left : (S.map σ.toEmbedding) ∩ K ⊆ S.map σ.toEmbedding)
    rw [Finset.card_map] at hle
    exact Finset.mem_range.mpr (by omega)
  have hfiber := Finset.sum_fiberwise_of_maps_to' hmap f
  rw [← hfiber, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.sum_const, nsmul_eq_mul, permutationIntersectionMass]
  ring

/-- Uniform permutations of a fixed sample have exactly the hypergeometric MGF. -/
theorem uniformPermutation_mgf (N : ℕ) (S K : Finset (Fin N)) (t : ℝ) :
    (∑ σ : Equiv.Perm (Fin N), Real.exp (t * (((S.map σ.toEmbedding) ∩ K).card : ℝ))) /
        (Fintype.card (Equiv.Perm (Fin N)) : ℝ) = hypergeomMGF N K.card S.card t := by
  rw [uniformPermutation_expectation S K (fun i => Real.exp (t * i))]
  unfold hypergeomMGF finiteMGF
  apply Finset.sum_congr rfl
  intro i hi
  rw [permutationIntersectionMass_eq_hypergeomPMF]
  have him : i ≤ S.card := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp only [hypergeomPMFValue, if_pos him]

end ExactHoeffding
