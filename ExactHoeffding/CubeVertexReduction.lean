import ExactHoeffding.FiniteExchangeability
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Pointwise reduction of the real cube to its sign vertices

The finite product convex-hull theorem identifies the entire cube with the
convex hull of its vertices. The convex maximum principle then gives the
actual pointwise vertex reduction.
-/

namespace ExactHoeffding

def realCube (N : ℕ) : Set (Fin N → ℝ) :=
  Set.univ.pi (fun _ => Set.Icc (-1 : ℝ) 1)

def signVertex {N : ℕ} (S : Finset (Fin N)) : Fin N → ℝ :=
  fun i => if i ∈ S then 1 else -1

theorem signVertex_mem_realCube {N : ℕ} (S : Finset (Fin N)) :
    signVertex S ∈ realCube N := by
  intro i hi
  dsimp [signVertex]
  split_ifs <;> constructor <;> norm_num

/-- The real cube is exactly the convex hull of its two-valued vertices. -/
theorem realCube_eq_convexHull_vertices (N : ℕ) :
    realCube N = convexHull ℝ (Set.univ.pi (fun _ : Fin N => ({-1, 1} : Set ℝ))) := by
  rw [convexHull_pi]
  have hpair : convexHull ℝ ({-1, 1} : Set ℝ) = Set.Icc (-1 : ℝ) 1 := by
    rw [convexHull_pair, segment_eq_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
  simp only [hpair, realCube]

/-- Every vertex in the product representation comes from an actual subset. -/
theorem vertex_eq_signVertex {N : ℕ} (v : Fin N → ℝ)
    (hv : v ∈ Set.univ.pi (fun _ : Fin N => ({-1, 1} : Set ℝ))) :
    ∃ S : Finset (Fin N), v = signVertex S := by
  classical
  refine ⟨Finset.univ.filter (fun i => v i = 1), ?_⟩
  funext i
  have hi := hv i (Set.mem_univ i)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  simp only [signVertex, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hi with hi | hi
  · rw [hi]
    norm_num
  · rw [hi]
    norm_num

/-- A convex function at an arbitrary cube point is bounded by one actual sign vertex. -/
theorem convexOn_realCube_le_vertex {N : ℕ} (f : (Fin N → ℝ) → ℝ)
    (hf : ConvexOn ℝ (realCube N) f) (x : Fin N → ℝ) (hx : x ∈ realCube N) :
    ∃ S : Finset (Fin N), f x ≤ f (signVertex S) := by
  have hverts : Set.univ.pi (fun _ : Fin N => ({-1, 1} : Set ℝ)) ⊆ realCube N := by
    intro v hv
    obtain ⟨S, rfl⟩ := vertex_eq_signVertex v hv
    exact signVertex_mem_realCube S
  have hx' : x ∈ convexHull ℝ (Set.univ.pi (fun _ : Fin N => ({-1, 1} : Set ℝ))) := by
    rw [← realCube_eq_convexHull_vertices]
    exact hx
  obtain ⟨v, hv, hfv⟩ := hf.exists_ge_of_mem_convexHull hverts hx'
  obtain ⟨S, rfl⟩ := vertex_eq_signVertex v hv
  exact ⟨S, hfv⟩

/-- Exponential linear contrast averaged over the actual finite permutation group. -/
noncomputable def symmetrizedExpContrast {N : ℕ} (a : Fin N → ℝ) (t : ℝ)
    (x : Fin N → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin N), Real.exp (t * ∑ i : Fin N, a i * x (σ.symm i))) /
    (Fintype.card (Equiv.Perm (Fin N)) : ℝ)

/-- Convexity of the symmetrized exponential follows termwise from real exponential convexity. -/
theorem symmetrizedExpContrast_convexOn {N : ℕ} (a : Fin N → ℝ) (t : ℝ) :
    ConvexOn ℝ (realCube N) (symmetrizedExpContrast a t) := by
  refine ⟨convex_pi (fun _ _ => convex_Icc _ _), ?_⟩
  intro x hx y hy c d hc hd hcd
  have hterm (σ : Equiv.Perm (Fin N)) :
      Real.exp (t * ∑ i : Fin N, a i * ((c • x + d • y) (σ.symm i))) ≤
        c * Real.exp (t * ∑ i : Fin N, a i * x (σ.symm i)) +
          d * Real.exp (t * ∑ i : Fin N, a i * y (σ.symm i)) := by
    have hlin : (t * ∑ i : Fin N, a i * ((c • x + d • y) (σ.symm i))) =
        c * (t * ∑ i : Fin N, a i * x (σ.symm i)) +
          d * (t * ∑ i : Fin N, a i * y (σ.symm i)) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hlin]
    exact convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) hc hd hcd
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin N)))) => hterm σ)
  have hdiv := div_le_div_of_nonneg_right hsum
    (show (0 : ℝ) ≤ Fintype.card (Equiv.Perm (Fin N)) by positivity)
  simpa only [symmetrizedExpContrast, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, add_div, mul_div_assoc] using hdiv

/-- Uniform permutation averages over a fixed set equal the uniform average
over its cardinality slice, for every real-valued test function. -/
theorem uniformPermutation_subset_average {N : ℕ} (S : Finset (Fin N))
    (g : Finset (Fin N) → ℝ) :
    (∑ σ : Equiv.Perm (Fin N), g (S.map σ.toEmbedding)) /
        (Fintype.card (Equiv.Perm (Fin N)) : ℝ) = hammingSliceAverage g S.card := by
  classical
  have hmap : ∀ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin N))),
      S.map σ.toEmbedding ∈ (Finset.univ : Finset (Fin N)).powersetCard S.card := by
    intro σ hσ
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Finset.card_map _⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to' hmap g
  have hsum : (∑ σ : Equiv.Perm (Fin N), g (S.map σ.toEmbedding)) =
      ((permutationSliceFiber S S).card : ℝ) *
        ∑ A ∈ (Finset.univ : Finset (Fin N)).powersetCard S.card, g A := by
    rw [← hfiber, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [show (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => S.map σ.toEmbedding = A)).card =
      (permutationSliceFiber S S).card from
        permutationSliceFiber_card_eq S A (Finset.mem_powersetCard.mp hA).2]
  rw [hsum, permutation_card_eq_slice_mul_fiber S]
  unfold hammingSliceAverage
  push_cast
  have hf : ((permutationSliceFiber S S).card : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (permutationSliceFiber_self_pos S)
  rw [mul_comm ((permutationSliceFiber S S).card : ℝ), mul_div_mul_right _ _ hf]

theorem symmetrizedExpContrast_vertex {N : ℕ} (a : Fin N → ℝ) (t : ℝ)
    (S : Finset (Fin N)) :
    symmetrizedExpContrast a t (signVertex S) =
      hammingSliceAverage (fun T => Real.exp (t * booleanContrast a T)) S.card := by
  have hpoint (σ : Equiv.Perm (Fin N)) :
      (∑ i : Fin N, a i * signVertex S (σ.symm i)) = booleanContrast a (S.map σ.toEmbedding) := by
    unfold booleanContrast signVertex
    simp only [Finset.mem_map_equiv]
  unfold symmetrizedExpContrast
  simp_rw [hpoint]
  exact uniformPermutation_subset_average S (fun T => Real.exp (t * booleanContrast a T))

/-- Every real cube point obeys the finite maximum of genuine Hamming-slice MGFs. -/
theorem symmetrizedExpContrast_le_max_slice {N : ℕ} (a : Fin N → ℝ) (t : ℝ)
    (x : Fin N → ℝ) (hx : x ∈ realCube N) :
    symmetrizedExpContrast a t x ≤
      (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (hammingSliceAverage (fun S => Real.exp (t * booleanContrast a S))) := by
  obtain ⟨S, hS⟩ := convexOn_realCube_le_vertex (symmetrizedExpContrast a t)
    (symmetrizedExpContrast_convexOn a t) x hx
  rw [symmetrizedExpContrast_vertex] at hS
  have hcard : S.card ≤ N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ S)
  exact hS.trans (Finset.le_sup'
    (f := hammingSliceAverage (fun T => Real.exp (t * booleanContrast a T)))
    (Finset.mem_range.mpr (by omega)))

end ExactHoeffding
