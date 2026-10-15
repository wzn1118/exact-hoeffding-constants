import ExactHoeffding.PermutationSlice
import ExactHoeffding.Sampling
import ExactHoeffding.Contrasts
import ExactHoeffding.Symmetries
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Finite Boolean exchangeability and uniform Hamming slices

Boolean cube points are represented by their subsets of positive coordinates.
Permutation invariance makes a finite probability mass constant on each
cardinality class, giving an exact convex mixture of uniform slices.
-/

namespace ExactHoeffding

/-- Coordinate-permutation invariance of a finite Boolean-cube mass. -/
def BooleanExchangeable {N : ℕ} (μ : Finset (Fin N) → ℝ) : Prop :=
  ∀ (S : Finset (Fin N)) (σ : Equiv.Perm (Fin N)), μ (S.map σ.toEmbedding) = μ S

noncomputable def hammingSliceWeight {N : ℕ} (μ : Finset (Fin N) → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, μ S

noncomputable def hammingSliceAverage {N : ℕ} (f : Finset (Fin N) → ℝ) (k : ℕ) : ℝ :=
  (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, f S) /
    (((Finset.univ : Finset (Fin N)).powersetCard k).card : ℝ)

theorem BooleanExchangeable.eq_of_card_eq {N : ℕ} {μ : Finset (Fin N) → ℝ}
    (hμ : BooleanExchangeable μ) (S T : Finset (Fin N)) (hST : S.card = T.card) :
    μ S = μ T := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq S T hST
  rw [← hσ]
  exact (hμ S σ).symm

/-- Partition any cube sum by its actual Hamming weight. -/
theorem booleanCube_sum_by_card {N : ℕ} (g : Finset (Fin N) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, g S) =
      ∑ k ∈ Finset.range (N + 1),
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, g S := by
  have hmap : ∀ S ∈ (Finset.univ : Finset (Fin N)).powerset,
      S.card ∈ Finset.range (N + 1) := by
    intro S hS
    have hle := Finset.card_le_card (Finset.subset_univ S)
    simp only [Finset.card_univ, Fintype.card_fin] at hle
    exact Finset.mem_range.mpr (by omega)
  have hfiber := Finset.sum_fiberwise_of_maps_to hmap g
  simpa only [← Finset.powersetCard_eq_filter] using hfiber.symm

theorem hammingSliceWeight_nonneg {N : ℕ} (μ : Finset (Fin N) → ℝ)
    (hμ : ∀ S, 0 ≤ μ S) (k : ℕ) : 0 ≤ hammingSliceWeight μ k := by
  exact Finset.sum_nonneg (fun S _ => hμ S)

theorem hammingSliceWeight_sum {N : ℕ} (μ : Finset (Fin N) → ℝ)
    (hnorm : ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, μ S = 1) :
    ∑ k ∈ Finset.range (N + 1), hammingSliceWeight μ k = 1 := by
  unfold hammingSliceWeight
  rw [← booleanCube_sum_by_card μ]
  exact hnorm

theorem BooleanExchangeable.slice_factorization {N : ℕ}
    {μ : Finset (Fin N) → ℝ} (hμ : BooleanExchangeable μ)
    (f : Finset (Fin N) → ℝ) (k : ℕ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, μ S * f S) =
      hammingSliceWeight μ k * hammingSliceAverage f k := by
  let s := (Finset.univ : Finset (Fin N)).powersetCard k
  rcases s.eq_empty_or_nonempty with hs | hs
  · simp only [hammingSliceWeight, hammingSliceAverage]
    change (∑ S ∈ s, μ S * f S) = (∑ S ∈ s, μ S) * ((∑ S ∈ s, f S) / s.card)
    simp [hs]
  · obtain ⟨S₀, hS₀⟩ := hs
    have hsame : ∀ S ∈ s, μ S = μ S₀ := by
      intro S hS
      apply hμ.eq_of_card_eq
      exact (Finset.mem_powersetCard.mp hS).2.trans
        (Finset.mem_powersetCard.mp hS₀).2.symm
    have hweight : hammingSliceWeight μ k = (s.card : ℝ) * μ S₀ := by
      unfold hammingSliceWeight
      change (∑ S ∈ s, μ S) = _
      rw [Finset.sum_congr rfl hsame]
      simp
    have hsum : (∑ S ∈ s, μ S * f S) = μ S₀ * ∑ S ∈ s, f S := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun S hS => by rw [hsame S hS])
    have hc : (s.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero_of_mem hS₀
    change (∑ S ∈ s, μ S * f S) = _
    rw [hsum, hweight]
    unfold hammingSliceAverage
    change μ S₀ * (∑ S ∈ s, f S) = (s.card : ℝ) * μ S₀ * ((∑ S ∈ s, f S) / s.card)
    field_simp [hc]

/-- Every permutation-invariant Boolean-cube expectation is its explicit
mixture of uniform Hamming-slice expectations. -/
theorem BooleanExchangeable.expectation_mixture {N : ℕ}
    {μ : Finset (Fin N) → ℝ} (hμ : BooleanExchangeable μ)
    (f : Finset (Fin N) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, μ S * f S) =
      ∑ k ∈ Finset.range (N + 1), hammingSliceWeight μ k * hammingSliceAverage f k := by
  rw [booleanCube_sum_by_card]
  exact Finset.sum_congr rfl (fun k _ => hμ.slice_factorization f k)

/-- A common bound on slice expectations bounds every exchangeable Boolean law. -/
theorem BooleanExchangeable.expectation_le_of_slice_bounds {N : ℕ}
    {μ : Finset (Fin N) → ℝ} (hex : BooleanExchangeable μ)
    (hμ : ∀ S, 0 ≤ μ S)
    (hnorm : ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, μ S = 1)
    (f : Finset (Fin N) → ℝ) (B : ℝ)
    (hB : ∀ k ≤ N, hammingSliceAverage f k ≤ B) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, μ S * f S) ≤ B := by
  rw [hex.expectation_mixture]
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), hammingSliceWeight μ k * B := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hB k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))
        (hammingSliceWeight_nonneg μ hμ k)
    _ = B := by rw [← Finset.sum_mul, hammingSliceWeight_sum μ hnorm, one_mul]

/-- Exact finite maximum over the nonempty collection of Hamming slices. -/
theorem BooleanExchangeable.expectation_le_max_slice {N : ℕ}
    {μ : Finset (Fin N) → ℝ} (hex : BooleanExchangeable μ)
    (hμ : ∀ S, 0 ≤ μ S)
    (hnorm : ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, μ S = 1)
    (f : Finset (Fin N) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, μ S * f S) ≤
      (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (hammingSliceAverage f) := by
  apply hex.expectation_le_of_slice_bounds hμ hnorm f
  intro k hk
  exact Finset.le_sup' (f := hammingSliceAverage f) (Finset.mem_range.mpr (by omega))

/-- The genuine sign-vector contrast attached to a Boolean cube point. -/
noncomputable def booleanContrast {N : ℕ} (a : Fin N → ℝ) (S : Finset (Fin N)) : ℝ :=
  ∑ j : Fin N, a j * (if j ∈ S then 1 else -1)

theorem BooleanExchangeable.mgf_le_max_slice {N : ℕ}
    {μ : Finset (Fin N) → ℝ} (hex : BooleanExchangeable μ)
    (hμ : ∀ S, 0 ≤ μ S)
    (hnorm : ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, μ S = 1)
    (a : Fin N → ℝ) (t : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
      μ S * Real.exp (t * booleanContrast a S)) ≤
      (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩
        (hammingSliceAverage (fun S => Real.exp (t * booleanContrast a S))) := by
  exact hex.expectation_le_max_slice hμ hnorm _

/-- The paper's zero-sum two-level vector on a fixed coordinate set. -/
noncomputable def twoLevelVector {N : ℕ} (M : Finset (Fin N)) (t : ℝ) (j : Fin N) : ℝ :=
  if j ∈ M then ((N : ℝ) - M.card) * t / N else -(M.card : ℝ) * t / N

private theorem twoLevelVector_indicator {N : ℕ} (M : Finset (Fin N)) (t : ℝ)
    (hN : 0 < N) (j : Fin N) :
    twoLevelVector M t j = (if j ∈ M then t else 0) - (M.card : ℝ) * t / N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  unfold twoLevelVector
  by_cases hj : j ∈ M
  · rw [if_pos hj, if_pos hj]
    field_simp [hN']
  · rw [if_neg hj, if_neg hj]
    ring

/-- The two-level vector is a genuine centered contrast. -/
theorem twoLevelVector_sum {N : ℕ} (M : Finset (Fin N)) (t : ℝ) (hN : 0 < N) :
    ∑ j : Fin N, twoLevelVector M t j = 0 := by
  simp_rw [twoLevelVector_indicator M t hN]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp [hN']
  ring

/-- Its squared Euclidean norm is the manuscript's exact normalization. -/
theorem twoLevelVector_sq_norm {N : ℕ} (M : Finset (Fin N)) (t : ℝ) (hN : 0 < N) :
    ∑ j : Fin N, (twoLevelVector M t j) ^ 2 =
      (M.card : ℝ) * ((N : ℝ) - M.card) * t ^ 2 / N := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hind (j : Fin N) : (twoLevelVector M t j) ^ 2 =
      (if j ∈ M then t ^ 2 - 2 * (M.card : ℝ) * t ^ 2 / N else 0) +
        ((M.card : ℝ) * t / N) ^ 2 := by
    rw [twoLevelVector_indicator M t hN]
    split_ifs <;> ring
  simp_rw [hind]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Fintype.card_fin]
  field_simp [hN']
  ring

/-- The slice linear statistic is the centered intersection count. -/
theorem twoLevelVector_slice_sum {N : ℕ} (M S : Finset (Fin N)) (t : ℝ) (hN : 0 < N) :
    (∑ j ∈ S, twoLevelVector M t j) =
      t * (((S ∩ M).card : ℝ) - (S.card : ℝ) * M.card / N) := by
  simp_rw [twoLevelVector_indicator M t hN]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
  ring

/-- The actual uniform slice exponential moment of the two-level vector
is the centered hypergeometric MGF, with the usual order of margins. -/
theorem twoLevelVector_slice_mgf {N : ℕ} (M : Finset (Fin N)) (k : ℕ)
    (hk : k ≤ N) (t : ℝ) (hN : 0 < N) :
    hammingSliceAverage (fun S => Real.exp (∑ j ∈ S, twoLevelVector M t j)) k =
      centeredHypergeomMGF N k M.card t := by
  have hM : M.card ≤ N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ M)
  have hrewrite :
      (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        Real.exp (∑ j ∈ S, twoLevelVector M t j)) =
      (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k,
        Real.exp (t * (((S ∩ M).card : ℝ) - (k : ℝ) * M.card / N))) := by
    apply Finset.sum_congr rfl
    intro S hS
    rw [twoLevelVector_slice_sum M S t hN, (Finset.mem_powersetCard.mp hS).2]
  unfold hammingSliceAverage
  rw [hrewrite, uniformSlice_expectation Finset.univ M (Finset.subset_univ M) k
    (fun i => Real.exp (t * ((i : ℝ) - (k : ℝ) * M.card / N)))]
  have hcenter :
      (∑ i ∈ Finset.range (k + 1), hypergeomPMFValue N M.card k i *
        Real.exp (t * ((i : ℝ) - (k : ℝ) * M.card / N))) =
      centeredHypergeomMGF N M.card k t := by
    unfold centeredHypergeomMGF finiteMGF
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    simp only [hypergeomPMFValue, if_pos hik]
    congr 2
    ring
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [hcenter, centeredHypergeomMGF_factor, centeredHypergeomMGF_factor,
    hypergeomMGF_transpose N M.card k hM hk]
  congr 2
  ring

/-- Sign-vector contrasts equal twice their positive-coordinate sum minus
the full coefficient sum. -/
theorem booleanContrast_eq {N : ℕ} (a : Fin N → ℝ) (S : Finset (Fin N)) :
    booleanContrast a S = 2 * (∑ j ∈ S, a j) - ∑ j : Fin N, a j := by
  have hterm (j : Fin N) : a j * (if j ∈ S then 1 else -1) =
      2 * (if j ∈ S then a j else 0) - a j := by
    split_ifs <;> ring
  unfold booleanContrast
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_mem, Finset.univ_inter]

/-- The half-scaled vector is exactly the contrast used for slice sharpness. -/
theorem booleanContrast_twoLevel {N : ℕ} (M S : Finset (Fin N))
    (t : ℝ) (hN : 0 < N) :
    booleanContrast (fun j => twoLevelVector M t j / 2) S =
      t * (((S ∩ M).card : ℝ) - (S.card : ℝ) * M.card / N) := by
  rw [booleanContrast_eq]
  simp only [← Finset.sum_div, twoLevelVector_sum M t hN, zero_div, sub_zero]
  rw [twoLevelVector_slice_sum M S t hN]
  ring

theorem booleanTwoLevel_sq_norm {N : ℕ} (M : Finset (Fin N))
    (t : ℝ) (hN : 0 < N) :
    ∑ j : Fin N, (twoLevelVector M t j / 2) ^ 2 =
      (M.card : ℝ) * ((N : ℝ) - M.card) * t ^ 2 / (4 * N) := by
  simp_rw [div_pow]
  rw [← Finset.sum_div, twoLevelVector_sq_norm M t hN]
  ring

/-- The actual Boolean sign-vector contrast has the centered hypergeometric MGF. -/
theorem booleanTwoLevel_slice_mgf {N : ℕ} (M : Finset (Fin N))
    (k : ℕ) (hk : k ≤ N) (t : ℝ) (hN : 0 < N) :
    hammingSliceAverage
        (fun S => Real.exp (booleanContrast (fun j => twoLevelVector M t j / 2) S)) k =
      centeredHypergeomMGF N k M.card t := by
  have heq (S : Finset (Fin N)) :
      booleanContrast (fun j => twoLevelVector M t j / 2) S =
        ∑ j ∈ S, twoLevelVector M t j := by
    rw [booleanContrast_twoLevel M S t hN, twoLevelVector_slice_sum M S t hN]
  simp_rw [heq]
  exact twoLevelVector_slice_mgf M k hk t hN

/-- The actual uniform probability mass on the Hamming slice of weight `k`. -/
noncomputable def uniformHammingMass (N k : ℕ) (S : Finset (Fin N)) : ℝ :=
  if S.card = k then 1 / (Nat.choose N k : ℝ) else 0

theorem uniformHammingMass_nonneg (N k : ℕ) (S : Finset (Fin N)) :
    0 ≤ uniformHammingMass N k S := by
  unfold uniformHammingMass
  split_ifs <;> positivity

theorem uniformHammingMass_exchangeable (N k : ℕ) :
    BooleanExchangeable (uniformHammingMass N k) := by
  intro S σ
  simp only [uniformHammingMass, Finset.card_map]

theorem uniformHammingMass_expectation (N k : ℕ) (f : Finset (Fin N) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, uniformHammingMass N k S * f S) =
      hammingSliceAverage f k := by
  unfold uniformHammingMass hammingSliceAverage
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [← Finset.powersetCard_eq_filter]
  rw [← Finset.mul_sum]
  simp only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  ring

theorem uniformHammingMass_total (N k : ℕ) (hk : k ≤ N) :
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, uniformHammingMass N k S = 1 := by
  have h := uniformHammingMass_expectation N k (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  unfold hammingSliceAverage
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin]
  apply div_self
  exact_mod_cast Nat.choose_ne_zero hk

/-- The normalized exchangeable Hamming law realizes the centered
hypergeometric exponential moment of the explicit half-scaled contrast. -/
theorem uniformHammingMass_twoLevel_mgf {N : ℕ} (M : Finset (Fin N))
    (k : ℕ) (hk : k ≤ N) (t : ℝ) (hN : 0 < N) :
    (∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
      uniformHammingMass N k S *
        Real.exp (booleanContrast (fun j => twoLevelVector M t j / 2) S)) =
      centeredHypergeomMGF N k M.card t := by
  rw [uniformHammingMass_expectation]
  exact booleanTwoLevel_slice_mgf M k hk t hN

end ExactHoeffding
