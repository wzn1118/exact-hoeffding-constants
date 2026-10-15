import ExactHoeffding.CubeVertexReduction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open MeasureTheory
open scoped BigOperators ENNReal

namespace ExactHoeffding
noncomputable section

/-- The actual uniform measure on the sign vertices with exactly `k` positive
coordinates. The definition is valid for every `N,k`; probability requires `k≤N`. -/
def uniformHammingMeasure (N k : ℕ) : Measure (Fin N→ℝ) :=
  (Nat.choose N k:ℝ≥0∞)⁻¹ •
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard k, Measure.dirac (signVertex S)

theorem uniformHammingMeasure_isProbability (N k : ℕ) (hk : k≤N) :
    IsProbabilityMeasure (uniformHammingMeasure N k) := by
  refine ⟨?_⟩
  unfold uniformHammingMeasure
  rw [Measure.smul_apply,Measure.finsetSum_apply]
  simp only [Measure.dirac_apply_of_mem (Set.mem_univ _),Finset.sum_const,
    nsmul_eq_mul,mul_one,smul_eq_mul,Finset.card_powersetCard,
    Finset.card_univ,Fintype.card_fin]
  apply ENNReal.inv_mul_cancel
  · exact_mod_cast Nat.choose_ne_zero hk
  · exact ENNReal.natCast_ne_top _

/-- Every real-valued function is integrable for this finite-support law. -/
theorem uniformHammingMeasure_integrable (N k : ℕ) (hk : k≤N)
    (f : (Fin N→ℝ)→ℝ) : Integrable f (uniformHammingMeasure N k) := by
  unfold uniformHammingMeasure
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro S hS
    exact integrable_dirac (by simp)
  · apply ENNReal.inv_ne_top.mpr
    exact_mod_cast Nat.choose_ne_zero hk

/-- Integration against the genuine measure equals the finite Hamming-slice average. -/
theorem uniformHammingMeasure_integral (N k : ℕ) (f : (Fin N→ℝ)→ℝ) :
    (∫x,f x ∂uniformHammingMeasure N k)=
      hammingSliceAverage (fun S => f (signVertex S)) k := by
  unfold uniformHammingMeasure
  rw [integral_smul_measure,integral_finsetSum_measure
    (fun S _ => (integrable_dirac (by simp) : Integrable f (Measure.dirac (signVertex S))))]
  simp only [integral_dirac,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  unfold hammingSliceAverage
  simp only [Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]
  ring

theorem uniformHammingMeasure_ae_cube (N k : ℕ) :
    ∀ᵐx ∂uniformHammingMeasure N k,x∈realCube N := by
  unfold uniformHammingMeasure
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro S hS
  rw [ae_dirac_eq]
  exact signVertex_mem_realCube S

theorem signVertex_coordinate_permutation {N : ℕ} (S : Finset (Fin N))
    (σ : Equiv.Perm (Fin N)) :
    MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ (signVertex S)=
      signVertex (S.map σ.toEmbedding) := by
  funext i
  obtain ⟨j,rfl⟩ := σ.surjective i
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  simp only [signVertex,Finset.mem_map_equiv,Equiv.symm_apply_apply]

theorem uniformHammingMeasure_exchangeable (N k : ℕ) :
    ∀σ : Equiv.Perm (Fin N), MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ)
      (uniformHammingMeasure N k) (uniformHammingMeasure N k) := by
  intro σ
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ
  refine ⟨e.measurable,?_⟩
  unfold uniformHammingMeasure
  rw [Measure.map_smul,Measure.map_finset_sum e.measurable.aemeasurable]
  simp_rw [Measure.map_dirac' e.measurable]
  have hvertex (S : Finset (Fin N)) : e (signVertex S)=signVertex (S.map σ.toEmbedding) :=
    signVertex_coordinate_permutation S σ
  simp_rw [hvertex]
  congr 1
  apply Finset.sum_bij (fun S _ => S.map σ.toEmbedding)
  · intro S hS
    apply Finset.mem_powersetCard.mpr
    exact ⟨Finset.subset_univ _,by rw [Finset.card_map]; exact (Finset.mem_powersetCard.mp hS).2⟩
  · intro S hS T hT hST
    exact Finset.map_injective σ.toEmbedding hST
  · intro T hT
    refine ⟨T.map σ.symm.toEmbedding,?_,?_⟩
    · apply Finset.mem_powersetCard.mpr
      exact ⟨Finset.subset_univ _,by rw [Finset.card_map]; exact (Finset.mem_powersetCard.mp hT).2⟩
    · simp [Finset.map_map]
  · intro S hS
    rfl

/-- Actual integration of a sign contrast has the already established finite formula. -/
theorem uniformHammingMeasure_expContrast (N k : ℕ) (a : Fin N→ℝ) (t : ℝ) :
    (∫x,Real.exp (t*∑i : Fin N,a i*x i) ∂uniformHammingMeasure N k)=
      hammingSliceAverage (fun S => Real.exp (t*booleanContrast a S)) k := by
  rw [uniformHammingMeasure_integral]
  rfl

/-- The explicit half-scaled two-level vector realizes the centered hypergeometric MGF
under a genuine exchangeable probability measure. -/
theorem uniformHammingMeasure_twoLevel_mgf {N : ℕ} (M : Finset (Fin N))
    (k : ℕ) (hk : k≤N) (t : ℝ) (hN : 0<N) :
    (∫x,Real.exp (∑j : Fin N,(twoLevelVector M t j/2)*x j)
      ∂uniformHammingMeasure N k)=centeredHypergeomMGF N k M.card t := by
  rw [uniformHammingMeasure_integral]
  exact booleanTwoLevel_slice_mgf M k hk t hN

end
end ExactHoeffding
