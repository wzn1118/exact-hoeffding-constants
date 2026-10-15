import ExactHoeffding.CubeVertexReduction
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi

open MeasureTheory
open scoped BigOperators

namespace ExactHoeffding
noncomputable section

/-- A law on real vectors is finitely exchangeable when every coordinate
permutation preserves the measure. -/
def FiniteExchangeableMeasure {N : ℕ} (μ : Measure (Fin N→ℝ)) : Prop :=
  ∀σ : Equiv.Perm (Fin N), MeasurePreserving
    (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ) μ μ

def expContrast {N : ℕ} (a : Fin N→ℝ) (t : ℝ) (x : Fin N→ℝ) : ℝ :=
  Real.exp (t*∑i,a i*x i)

theorem expContrast_comp_permutation {N : ℕ} (a : Fin N→ℝ) (t : ℝ)
    (σ : Equiv.Perm (Fin N)) :
    expContrast a t ∘ (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ)=
      (fun x : Fin N→ℝ => Real.exp (t*∑i,a i*x (σ.symm i))) := by
  funext x
  unfold expContrast
  simp only [Function.comp_apply]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have he := MeasurableEquiv.piCongrLeft_apply_apply σ (β := fun _ : Fin N => ℝ) x (σ.symm i)
  simpa only [Equiv.apply_symm_apply] using congrArg (fun z : ℝ => a i*z) he

theorem expContrast_continuous {N : ℕ} (a : Fin N→ℝ) (t : ℝ) :
    Continuous (expContrast a t) := by
  apply Real.continuous_exp.comp
  exact continuous_const.mul (continuous_finsetSum Finset.univ
    (fun i _ => continuous_const.mul (continuous_apply i)))

theorem expContrast_bound_on_cube {N : ℕ} (a : Fin N→ℝ) (t : ℝ)
    (x : Fin N→ℝ) (hx : x∈realCube N) :
    ‖expContrast a t x‖≤Real.exp (|t| * ∑i,|a i|) := by
  unfold expContrast
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hsum : |∑i,a i*x i|≤∑i,|a i| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul]
    have hxi : |x i|≤1 := abs_le.mpr (hx i (Set.mem_univ i))
    simpa using mul_le_mul_of_nonneg_left hxi (abs_nonneg (a i))
  exact (le_abs_self (t*∑i,a i*x i)).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hsum (abs_nonneg t))

theorem expContrast_integrable {N : ℕ} (μ : Measure (Fin N→ℝ)) [IsFiniteMeasure μ]
    (hcube : ∀ᵐx ∂μ,x∈realCube N) (a : Fin N→ℝ) (t : ℝ) :
    Integrable (expContrast a t) μ := by
  apply (integrable_const (Real.exp (|t| * ∑i,|a i|))).mono'
    (expContrast_continuous a t).aestronglyMeasurable
  filter_upwards [hcube] with x hx
  exact expContrast_bound_on_cube a t x hx

theorem finiteExchangeable_integral_symmetrized {N : ℕ}
    (μ : Measure (Fin N→ℝ)) [IsFiniteMeasure μ]
    (hex : FiniteExchangeableMeasure μ) (hcube : ∀ᵐx ∂μ,x∈realCube N)
    (a : Fin N→ℝ) (t : ℝ) :
    (∫x,expContrast a t x ∂μ)=∫x,symmetrizedExpContrast a t x ∂μ := by
  have hI := expContrast_integrable μ hcube a t
  have hi (σ : Equiv.Perm (Fin N)) :
      Integrable (fun x : Fin N→ℝ => Real.exp (t*∑i,a i*x (σ.symm i))) μ := by
    have h := (hex σ).integrable_comp_of_integrable hI
    rw [expContrast_comp_permutation a t σ] at h
    exact h
  have he (σ : Equiv.Perm (Fin N)) :
      (∫x : Fin N→ℝ,Real.exp (t*∑i,a i*x (σ.symm i)) ∂μ)=∫x,expContrast a t x ∂μ := by
    have h := (hex σ).integral_comp' (expContrast a t)
    change (∫x,(expContrast a t ∘ (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ) σ)) x ∂μ)=_ at h
    rw [expContrast_comp_permutation a t σ] at h
    exact h
  unfold symmetrizedExpContrast
  rw [integral_div,integral_finsetSum Finset.univ (fun σ _ => hi σ)]
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcard : (Fintype.card (Equiv.Perm (Fin N)):ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hcard]

theorem finiteExchangeable_mgf_le_max_slice {N : ℕ}
    (μ : Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex : FiniteExchangeableMeasure μ) (hcube : ∀ᵐx ∂μ,x∈realCube N)
    (a : Fin N→ℝ) (t : ℝ) :
    (∫x,expContrast a t x ∂μ)≤
      (Finset.range (N+1)).sup' ⟨0,Finset.mem_range.mpr (by omega)⟩
        (hammingSliceAverage (fun S => Real.exp (t*booleanContrast a S))) := by
  rw [finiteExchangeable_integral_symmetrized μ hex hcube a t]
  have hI := expContrast_integrable μ hcube a t
  have hi (σ : Equiv.Perm (Fin N)) :
      Integrable (fun x : Fin N→ℝ => Real.exp (t*∑i,a i*x (σ.symm i))) μ := by
    have h := (hex σ).integrable_comp_of_integrable hI
    rw [expContrast_comp_permutation a t σ] at h
    exact h
  have hsym : Integrable (symmetrizedExpContrast a t) μ :=
    (integrable_finsetSum Finset.univ (fun σ _ => hi σ)).div_const _
  have h := integral_mono_ae hsym (integrable_const _)
    (hcube.mono (fun x hx => symmetrizedExpContrast_le_max_slice a t x hx))
  simpa using h

end
end ExactHoeffding
