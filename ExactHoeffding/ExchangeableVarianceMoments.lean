import ExactHoeffding.HammingMeasure
import ExactHoeffding.MeasureExchangeability
import ExactHoeffding.ProjectedWeights
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Logic.Equiv.Fintype

/-! # Actual first and second moments of exchangeable cube laws -/
namespace ExactHoeffding
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Every continuous function is integrable under a finite law supported on the cube. -/
theorem continuous_integrable_cube {N:ℕ} (μ:Measure (Fin N→ℝ)) [IsFiniteMeasure μ]
    (hcube:∀ᵐ x ∂μ,x∈realCube N) (f:(Fin N→ℝ)→ℝ) (hf:Continuous f):
    Integrable f μ := by
  have hcomp:IsCompact (realCube N):=isCompact_univ_pi (fun _=>isCompact_Icc)
  have hi:=hf.continuousOn.integrableOn_compact hcomp (μ:=μ)
  rwa [IntegrableOn,Measure.restrict_eq_self_of_ae_mem hcube] at hi

/-- Coordinate means are equal for an actual exchangeable measure. -/
theorem finiteExchangeable_coordinate_mean_eq {N:ℕ} (μ:Measure (Fin N→ℝ))
    (hex:FiniteExchangeableMeasure μ) (i j:Fin N) :
    (∫x,x i ∂μ)=∫x,x j ∂μ := by
  have h:=(hex (Equiv.swap i j)).integral_comp' (fun x:Fin N→ℝ=>x i)
  have he:(fun x:Fin N→ℝ=>(MeasurableEquiv.piCongrLeft (fun _:Fin N=>ℝ)
      (Equiv.swap i j) x) i)=(fun x=>x j) := by
    funext x
    have hh:=MeasurableEquiv.piCongrLeft_apply_apply (Equiv.swap i j)
      (β:=fun _:Fin N=>ℝ) x j
    simpa only [Equiv.swap_apply_right] using hh
  rw [he] at h
  exact h.symm

/-- Joint second moments are preserved by every prescribed coordinate permutation. -/
theorem finiteExchangeable_coordinate_product_perm {N:ℕ} (μ:Measure (Fin N→ℝ))
    (hex:FiniteExchangeableMeasure μ) (σ:Equiv.Perm (Fin N)) (i j:Fin N) :
    (∫x,x (σ i)*x (σ j) ∂μ)=∫x,x i*x j ∂μ := by
  have h:=(hex σ).integral_comp' (fun x:Fin N→ℝ=>x (σ i)*x (σ j))
  have he:(fun x:Fin N→ℝ=>
      (MeasurableEquiv.piCongrLeft (fun _:Fin N=>ℝ) σ x) (σ i)*
      (MeasurableEquiv.piCongrLeft (fun _:Fin N=>ℝ) σ x) (σ j))=
      (fun x=>x i*x j) := by
    funext x
    rw [MeasurableEquiv.piCongrLeft_apply_apply,MeasurableEquiv.piCongrLeft_apply_apply]
  rw [he] at h
  exact h.symm

/-- Every off-diagonal second moment agrees with every other one. -/
theorem finiteExchangeable_coordinate_product_eq {N:ℕ} (μ:Measure (Fin N→ℝ))
    (hex:FiniteExchangeableMeasure μ) (i j k l:Fin N) (hij:i≠j) (hkl:k≠l) :
    (∫x,x i*x j ∂μ)=∫x,x k*x l ∂μ := by
  let f:Fin 2→Fin N:=fun b=>if b=0 then i else j
  let g:Fin 2→Fin N:=fun b=>if b=0 then k else l
  have hf:Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have hg:Function.Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [g]
  obtain ⟨σ,hσ⟩:=Equiv.Perm.exists_extending_pair f g hf hg
  have hi:σ i=k:=by simpa [f,g] using hσ 0
  have hj:σ j=l:=by simpa [f,g] using hσ 1
  have h:=finiteExchangeable_coordinate_product_perm μ hex σ i j
  rw [hi,hj] at h
  exact h.symm

/-- Every diagonal second moment agrees with every other one. -/
theorem finiteExchangeable_coordinate_square_eq {N:ℕ} (μ:Measure (Fin N→ℝ))
    (hex:FiniteExchangeableMeasure μ) (i j:Fin N) :
    (∫x,(x i)^2 ∂μ)=∫x,(x j)^2 ∂μ := by
  have h:=finiteExchangeable_coordinate_product_perm μ hex (Equiv.swap i j) i i
  simpa only [Equiv.swap_apply_left,←pow_two] using h.symm

/-- Exact algebra for the exchangeable second-moment matrix. -/
theorem exchangeable_quadratic_form {N:ℕ} (a:Fin N→ℝ) (A B:ℝ) :
    (∑i:Fin N,∑j:Fin N,a i*a j*(if i=j then A else B))=
      (A-B)*(∑i:Fin N,(a i)^2)+B*(∑i:Fin N,a i)^2 := by
  classical
  have he (i j:Fin N):a i*a j*(if i=j then A else B)=
      B*(a i*a j)+(if j=i then (A-B)*(a i)^2 else 0) := by
    by_cases h:i=j
    · subst j;simp;ring
    · simp [h,Ne.symm h];ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [←Finset.mul_sum,←Finset.sum_mul]
  ring

/-- First moments of any centered contrast vanish. -/
theorem finiteExchangeable_contrast_mean_zero {N:ℕ} (hN:0<N)
    (μ:Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex:FiniteExchangeableMeasure μ) (hcube:∀ᵐ x ∂μ,x∈realCube N)
    (a:Fin N→ℝ) (ha:∑i,a i=0) :
    (∫x,∑i:Fin N,a i*x i ∂μ)=0 := by
  let i₀:Fin N:=⟨0,hN⟩
  have hi (i:Fin N):Integrable (fun x:Fin N→ℝ=>a i*x i) μ :=
    continuous_integrable_cube μ hcube _ (by fun_prop)
  rw [integral_finsetSum _ (fun i _=>hi i)]
  simp_rw [integral_const_mul,finiteExchangeable_coordinate_mean_eq μ hex _ i₀]
  rw [←Finset.sum_mul,ha,zero_mul]

/-- The actual second moment of every zero-sum contrast is determined by
one diagonal and one off-diagonal moment. -/
theorem finiteExchangeable_contrast_second {N:ℕ} (hN:2≤N)
    (μ:Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex:FiniteExchangeableMeasure μ) (hcube:∀ᵐ x ∂μ,x∈realCube N)
    (a:Fin N→ℝ) (ha:∑i,a i=0) :
    (∫x,(∑i:Fin N,a i*x i)^2 ∂μ)=
      ((∫x,(x ⟨0,by omega⟩)^2 ∂μ)-
        ∫x,x ⟨0,by omega⟩*x ⟨1,by omega⟩ ∂μ)*(∑i:Fin N,(a i)^2) := by
  classical
  let i₀:Fin N:=⟨0,by omega⟩
  let i₁:Fin N:=⟨1,by omega⟩
  have hprod (i j:Fin N):Integrable (fun x:Fin N→ℝ=>(a i*a j)*(x i*x j)) μ:=
    continuous_integrable_cube μ hcube _ (by fun_prop)
  have he (x:Fin N→ℝ):(∑i:Fin N,a i*x i)^2=
      ∑i:Fin N,∑j:Fin N,(a i*a j)*(x i*x j) := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ (fun j _=>hprod i j))]
  simp_rw [integral_finsetSum _ (fun j _=>hprod _ j),integral_const_mul]
  have hm (i j:Fin N):(∫x,x i*x j ∂μ)=
      if i=j then (∫x,(x i₀)^2 ∂μ) else (∫x,x i₀*x i₁ ∂μ) := by
    by_cases hij:i=j
    · subst j
      simp only [ite_true,←pow_two]
      exact finiteExchangeable_coordinate_square_eq μ hex i i₀
    · rw [if_neg hij]
      exact finiteExchangeable_coordinate_product_eq μ hex i j i₀ i₁ hij (by intro he; have hh:=congrArg Fin.val he; simp [i₀,i₁] at hh)
  have hmain : (∑i:Fin N,∑j:Fin N,a i*a j*(∫x,x i*x j ∂μ))=
      ∑i:Fin N,∑j:Fin N,a i*a j*(if i=j then (∫x,(x i₀)^2 ∂μ) else ∫x,x i₀*x i₁ ∂μ) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hm i j]
  rw [hmain]
  rw [exchangeable_quadratic_form,ha,zero_pow (by omega),mul_zero,add_zero]

/-- The usual variance equals the second moment for a zero-sum contrast. -/
theorem finiteExchangeable_contrast_variance {N:ℕ} (hN:2≤N)
    (μ:Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex:FiniteExchangeableMeasure μ) (hcube:∀ᵐ x ∂μ,x∈realCube N)
    (a:Fin N→ℝ) (ha:∑i,a i=0) :
    variance (fun x:Fin N→ℝ=>∑i:Fin N,a i*x i) μ=
      ((∫x,(x ⟨0,by omega⟩)^2 ∂μ)-
        ∫x,x ⟨0,by omega⟩*x ⟨1,by omega⟩ ∂μ)*(∑i:Fin N,(a i)^2) := by
  have hc:Continuous (fun x:Fin N→ℝ=>∑i:Fin N,a i*x i):=by fun_prop
  rw [variance_eq_integral hc.measurable.aemeasurable,
    finiteExchangeable_contrast_mean_zero (by omega) μ hex hcube a ha]
  simp only [sub_zero]
  exact finiteExchangeable_contrast_second hN μ hex hcube a ha

end
end ExactHoeffding
