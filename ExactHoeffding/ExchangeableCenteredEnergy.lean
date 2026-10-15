import ExactHoeffding.ExchangeableVarianceMoments

/-! # The actual contrast variance as expected centered population energy -/
namespace ExactHoeffding
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem finiteExchangeable_general_contrast_second {N:ℕ} (hN:2≤N)
    (μ:Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex:FiniteExchangeableMeasure μ) (hcube:∀ᵐ x ∂μ,x∈realCube N)
    (a:Fin N→ℝ) :
    (∫x,(∑i:Fin N,a i*x i)^2 ∂μ)=
      ((∫x,(x ⟨0,by omega⟩)^2 ∂μ)-
        ∫x,x ⟨0,by omega⟩*x ⟨1,by omega⟩ ∂μ)*(∑i:Fin N,(a i)^2)+
      (∫x,x ⟨0,by omega⟩*x ⟨1,by omega⟩ ∂μ)*(∑i:Fin N,a i)^2 := by
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
  rw [exchangeable_quadratic_form]


/-- The centered population energy determines the universal covariance gap. -/
theorem finiteExchangeable_expected_centered_energy {N:ℕ} (hN:2≤N)
    (μ:Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex:FiniteExchangeableMeasure μ) (hcube:∀ᵐ x ∂μ,x∈realCube N) :
    (∫x,∑i:Fin N,(x i-(∑j:Fin N,x j)/(N:ℝ))^2 ∂μ)=
      ((N:ℝ)-1)*((∫x,(x ⟨0,by omega⟩)^2 ∂μ)-
        ∫x,x ⟨0,by omega⟩*x ⟨1,by omega⟩ ∂μ) := by
  have hpoint (x:Fin N→ℝ):(∑i:Fin N,(x i-(∑j:Fin N,x j)/(N:ℝ))^2)=
      (∑i:Fin N,(x i)^2)-(∑i:Fin N,x i)^2/(N:ℝ) := by
    exact centerContrast_sq_norm N (by omega) x
  simp_rw [hpoint]
  have hi:Integrable (fun x:Fin N→ℝ=>∑i:Fin N,(x i)^2) μ:=
    continuous_integrable_cube μ hcube _ (by fun_prop)
  have hj:Integrable (fun x:Fin N→ℝ=>(∑i:Fin N,x i)^2/(N:ℝ)) μ:=
    continuous_integrable_cube μ hcube _ (by fun_prop)
  rw [integral_sub hi hj,integral_finsetSum _ (fun i _=>
    continuous_integrable_cube μ hcube _ (show Continuous (fun x:Fin N→ℝ=>(x i)^2) by fun_prop)),
    integral_div]
  have hs:(∫x,(∑i:Fin N,x i)^2 ∂μ)=
      ((∫x,(x ⟨0,by omega⟩)^2 ∂μ)-∫x,x ⟨0,by omega⟩*x ⟨1,by omega⟩ ∂μ)*(N:ℝ)+
      (∫x,x ⟨0,by omega⟩*x ⟨1,by omega⟩ ∂μ)*(N:ℝ)^2 := by
    simpa using finiteExchangeable_general_contrast_second hN μ hex hcube (fun _=>1)
  rw [hs]
  simp_rw [finiteExchangeable_coordinate_square_eq μ hex _ (⟨0,by omega⟩:Fin N)]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hn:(N:ℝ)≠0:=by exact_mod_cast (show N≠0 by omega)
  field_simp [hn]
  ring

/-- The exact covariance identity for every actual exchangeable cube law. -/
theorem finiteExchangeable_contrast_variance_energy {N:ℕ} (hN:2≤N)
    (μ:Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex:FiniteExchangeableMeasure μ) (hcube:∀ᵐ x ∂μ,x∈realCube N)
    (a:Fin N→ℝ) (ha:∑i,a i=0) :
    variance (fun x:Fin N→ℝ=>∑i:Fin N,a i*x i) μ=
      (∫x,∑i:Fin N,(x i-(∑j:Fin N,x j)/(N:ℝ))^2 ∂μ)/((N:ℝ)-1)*
        (∑i:Fin N,(a i)^2) := by
  rw [finiteExchangeable_contrast_variance hN μ hex hcube a ha,
    finiteExchangeable_expected_centered_energy hN μ hex hcube]
  have hn:(N:ℝ)-1≠0:=by
    have hh:(2:ℝ)≤N:=by exact_mod_cast hN
    linarith
  field_simp [hn]

end
end ExactHoeffding
