import ExactHoeffding.Contrasts

namespace ExactHoeffding

/-- The squared norm of weights projected onto the zero-sum subspace. -/
noncomputable def projectedWeightVariance {N : ℕ} (w : Fin N→ℝ) : ℝ :=
  (∑i,(w i)^2)-(∑i,w i)^2/(N:ℝ)

theorem centerContrast_sum_zero (N : ℕ) (hN : 0<N) (w : Fin N→ℝ) :
    ∑i,centerContrast w i=0 := by
  unfold centerContrast
  rw [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp [hN0]
  ring

theorem centerContrast_sq_norm (N : ℕ) (hN : 0<N) (w : Fin N→ℝ) :
    (∑i,(centerContrast w i)^2)=projectedWeightVariance w := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  have hp (i : Fin N) : (centerContrast w i)^2=
      (w i)^2-2*((∑j,w j)/(N:ℝ))*w i+((∑j,w j)/(N:ℝ))^2 := by
    unfold centerContrast
    ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  unfold projectedWeightVariance
  field_simp [hN0]
  ring

/-- Coefficient centering is identical to subtracting the observed population
mean from every coordinate before applying the original weights. -/
theorem centerContrast_linear_contrast (N : ℕ) (w x : Fin N→ℝ) :
    (∑i,centerContrast w i*x i)=∑i,w i*(x i-(∑j,x j)/(N:ℝ)) := by
  unfold centerContrast
  simp_rw [sub_mul,mul_sub]
  rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_mul]
  ring

theorem projectedWeightVariance_nonnegative (N : ℕ) (hN : 0<N) (w : Fin N→ℝ) :
    0≤projectedWeightVariance w := by
  rw [← centerContrast_sq_norm N hN w]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (centerContrast w i))

theorem projectedWeightVariance_eq_zero_iff (N : ℕ) (hN : 0<N) (w : Fin N→ℝ) :
    projectedWeightVariance w=0 ↔ ∀i, w i=(∑j,w j)/(N:ℝ) := by
  rw [← centerContrast_sq_norm N hN w]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (centerContrast w i))]
  simp only [Finset.mem_univ,true_implies,sq_eq_zero_iff,centerContrast,sub_eq_zero]

end ExactHoeffding
