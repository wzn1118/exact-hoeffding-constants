import ExactHoeffding.CubeVertexReduction
import ExactHoeffding.ProjectedWeights

/-! # Sharp centered-energy bound on the real cube -/
namespace ExactHoeffding
noncomputable section
open Set
open scoped BigOperators

/-- The actual sum of squared deviations from the coordinate mean. -/
def centeredCubeEnergy {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  ∑ i, (x i - (∑ j, x j) / (N : ℝ)) ^ 2

theorem centeredCubeEnergy_eq {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ) :
    centeredCubeEnergy x = (∑ i, (x i)^2) - (∑ i, x i)^2 / (N:ℝ) := by
  exact centerContrast_sq_norm N hN x

theorem centeredCubeEnergy_signVertex {N : ℕ} (hN : 0 < N)
    (S : Finset (Fin N)) :
    centeredCubeEnergy (signVertex S) = 4 * (S.card:ℝ) * ((N:ℝ)-S.card) / N := by
  classical
  have hs : (∑ i : Fin N, signVertex S i) = 2*(S.card:ℝ)-(N:ℝ) := by
    have he (i : Fin N) : signVertex S i = (if i∈S then (2:ℝ) else 0)-1 := by
      simp only [signVertex]; split_ifs <;> norm_num
    simp_rw [he]
    simp [Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.sum_const]
    ring
  have hq : (∑ i : Fin N, (signVertex S i)^2) = (N:ℝ) := by
    have he (i : Fin N) : (signVertex S i)^2 = 1 := by
      simp only [signVertex]; split_ifs <;> norm_num
    simp_rw [he]
    simp
  rw [centeredCubeEnergy_eq hN,hs,hq]
  have hn : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  field_simp [hn]
  ring

/-- A squared linear deviation is convex, hence so is their finite sum. -/
theorem centeredCubeEnergy_convex (N : ℕ) :
    ConvexOn ℝ (realCube N) (centeredCubeEnergy (N:=N)) := by
  refine ⟨convex_pi (fun _ _ => convex_Icc _ _), ?_⟩
  intro x hx y hy a b ha hb hab
  have hs : (∑ j : Fin N, (a • x + b • y) j) =
      a*(∑ j,x j)+b*(∑ j,y j) := by
    simp [Pi.add_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_add_distrib,←Finset.mul_sum]
  have hd (i : Fin N) :
      (a • x + b • y) i - (∑ j, (a • x + b • y) j)/(N:ℝ) =
      a*(x i-(∑ j,x j)/(N:ℝ))+b*(y i-(∑ j,y j)/(N:ℝ)) := by
    rw [hs]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  simp only [centeredCubeEnergy,smul_eq_mul]
  rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  rw [hd i]
  have hpos := mul_nonneg (mul_nonneg ha hb)
    (sq_nonneg ((x i-(∑ j,x j)/(N:ℝ))-(y i-(∑ j,y j)/(N:ℝ))))
  nlinarith [sq_nonneg (x i-(∑ j,x j)/(N:ℝ)),sq_nonneg (y i-(∑ j,y j)/(N:ℝ))]

/-- An integer success margin is maximized at the two nearest-balanced counts. -/
theorem integer_margin_product_le (N k : ℕ) :
    (k:ℝ)*((N:ℝ)-k) ≤ (N/2:ℕ)*((N:ℝ)-(N/2:ℕ)) := by
  have hn : N = 2*(N/2)+N%2 := by omega
  have hr : N%2=0 ∨ N%2=1 := by omega
  rcases hr with hr | hr
  · have he : (N:ℝ)=2*(N/2:ℕ) := by exact_mod_cast (by omega : N=2*(N/2))
    rw [he]
    nlinarith [sq_nonneg ((k:ℝ)-(N/2:ℕ))]
  · have he : (N:ℝ)=2*(N/2:ℕ)+1 := by exact_mod_cast (by omega : N=2*(N/2)+1)
    have hh : k≤N/2 ∨ N/2+1≤k := by omega
    rw [he]
    rcases hh with hh | hh
    · have h : (k:ℝ)≤(N/2:ℕ) := by exact_mod_cast hh
      nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0≤(N/2:ℕ)+1-(k:ℝ) by linarith)]
    · have h : (N/2:ℕ)+1≤(k:ℝ) := by exact_mod_cast hh
      nlinarith [mul_nonneg (show 0≤(k:ℝ)-(N/2:ℕ) by linarith) (sub_nonneg.mpr h)]

/-- The sharp pointwise cube bound, including the odd lattice correction. -/
theorem centeredCubeEnergy_le {N : ℕ} (hN : 0 < N) (x : Fin N → ℝ)
    (hx : x∈realCube N) :
    centeredCubeEnergy x ≤ 4*(N/2:ℕ)*((N:ℝ)-(N/2:ℕ))/N := by
  obtain ⟨S,hS⟩ := convexOn_realCube_le_vertex _ (centeredCubeEnergy_convex N) x hx
  apply hS.trans
  rw [centeredCubeEnergy_signVertex hN]
  exact div_le_div_of_nonneg_right
    (by nlinarith [integer_margin_product_le N S.card]) (by positivity)

end
end ExactHoeffding
