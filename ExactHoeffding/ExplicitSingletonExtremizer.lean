import ExactHoeffding.HammingMeasure
import ExactHoeffding.ExactParityConstants
import ExactHoeffding.BernoulliOptimal
import ExactHoeffding.ProjectedWeights

/-! # The actual single-coordinate Hamming extremizer -/

namespace ExactHoeffding
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

/-- The explicit zero-sum contrast `e_i-N⁻¹1`. -/
def singleCoordinateContrast {N:ℕ} (i:Fin N) (j:Fin N) : ℝ :=
  (if j=i then 1 else 0)-1/(N:ℝ)

theorem singleCoordinateContrast_eq_twoLevel {N:ℕ} (hN:0<N) (i:Fin N) :
    singleCoordinateContrast i=twoLevelVector {i} 1 := by
  funext j
  have hNR : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  unfold singleCoordinateContrast twoLevelVector
  simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one]
  split_ifs <;> field_simp <;> ring

theorem singleCoordinateContrast_sum {N:ℕ} (hN:0<N) (i:Fin N) :
    ∑j,singleCoordinateContrast i j=0 := by
  rw [singleCoordinateContrast_eq_twoLevel hN i]
  exact twoLevelVector_sum {i} 1 hN

theorem singleCoordinateContrast_sq_norm {N:ℕ} (hN:0<N) (i:Fin N) :
    ∑j,(singleCoordinateContrast i j)^2=((N:ℝ)-1)/N := by
  rw [singleCoordinateContrast_eq_twoLevel hN i,twoLevelVector_sq_norm {i} 1 hN]
  simp

theorem singleCoordinateContrast_linear {N:ℕ} (i:Fin N) (x:Fin N→ℝ) :
    ∑j,singleCoordinateContrast i j*x j=x i-(∑j,x j)/(N:ℝ) := by
  classical
  unfold singleCoordinateContrast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  simp only [ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

/-- The actual exponential moment of the explicit contrast under the uniform
Hamming probability law. -/
def singleCoordinateMGF {N:ℕ} (k:ℕ) (i:Fin N) (z:ℝ) : ℝ :=
  ∫x,Real.exp (z*∑j,singleCoordinateContrast i j*x j) ∂uniformHammingMeasure N k

theorem singleCoordinateMGF_eq_centeredHypergeom {N:ℕ} (hN:0<N)
    (k:ℕ) (hk:k≤N) (i:Fin N) (z:ℝ) :
    singleCoordinateMGF k i z=centeredHypergeomMGF N k 1 (2*z) := by
  have hc (j:Fin N) : twoLevelVector {i} (2*z) j/2=z*singleCoordinateContrast i j := by
    have hNR : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
    unfold twoLevelVector singleCoordinateContrast
    simp only [Finset.mem_singleton,Finset.card_singleton,Nat.cast_one]
    split_ifs <;> field_simp <;> ring
  have h := uniformHammingMeasure_twoLevel_mgf ({i}:Finset (Fin N)) k hk (2*z) hN
  simp only [Finset.card_singleton] at h
  rw [← h]
  unfold singleCoordinateMGF
  apply integral_congr_ae
  filter_upwards [] with x
  congr 1
  simp only [hc,mul_assoc,← Finset.mul_sum]

theorem singleCoordinateMGF_log {N:ℕ} (hN:0<N) (k:ℕ) (hk:k≤N)
    (i:Fin N) (z:ℝ) :
    Real.log (singleCoordinateMGF k i z)=bernoulliCenteredLogMGF ((k:ℝ)/N) (2*z) := by
  rw [singleCoordinateMGF_eq_centeredHypergeom hN k hk i z,
    centeredHypergeomMGF_eq_exp_log N k 1 hk (by omega),Real.log_exp,
    hypergeomCenteredLogMGF_singleton N k hk hN]

/-- The proposed law is an actual exchangeable probability measure on the cube. -/
theorem singleCoordinate_extremizer_law (N k:ℕ) (hk:k≤N) :
    IsProbabilityMeasure (uniformHammingMeasure N k) ∧
      FiniteExchangeableMeasure (uniformHammingMeasure N k) ∧
      (∀ᵐx ∂uniformHammingMeasure N k,x∈realCube N) :=
  ⟨uniformHammingMeasure_isProbability N k hk,
    uniformHammingMeasure_exchangeable N k,uniformHammingMeasure_ae_cube N k⟩

/-- The odd extremizer's contact occurs at the stated nonzero argument. -/
theorem singleCoordinate_odd_contact (n:ℕ) (hn:0<n) (i:Fin (2*n+1)) :
    let N:=2*n+1
    let α:=Real.log (((N:ℝ)+1)/((N:ℝ)-1))
    α≠0 ∧ Real.log (singleCoordinateMGF n i α)=
      paritySharpConstant N*α^2*(∑j,(singleCoordinateContrast i j)^2)/2 := by
  dsimp only
  have hNR : (1:ℝ)<((2*n+1:ℕ):ℝ) := by exact_mod_cast (show 1<2*n+1 by omega)
  have hN0 : (((2*n+1:ℕ):ℝ))≠0 := by linarith
  have hp : (n:ℝ)/((2*n+1:ℕ):ℝ)=
      (((2*n+1:ℕ):ℝ)-1)/(2*((2*n+1:ℕ):ℝ)) := by
    push_cast
    field_simp
    <;> ring
  have hα : 0<Real.log ((((2*n+1:ℕ):ℝ)+1)/(((2*n+1:ℕ):ℝ)-1)) := by
    apply Real.log_pos
    apply (one_lt_div (by linarith)).mpr
    linarith
  refine ⟨hα.ne',?_⟩
  rw [singleCoordinateMGF_log (by omega) n (by omega),singleCoordinateContrast_sq_norm (by omega),hp]
  have hodd : ¬Even (2*n+1) := by
    rintro ⟨r,hr⟩
    omega
  rw [paritySharpConstant,if_neg hodd]
  have h := singleton_odd_quadratic_saturation (((2*n+1:ℕ):ℝ)) hNR
  dsimp only at h
  unfold bernoulliCenteredLogMGF oddHypergeomConstant
  convert h using 1 <;> ring

end
end ExactHoeffding
