import ExactHoeffding.ExchangeableCenteredEnergy
import ExactHoeffding.CubeCenteredEnergyBounds
import ExactHoeffding.ParityVarianceGap
import Mathlib.Algebra.Order.Floor.Semifield

/-! # The exact variance supremum over actual finite exchangeable laws -/
namespace ExactHoeffding
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Asymptotics
open scoped BigOperators

/-- Every variance ratio realized by an actual exchangeable probability law
on the cube and a nonzero zero-sum contrast. -/
def exchangeableVarianceSet (N:ℕ):Set ℝ :=
  {v|∃μ:Measure (Fin N→ℝ), IsProbabilityMeasure μ ∧ FiniteExchangeableMeasure μ ∧
    (∀ᵐx ∂μ,x∈realCube N) ∧ ∃a:Fin N→ℝ,(∑i,a i)=0 ∧ a≠0 ∧
    v=variance (fun x:Fin N→ℝ=>∑i:Fin N,a i*x i) μ/(∑i:Fin N,(a i)^2)}

def exactExchangeableVarianceConstant (N:ℕ):ℝ:=sSup (exchangeableVarianceSet N)

/-- The nearest-balanced margin product is exactly floor(N²/4). -/
theorem nearestBalanced_product_floor (N:ℕ) :
    ((N/2:ℕ):ℝ)*((N:ℝ)-(N/2:ℕ))=(⌊(N:ℝ)^2/4⌋₊:ℝ) := by
  have hr:N%2=0 ∨ N%2=1:=by omega
  rcases hr with hr | hr
  · have hn:N=2*(N/2):=by omega
    have hnr:(N:ℝ)=2*((N/2:ℕ):ℝ):=by exact_mod_cast hn
    have he:(N:ℝ)^2/4=((N/2:ℕ)^2:ℕ):=by rw [hnr];push_cast;ring
    rw [he,Nat.floor_natCast]
    push_cast
    rw [hnr]
    ring
  · have hn:N=2*(N/2)+1:=by omega
    have hnr:(N:ℝ)=2*((N/2:ℕ):ℝ)+1:=by exact_mod_cast hn
    have he:(N:ℝ)^2/4=(((N/2)*(N/2+1):ℕ):ℝ)+(1/4:ℝ):=by rw [hnr];push_cast;ring
    rw [he,show (((N/2)*(N/2+1):ℕ):ℝ)+(1/4:ℝ)=
      (1/4:ℝ)+(((N/2)*(N/2+1):ℕ):ℝ) by ring,
      Nat.floor_add_natCast (by norm_num : (0:ℝ)≤1/4)]
    have hf:⌊(1/4:ℝ)⌋₊=0:=by norm_num
    rw [hf,zero_add,Nat.cast_mul,Nat.cast_add,Nat.cast_one,hnr]
    ring

/-- The geometric maximum has exactly the stated even/odd variance value. -/
theorem parityVarianceConstant_eq_margin (N:ℕ) (hN:2≤N) :
    parityVarianceConstant N=4*((N/2:ℕ):ℝ)*((N:ℝ)-(N/2:ℕ))/((N:ℝ)*((N:ℝ)-1)) := by
  unfold parityVarianceConstant
  split_ifs with he
  · have hn:N=2*(N/2):=by have hh:=Nat.even_iff.mp he;omega
    have hnr:(N:ℝ)=2*((N/2:ℕ):ℝ):=by exact_mod_cast hn
    have hq:(0:ℝ)<(N/2:ℕ):=by exact_mod_cast (show 0<N/2 by omega)
    rw [hnr]
    field_simp
    ring
  · have hn:N=2*(N/2)+1:=by have hh:=Nat.not_even_iff.mp he;omega
    have hnr:(N:ℝ)=2*((N/2:ℕ):ℝ)+1:=by exact_mod_cast hn
    have hq:(0:ℝ)<(N/2:ℕ):=by exact_mod_cast (show 0<N/2 by omega)
    rw [hnr]
    field_simp
    ring

/-- The universal sharp upper bound for every actual variance. -/
theorem finiteExchangeable_variance_le_parity {N:ℕ} (hN:2≤N)
    (μ:Measure (Fin N→ℝ)) [IsProbabilityMeasure μ]
    (hex:FiniteExchangeableMeasure μ) (hcube:∀ᵐ x ∂μ,x∈realCube N)
    (a:Fin N→ℝ) (ha:∑i,a i=0) :
    variance (fun x:Fin N→ℝ=>∑i:Fin N,a i*x i) μ≤
      parityVarianceConstant N*(∑i:Fin N,(a i)^2) := by
  have hi:Integrable (centeredCubeEnergy (N:=N)) μ:=
    continuous_integrable_cube μ hcube _ (by unfold centeredCubeEnergy;fun_prop)
  have hb:(∫x,centeredCubeEnergy x ∂μ)≤
      4*((N/2:ℕ):ℝ)*((N:ℝ)-(N/2:ℕ))/N := by
    have h:=integral_mono_ae hi (integrable_const _) (hcube.mono fun x hx=>
      centeredCubeEnergy_le (by omega) x hx)
    simpa using h
  rw [finiteExchangeable_contrast_variance_energy hN μ hex hcube a ha]
  have hp:(0:ℝ)<(N:ℝ)-1:=by
    have h:(2:ℝ)≤N:=by exact_mod_cast hN
    linarith
  have hn:(N:ℝ)≠0:=by exact_mod_cast (show N≠0 by omega)
  have hd:=div_le_div_of_nonneg_right hb hp.le
  have heq:(4*((N/2:ℕ):ℝ)*((N:ℝ)-(N/2:ℕ))/(N:ℝ))/((N:ℝ)-1)=
      parityVarianceConstant N := by rw [parityVarianceConstant_eq_margin N hN,div_div]
  rw [heq] at hd
  exact mul_le_mul_of_nonneg_right hd (Finset.sum_nonneg fun _ _=>sq_nonneg _)

/-- Uniform Hamming laws attain their exact finite-population variance for
every zero-sum contrast. -/
theorem uniformHammingMeasure_contrast_variance {N:ℕ} (hN:2≤N) (k:ℕ) (hk:k≤N)
    (a:Fin N→ℝ) (ha:∑i,a i=0) :
    variance (fun x:Fin N→ℝ=>∑i:Fin N,a i*x i) (uniformHammingMeasure N k)=
      (4*(k:ℝ)*((N:ℝ)-k)/((N:ℝ)*((N:ℝ)-1)))*(∑i:Fin N,(a i)^2) := by
  let _:=uniformHammingMeasure_isProbability N k hk
  have he:∀ᵐx ∂uniformHammingMeasure N k,centeredCubeEnergy x=4*(k:ℝ)*((N:ℝ)-k)/N := by
    unfold uniformHammingMeasure
    apply Measure.ae_smul_measure
    rw [ae_finsetSum_measure_iff]
    intro S hS
    rw [ae_dirac_eq]
    simp only [Filter.eventually_pure]
    rw [centeredCubeEnergy_signVertex (show 0<N by omega),
      (Finset.mem_powersetCard.mp hS).2]
  have hi:(∫x,centeredCubeEnergy x ∂uniformHammingMeasure N k)=
      4*(k:ℝ)*((N:ℝ)-k)/N := by
    rw [integral_congr_ae he]
    simp
  rw [finiteExchangeable_contrast_variance_energy hN _
    (uniformHammingMeasure_exchangeable N k) (uniformHammingMeasure_ae_cube N k) a ha]
  change (∫x,centeredCubeEnergy x ∂uniformHammingMeasure N k)/((N:ℝ)-1)*_= _
  rw [hi,div_div]

/-- Every nonzero contrast attains the parity maximum under the nearest-balanced slice. -/
theorem uniformHammingMeasure_nearestBalanced_variance {N:ℕ} (hN:2≤N)
    (a:Fin N→ℝ) (ha:∑i,a i=0) :
    variance (fun x:Fin N→ℝ=>∑i:Fin N,a i*x i) (uniformHammingMeasure N (N/2))=
      parityVarianceConstant N*(∑i:Fin N,(a i)^2) := by
  rw [uniformHammingMeasure_contrast_variance hN (N/2) (by omega) a ha,
    parityVarianceConstant_eq_margin N hN]

/-- A nonzero finite vector has strictly positive squared norm. -/
theorem contrast_sq_norm_pos {N:ℕ} (a:Fin N→ℝ) (ha:a≠0) :0<∑i:Fin N,(a i)^2 := by
  have hn:0≤∑i:Fin N,(a i)^2:=Finset.sum_nonneg fun _ _=>sq_nonneg _
  apply lt_of_le_of_ne hn
  intro hz
  have hzero:∀i:Fin N,a i=0 := by
    have hh:=(Finset.sum_eq_zero_iff_of_nonneg (fun i (_:i∈(Finset.univ:Finset (Fin N)))=>sq_nonneg (a i))).mp hz.symm
    intro i
    exact sq_eq_zero_iff.mp (hh i (Finset.mem_univ i))
  exact ha (funext hzero)

/-- The parity variance value is realized by an actual law and nonzero contrast. -/
theorem parityVarianceConstant_mem_varianceSet (N:ℕ) (hN:2≤N) :
    parityVarianceConstant N∈exchangeableVarianceSet N := by
  classical
  let i₀:Fin N:=⟨0,by omega⟩
  let a:Fin N→ℝ:=twoLevelVector {i₀} 1
  have ha:∑i,a i=0:=twoLevelVector_sum _ _ (by omega)
  have han:a≠0 := by
    intro hz
    have he:=congrFun hz i₀
    have hn:(0:ℝ)<N:=by exact_mod_cast (show 0<N by omega)
    have hN':(1:ℝ)<N:=by exact_mod_cast (show 1<N by omega)
    have hapos:0<a i₀:=by dsimp [a,twoLevelVector];simp only [Finset.card_singleton,Nat.cast_one,mul_one];exact div_pos (by linarith) hn
    simpa using hapos.ne' he
  refine ⟨uniformHammingMeasure N (N/2),uniformHammingMeasure_isProbability _ _ (by omega),
    uniformHammingMeasure_exchangeable _ _,uniformHammingMeasure_ae_cube _ _,a,ha,han,?_⟩
  rw [uniformHammingMeasure_nearestBalanced_variance hN a ha,
    mul_div_cancel_right₀ _ (contrast_sq_norm_pos a han).ne']

/-- The sharp actual exchangeable variance supremum equals the parity value. -/
theorem exactExchangeableVarianceConstant_eq (N:ℕ) (hN:2≤N) :
    exactExchangeableVarianceConstant N=parityVarianceConstant N := by
  have hm:=parityVarianceConstant_mem_varianceSet N hN
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt ⟨_,hm⟩
  · rintro v ⟨μ,hμ,hex,hcube,a,ha,han,rfl⟩
    let _:=hμ
    exact (div_le_iff₀ (contrast_sq_norm_pos a han)).mpr
      (finiteExchangeable_variance_le_parity hN μ hex hcube a ha)
  · intro w hw
    exact ⟨_,hm,hw⟩

/-- The floor formula for the actual variance supremum. -/
theorem exactExchangeableVarianceConstant_floor (N:ℕ) (hN:2≤N) :
    exactExchangeableVarianceConstant N=
      4*(⌊(N:ℝ)^2/4⌋₊:ℝ)/((N:ℝ)*((N:ℝ)-1)) := by
  rw [exactExchangeableVarianceConstant_eq N hN,parityVarianceConstant_eq_margin N hN,
    ←nearestBalanced_product_floor]
  ring

/-- The complete parity proposition for the actual variance supremum and
actual optimal finite-exchangeability coefficient. -/
theorem exact_variance_parity_theorem (N:ℕ) (hN:2≤N) :
    exactExchangeableVarianceConstant N=parityVarianceConstant N ∧
    exactExchangeableVarianceConstant N=4*(⌊(N:ℝ)^2/4⌋₊:ℝ)/((N:ℝ)*((N:ℝ)-1)) ∧
    (Even N→exactExchangeableConstant N=exactExchangeableVarianceConstant N) ∧
    (¬Even N→exactExchangeableVarianceConstant N<exactExchangeableConstant N ∧
      exactExchangeableConstant N<(N:ℝ)/((N:ℝ)-1) ∧
      exactExchangeableConstant N-exactExchangeableVarianceConstant N=
        (2*∫t in (0:ℝ)..(1/(N:ℝ)),t*Real.artanh t)/
          ((1-1/(N:ℝ))*Real.artanh (1/(N:ℝ)))) := by
  refine ⟨exactExchangeableVarianceConstant_eq N hN,
    exactExchangeableVarianceConstant_floor N hN,?_,?_⟩
  · intro he
    rw [exact_finite_exchangeability_constants N hN,
      exactExchangeableVarianceConstant_eq N hN,paritySharpConstant,parityVarianceConstant,
      if_pos he,if_pos he]
  · intro he
    rw [exact_finite_exchangeability_constants N hN,
      exactExchangeableVarianceConstant_eq N hN,paritySharpConstant,parityVarianceConstant,
      if_neg he,if_neg he]
    exact ⟨oddHypergeomConstant_gt_variance N hN,
      oddHypergeomConstant_lt_even_bound N (by omega),
      oddHypergeomConstant_variance_gap_integral N hN⟩

/-- The fourth-order gap expansion refers to the two actual supremum-defined
constants, along every odd sequence tending to infinity. -/
theorem exact_variance_gap_fourth_expansion_along (N J:ℕ→ℕ)
    (hN:Filter.Tendsto N Filter.atTop Filter.atTop)
    (hodd:∀ᶠ n in Filter.atTop,N n=2*J n+1) :
    (fun n=>exactExchangeableConstant (N n)-exactExchangeableVarianceConstant (N n)-
      (2/3:ℝ)*(1/(N n:ℝ))^2-(2/3:ℝ)*(1/(N n:ℝ))^3-
      (26/45:ℝ)*(1/(N n:ℝ))^4)=O[Filter.atTop](fun n=>(1/(N n:ℝ))^5) := by
  apply (odd_variance_gap_fourth_expansion_along N J hN hodd).congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hodd,hN.eventually (Filter.eventually_ge_atTop 2)] with n hn hlarge
  have he:¬Even (N n):=by rw [hn];simp
  rw [exact_finite_exchangeability_constants _ hlarge,
    exactExchangeableVarianceConstant_eq _ hlarge,paritySharpConstant,parityVarianceConstant,
    if_neg he,if_neg he]

end
end ExactHoeffding
