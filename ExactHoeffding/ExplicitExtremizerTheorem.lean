import ExactHoeffding.ExplicitSingletonExtremizerLaw

/-! # Complete actual single-coordinate sharpness witness -/

namespace ExactHoeffding
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

/-- Every nontrivial population has the explicit nearest-balanced Hamming
witness, its full Bernoulli marginal law, its contrast identity and norm,
and the appropriate odd contact or even zero-tilt equality mechanism. -/
theorem explicit_single_coordinate_extremizer (N:ℕ) (hN:2≤N) (i:Fin N) :
    let k:=N/2
    let p:ℝ:=(k:ℝ)/N
    let μ:=uniformHammingMeasure N k
    let a:=singleCoordinateContrast i
    IsProbabilityMeasure μ ∧ FiniteExchangeableMeasure μ ∧
      (∀ᵐx ∂μ,x∈realCube N) ∧ (∑j,a j=0) ∧
      (∑j,(a j)^2)=((N:ℝ)-1)/N ∧
      (∀x:Fin N→ℝ,∑j,a j*x j=x i-(∑j,x j)/N) ∧
      μ.map (singleCoordinateBernoulli i)=
        ENNReal.ofReal p • Measure.dirac (1:ℝ)+ENNReal.ofReal (1-p) • Measure.dirac (0:ℝ) ∧
      (∀ᵐx ∂μ,∑j,a j*x j=2*(singleCoordinateBernoulli i x-p)) ∧
      ((¬Even N)→let α:=Real.log (((N:ℝ)+1)/((N:ℝ)-1));
        α≠0 ∧ Real.log (∫x,Real.exp (α*∑j,a j*x j) ∂μ)=
          paritySharpConstant N*α^2*(∑j,(a j)^2)/2) ∧
      ((Even N)→Tendsto (fun z:ℝ =>
        2*Real.log (∫x,Real.exp (z*∑j,a j*x j) ∂μ)/(z^2*(∑j,(a j)^2)))
          (𝓝[≠] (0:ℝ)) (𝓝 (paritySharpConstant N))) := by
  dsimp only
  have hN₀:0<N:=by omega
  have hk:N/2≤N:=Nat.div_le_self N 2
  refine ⟨uniformHammingMeasure_isProbability N (N/2) hk,
    uniformHammingMeasure_exchangeable N (N/2),uniformHammingMeasure_ae_cube N (N/2),
    singleCoordinateContrast_sum hN₀ i,singleCoordinateContrast_sq_norm hN₀ i,
    singleCoordinateContrast_linear i,singleCoordinateBernoulli_law hN₀ (N/2) hk i,
    singleCoordinateContrast_eq_centeredBernoulli_ae hN₀ (N/2) hk i,?_,?_⟩
  · intro hodd
    obtain ⟨n,hn|hn⟩:=Nat.even_or_odd' N
    · subst N
      exact False.elim (hodd ⟨n,by omega⟩)
    · subst N
      have hhalf:(2*n+1)/2=n:=by omega
      rw [hhalf]
      exact singleCoordinate_odd_contact n (by omega) i
  · intro heven
    obtain ⟨q,hq⟩:=even_iff_exists_two_mul.mp heven
    subst N
    have hhalf:(2*q)/2=q:=by omega
    rw [hhalf,paritySharpConstant,if_pos (show Even (2*q) from ⟨q,by omega⟩)]
    exact singleCoordinate_even_quadratic_limit q (by omega) i

end
end ExactHoeffding
