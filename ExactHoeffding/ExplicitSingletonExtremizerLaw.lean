import ExactHoeffding.ExplicitSingletonExtremizer
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Actual Bernoulli marginal and even contact limit of the Hamming extremizer -/

namespace ExactHoeffding
noncomputable section
open MeasureTheory Filter Set
open scoped Topology

def singleCoordinateBernoulli {N:ℕ} (i:Fin N) (x:Fin N→ℝ) : ℝ := (x i+1)/2

theorem singleCoordinateBernoulli_measurable {N:ℕ} (i:Fin N) :
    Measurable (singleCoordinateBernoulli i) := by
  unfold singleCoordinateBernoulli
  fun_prop

theorem singleCoordinateBernoulli_signVertex {N:ℕ} (i:Fin N) (S:Finset (Fin N)) :
    singleCoordinateBernoulli i (signVertex S)=if i∈S then 1 else 0 := by
  unfold singleCoordinateBernoulli signVertex
  split_ifs <;> norm_num

theorem singleCoordinateBernoulli_zero_or_one {N:ℕ} (k:ℕ) (i:Fin N) :
    ∀ᵐx ∂uniformHammingMeasure N k,
      singleCoordinateBernoulli i x=1 ∨ singleCoordinateBernoulli i x=0 := by
  unfold uniformHammingMeasure
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro S hS
  rw [ae_dirac_eq]
  change singleCoordinateBernoulli i (signVertex S)=1 ∨ singleCoordinateBernoulli i (signVertex S)=0
  rw [singleCoordinateBernoulli_signVertex]
  split_ifs <;> simp

/-- The success or failure event has the corresponding actual one-draw
hypergeometric mass, computed by counting subset-intersection fibers. -/
theorem singleCoordinateBernoulli_event_real {N:ℕ} (hN:0<N) (k:ℕ) (hk:k≤N)
    (i:Fin N) (b:ℕ) (hb:b≤1) :
    (uniformHammingMeasure N k).real {x|singleCoordinateBernoulli i x=(b:ℝ)}=
      hypergeomPMFValue N k 1 b := by
  classical
  let s:Set (Fin N→ℝ):={x|singleCoordinateBernoulli i x=(b:ℝ)}
  have hs : MeasurableSet s := (singleCoordinateBernoulli_measurable i) (measurableSet_singleton _)
  rw [← integral_indicator_one hs,uniformHammingMeasure_integral]
  have heq : (fun S:Finset (Fin N) => s.indicator (fun _ => (1:ℝ)) (signVertex S))=
      fun S => if (S∩{i}).card=b then 1 else 0 := by
    funext S
    simp only [indicator_apply,s,mem_setOf_eq,singleCoordinateBernoulli_signVertex]
    by_cases hi:i∈S
    · have hsi : S∩{i}={i} := by ext j; simp only [Finset.mem_inter,Finset.mem_singleton]; aesop
      rw [if_pos hi,hsi,Finset.card_singleton]
      interval_cases b <;> norm_num
    · have hsi : S∩{i}=∅ := by ext j; simp only [Finset.mem_inter,Finset.mem_singleton,Finset.notMem_empty,iff_false]; aesop
      rw [if_neg hi,hsi,Finset.card_empty]
      interval_cases b <;> norm_num
  change hammingSliceAverage (fun S => s.indicator (fun _ => (1:ℝ)) (signVertex S)) k=_
  rw [heq]
  have hc : hammingSliceAverage (fun S:Finset (Fin N) => if (S∩{i}).card=b then 1 else 0) k=
      uniformSliceIntersectionMass Finset.univ {i} k b := by
    unfold hammingSliceAverage uniformSliceIntersectionMass sliceSamples
    rw [Finset.sum_ite]
    simp only [Finset.sum_const,Finset.sum_const_zero,nsmul_eq_mul,mul_one,mul_zero,add_zero]
  rw [hc,fin_uniformSliceIntersectionMass_eq_hypergeomPMF]
  simp only [Finset.card_singleton]
  exact hypergeomPMFValue_transpose N 1 k b (by omega) hk

/-- The coordinate indicator has the actual two-Dirac Bernoulli distribution,
not merely the same moment generating function. -/
theorem singleCoordinateBernoulli_law {N:ℕ} (hN:0<N) (k:ℕ) (hk:k≤N) (i:Fin N) :
    (uniformHammingMeasure N k).map (singleCoordinateBernoulli i)=
      ENNReal.ofReal ((k:ℝ)/N) • Measure.dirac (1:ℝ)+
        ENNReal.ofReal (1-(k:ℝ)/N) • Measure.dirac (0:ℝ) := by
  letI := uniformHammingMeasure_isProbability N k hk
  have h := (Measure.ae_eq_or_eq_iff_map_eq_dirac_add_dirac
    (singleCoordinateBernoulli_measurable i).aemeasurable (by norm_num : (1:ℝ)≠0)).mp
      (singleCoordinateBernoulli_zero_or_one k i)
  rw [h]
  have hevent (b:ℕ) (hb:b≤1) : uniformHammingMeasure N k
      ((singleCoordinateBernoulli i) ⁻¹' {(b:ℝ)})=
        ENNReal.ofReal (hypergeomPMFValue N k 1 b) := by
    rw [← singleCoordinateBernoulli_event_real hN k hk i b hb]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  have he1:=hevent 1 (by omega)
  have he0:=hevent 0 (by omega)
  norm_num only [Nat.cast_one] at he1
  norm_num only [Nat.cast_zero] at he0
  rw [he1,he0]
  simp only [hypergeomPMFValue,if_pos (by omega : 1≤1),if_pos (by omega : 0≤1),
    hypergeomMass_one_success,hypergeomMass_one_failure_complement N k hk hN]

/-- On its actual Hamming probability law the contrast is exactly twice a
centered Bernoulli variable, with parameter k/N. -/
theorem singleCoordinateContrast_eq_centeredBernoulli_ae {N:ℕ} (hN:0<N)
    (k:ℕ) (hk:k≤N) (i:Fin N) :
    ∀ᵐx ∂uniformHammingMeasure N k,
      ∑j,singleCoordinateContrast i j*x j=2*(singleCoordinateBernoulli i x-(k:ℝ)/N) := by
  unfold uniformHammingMeasure
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro S hS
  rw [ae_dirac_eq]
  change ∑j,singleCoordinateContrast i j*signVertex S j=2*(singleCoordinateBernoulli i (signVertex S)-(k:ℝ)/N)
  rw [singleCoordinateContrast_linear]
  have hcard := (Finset.mem_powersetCard.mp hS).2
  have hsum : ∑j,signVertex S j=2*(k:ℝ)-N := by
    simp_rw [signVertex,show ∀j:Fin N,(if j∈S then (1:ℝ) else -1)=
      2*(if j∈S then (1:ℝ) else 0)-1 by intro j; split_ifs <;> norm_num]
    rw [Finset.sum_sub_distrib,← Finset.mul_sum]
    simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,
      Finset.card_univ,Fintype.card_fin,mul_one,hcard]
  rw [hsum]
  unfold singleCoordinateBernoulli
  have hNR:(N:ℝ)≠0 := by exact_mod_cast hN.ne'
  field_simp
  <;> ring

/-- At an even nearest-balanced Hamming law the normalized actual log-MGF
quotient tends to the parity-sharp coefficient as the tilt tends to zero. -/
theorem singleCoordinate_even_quadratic_limit (q:ℕ) (hq:0<q) (i:Fin (2*q)) :
    Tendsto (fun z:ℝ => 2*Real.log (singleCoordinateMGF q i z)/
      (z^2*(∑j,(singleCoordinateContrast i j)^2)))
      (𝓝[≠] (0:ℝ)) (𝓝 (((2*q:ℕ):ℝ)/(((2*q:ℕ):ℝ)-1))) := by
  have hqR : (0:ℝ)<q := by exact_mod_cast hq
  have hp : (q:ℝ)/((2*q:ℕ):ℝ)=1/2 := by push_cast; field_simp
  have ht : Tendsto (fun z:ℝ => 2*z) (𝓝[≠] 0) (𝓝[≠] 0) := by
    have h := (((hasDerivAt_id (0:ℝ)).const_mul (2:ℝ)).tendsto_nhdsNE (by norm_num))
    simpa only [id_eq,mul_zero] using h
  have hlim := (bernoulli_half_quadratic_limit.comp ht).const_mul
    (8*((2*q:ℕ):ℝ)/(((2*q:ℕ):ℝ)-1))
  have hv : (8*((2*q:ℕ):ℝ)/(((2*q:ℕ):ℝ)-1))*((1/4:ℝ)/2)=
      ((2*q:ℕ):ℝ)/(((2*q:ℕ):ℝ)-1) := by ring
  rw [hv] at hlim
  have hN1 : (((2*q:ℕ):ℝ)-1)≠0 := by
    push_cast
    have : (1:ℝ)≤q := by exact_mod_cast hq
    linarith
  have hN0 : (((2*q:ℕ):ℝ))≠0 := by positivity
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp only [Function.comp_apply]
  rw [singleCoordinateMGF_log (by omega) q (by omega),hp,
    singleCoordinateContrast_sq_norm (by omega)]
  field_simp
  <;> ring

end
end ExactHoeffding
