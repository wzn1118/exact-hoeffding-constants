import ExactHoeffding.CompactContractionBoundary
import ExactHoeffding.OptimalProxyFourthExpansion
import ExactHoeffding.ExactParityConstants
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The exact odd variance gap and its fourth-order expansion -/
namespace ExactHoeffding
noncomputable section
open Set Filter Asymptotics MeasureTheory
open scoped Topology

/-- The parity variance constant in its finite-population normalization. -/
def parityVarianceConstant (N:ℕ):ℝ :=
  if Even N then (N:ℝ)/((N:ℝ)-1) else ((N:ℝ)+1)/N

/-- The numerator of the odd variance gap is exactly an integrated derivative. -/
theorem odd_variance_gap_numerator_integral (x:ℝ) (hx:0≤x) (hx1:x<1) :
    x-(1-x^2)*Real.artanh x=2*∫ t in (0:ℝ)..x,t*Real.artanh t := by
  let f:ℝ→ℝ:=fun t=>t-(1-t^2)*Real.artanh t
  have hderiv (t:ℝ) (ht:t∈uIcc (0:ℝ) x):HasDerivAt f (2*t*Real.artanh t) t := by
    have ht':t∈Ioo (-1:ℝ) 1 := by
      rw [uIcc_of_le hx] at ht
      exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
    have h := (hasDerivAt_id t).sub
      ((((hasDerivAt_id t).pow 2).const_sub 1).mul (artanh_hasDerivAt_open t ht'))
    have hne:1-t^2≠0 := by nlinarith [ht'.1,ht'.2]
    apply h.congr_deriv
    norm_num only [id_eq,Pi.pow_apply,pow_one,Nat.cast_ofNat,mul_one]
    field_simp [hne]
    ring
  have hint:IntervalIntegrable (fun t:ℝ=>2*t*Real.artanh t) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht':t∈Ioo (-1:ℝ) 1 := by
      rw [uIcc_of_le hx] at ht
      exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
    exact ((continuousAt_const.mul continuousAt_id).mul
      (artanh_hasDerivAt_open t ht').continuousAt).continuousWithinAt
  have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simp only [f,Real.artanh_zero,mul_zero,sub_zero] at hi
  rw [show (fun t:ℝ=>2*t*Real.artanh t)=(fun t=>2*(t*Real.artanh t)) by funext t;ring,
    intervalIntegral.integral_const_mul] at hi
  exact hi.symm

/-- The scalar odd gap is strictly positive throughout its full open domain. -/
theorem odd_variance_gap_scalar_pos (x:ℝ) (hx:0<x) (hx1:x<1) :
    0<x/((1-x)*Real.artanh x)-(1+x) := by
  have ha:0<Real.artanh x:=Real.artanh_pos ⟨hx,hx1⟩
  have hs:0<1-x^2:=by nlinarith
  have h:=artanhContractionFactor_pos x hx hx1
  unfold artanhContractionFactor at h
  have hn:0<x-(1-x^2)*Real.artanh x:=by
    have hh:1<x/((1-x^2)*Real.artanh x):=by linarith
    have hh':(1:ℝ)*((1-x^2)*Real.artanh x)<x:=
      (lt_div_iff₀ (mul_pos hs ha)).mp hh
    linarith
  have hd:0<(1-x)*Real.artanh x:=mul_pos (by linarith) ha
  apply (sub_pos.mpr ((lt_div_iff₀ hd).mpr ?_))
  nlinarith only [hn]

/-- The odd coefficient strictly exceeds the ordinary variance coefficient. -/
theorem oddHypergeomConstant_gt_variance (N:ℕ) (hN:2≤N) :
    ((N:ℝ)+1)/N<oddHypergeomConstant N := by
  have hNR:(2:ℝ)≤N:=by exact_mod_cast hN
  have hn:(0:ℝ)<N:=by linarith
  have hx:0<1/(N:ℝ):=by positivity
  have hx1:1/(N:ℝ)<1:=(div_lt_one hn).mpr (by linarith)
  have h:=odd_variance_gap_scalar_pos (1/(N:ℝ)) hx hx1
  rw [oddHypergeomConstant_eq_artanh N (by omega)]
  have hden:(N:ℝ)-1≠0:=by linarith
  have heq:(1/(N:ℝ))/((1-1/(N:ℝ))*Real.artanh (1/(N:ℝ)))=
      1/(((N:ℝ)-1)*Real.artanh (1/(N:ℝ))) := by
    field_simp [hn.ne']
  have heq2:1+1/(N:ℝ)=((N:ℝ)+1)/N:=by field_simp [hn.ne']
  rw [heq,heq2] at h
  linarith

/-- The complete integral formula for the odd gap. -/
theorem oddHypergeomConstant_variance_gap_integral (N:ℕ) (hN:2≤N) :
    oddHypergeomConstant N-((N:ℝ)+1)/N=
      (2*∫t in (0:ℝ)..(1/(N:ℝ)),t*Real.artanh t)/
        ((1-1/(N:ℝ))*Real.artanh (1/(N:ℝ))) := by
  have hNR:(2:ℝ)≤N:=by exact_mod_cast hN
  have hn:(0:ℝ)<N:=by linarith
  have hx:0<1/(N:ℝ):=by positivity
  have hx1:1/(N:ℝ)<1:=(div_lt_one hn).mpr (by linarith)
  rw [←odd_variance_gap_numerator_integral _ hx.le hx1,
    oddHypergeomConstant_eq_artanh N (by omega)]
  have ha:Real.artanh (1/(N:ℝ))≠0:=(Real.artanh_pos ⟨hx,hx1⟩).ne'
  have hm:(N:ℝ)-1≠0:=by linarith
  have he:1-1/(N:ℝ)≠0:=by linarith
  field_simp [hn.ne',ha,hm,he]
  ring

/-- The exact 26/45 coefficient of the odd variance gap, along every odd
population sequence tending to infinity. -/
theorem odd_variance_gap_fourth_expansion_along (N J:ℕ→ℕ)
    (hN:Tendsto N atTop atTop) (hodd:∀ᶠ n in atTop,N n=2*J n+1) :
    (fun n=>oddHypergeomConstant (N n)-((N n:ℝ)+1)/(N n:ℝ)-
      (2/3:ℝ)*(1/(N n:ℝ))^2-(2/3:ℝ)*(1/(N n:ℝ))^3-
      (26/45:ℝ)*(1/(N n:ℝ))^4)=O[atTop](fun n=>(1/(N n:ℝ))^5) := by
  have hv:∀ᶠ n in atTop,J n≤N n ∧ 1≤N n ∧ 2*(J n:ℝ)+1=(N n:ℝ) := by
    filter_upwards [hodd] with n hn
    refine ⟨by omega,by omega,?_⟩
    rw [hn]
    push_cast
    ring
  have h:=normalizedHypergeomProxy_fourth_expansion_along 1 (by omega) 1 (by norm_num)
    N J hN hv
  apply h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hodd,hN.eventually (eventually_ge_atTop 3)] with n hn hlarge
  have hj:0<J n:=by omega
  have heq:normalizedHypergeomProxy (N n) (J n) 1=oddHypergeomConstant (N n) := by
    rw [hn]
    exact (odd_normalized_proxy_all_equality (J n) (J n) 1 hj hj (by omega)
      (by omega) (by omega)).mpr ⟨Or.inl rfl,Or.inl rfl⟩
  rw [heq]
  have hn0:(N n:ℝ)≠0:=by exact_mod_cast (show N n≠0 by omega)
  field_simp [hn0]
  ring

end
end ExactHoeffding
