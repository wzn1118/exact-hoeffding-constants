import ExactHoeffding.TiltedVariance
import ExactHoeffding.StationaryCertificates
import ExactHoeffding.Sampling
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Curvature of one- and two-draw hypergeometric laws

The statements concern the second derivative of the logarithm of the actual
finite hypergeometric moment-generating function.
-/

namespace ExactHoeffding

/-- One draw has tilted variance at most one quarter, at every real tilt. -/
theorem hypergeom_one_draw_curvature_le (N k : ℕ)
    (hk : k ≤ N) (hN : 0 < N) (t : ℝ) :
    deriv (deriv (fun u => Real.log (hypergeomMGF N k 1 u))) t ≤ 1 / 4 := by
  rw [hypergeomLogMGF_second_deriv N k 1 hk (by omega) t]
  have hpos : 0 < hypergeomMGF N k 1 t :=
    finiteMGF_pos_of_normalized _ _ _
      (fun i _ => hypergeomMass_nonneg N k 1 i)
      (hypergeomMass_total N k 1 hk (by omega)) t
  have hfirst : finiteTiltFirst (Finset.range (1 + 1))
      (hypergeomMass N k 1) (fun i => (i : ℝ)) t =
      hypergeomMass N k 1 1 * Real.exp t := by
    simp [finiteTiltFirst, Finset.sum_range_succ]
  have hsecond : finiteTiltSecond (Finset.range (1 + 1))
      (hypergeomMass N k 1) (fun i => (i : ℝ)) t =
      hypergeomMass N k 1 1 * Real.exp t := by
    simp [finiteTiltSecond, Finset.sum_range_succ]
  rw [hfirst, hsecond]
  apply (div_le_iff₀ (sq_pos_of_pos hpos)).mpr
  nlinarith [sq_nonneg (hypergeomMass N k 1 1 * Real.exp t -
    hypergeomMGF N k 1 t / 2)]

/-- Balanced one-draw sampling attains the curvature bound at zero tilt. -/
theorem hypergeom_one_draw_curvature_balanced (k : ℕ) (hk : 0<k) :
    deriv (deriv (fun u => Real.log (hypergeomMGF (2*k) k 1 u))) 0 = 1/4 := by
  have hkm : k≤2*k := by omega
  have hN : 1≤2*k := by omega
  have hk0 : (k:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [hypergeomLogMGF_second_deriv (2*k) k 1 hkm hN 0,
    hypergeomMGF_zero (2*k) k 1 hkm hN]
  simp [finiteTiltFirst, finiteTiltSecond, Finset.sum_range_succ,
    hypergeomMass_one_success]
  field_simp
  ring

/-- Rational variance of weights `a`, `2*b*z`, and `c*z^2` at `0,1,2`. -/
noncomputable def threePointVariance (a b c z : ℝ) : ℝ :=
  ((2*b*z+4*c*z^2)*(a+2*b*z+c*z^2)-(2*b*z+2*c*z^2)^2) /
    (a+2*b*z+c*z^2)^2

/-- Exact identification with the symmetric three-mass variance expression. -/
theorem threePointVariance_normal_form (a b c z h : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hz : 0<z)
    (hh : 0<h) (hsq : h^2=a*c) :
    threePointVariance a b c z =
      ((b/h)*((a+c*z^2)/(2*h*z))+1) /
        ((b/h)+(a+c*z^2)/(2*h*z))^2 := by
  have hden : a+2*b*z+c*z^2≠0 := ne_of_gt (by positivity)
  have hsum : b/h+(a+c*z^2)/(2*h*z)≠0 := ne_of_gt (by positivity)
  unfold threePointVariance
  field_simp [ne_of_gt hh, ne_of_gt hz, hden, hsum]
  rw [hsq]
  ring

/-- A positive three-mass quadratic has a sharp symmetric-tilt envelope. -/
theorem threePointVariance_sqrt_envelope (a b c z : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hz : 0<z)
    (hshape : b^2≤4*(a*c)) :
    threePointVariance a b c z ≤ 1/(1+b/Real.sqrt (a*c)) := by
  let h := Real.sqrt (a*c)
  have hh : 0<h := Real.sqrt_pos.mpr (mul_pos ha hc)
  have hsq : h^2=a*c := Real.sq_sqrt (le_of_lt (mul_pos ha hc))
  have hr : 0<b/h := div_pos hb hh
  have hr2 : b/h≤2 := by
    apply (div_le_iff₀ hh).mpr
    nlinarith [hsq]
  have hq : 1≤(a+c*z^2)/(2*h*z) := by
    apply (le_div_iff₀ (by positivity : 0<2*h*z)).mpr
    have hid : (a+c*z^2)^2-(2*h*z)^2=(a-c*z^2)^2 := by
      linear_combination -4*z^2*hsq
    have hp : 0<a+c*z^2 := by positivity
    nlinarith [sq_nonneg (a-c*z^2)]
  rw [threePointVariance_normal_form a b c z h ha hb hc hz hh hsq]
  exact two_mark_variance_envelope (b/h) ((a+c*z^2)/(2*h*z)) hr hr2 hq

/-- Relating the three-mass envelope to the finite-population coefficient. -/
theorem threePointVariance_finite_population_bound (N a b c z : ℝ)
    (hN : 2<N) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hz : 0<z)
    (hshape : b^2≤4*(a*c))
    (hbalance : N^2*(a*c)≤b^2*(N-2)^2) :
    threePointVariance a b c z ≤ (N-2)/(2*(N-1)) := by
  have hh : 0<Real.sqrt (a*c) := Real.sqrt_pos.mpr (mul_pos ha hc)
  have hsq := Real.sq_sqrt (le_of_lt (mul_pos ha hc))
  have hN0 : 0<N := by linarith
  have hN1 : 0<N-1 := by linarith
  have hN2 : 0<N-2 := by linarith
  have hlower : N*Real.sqrt (a*c)≤b*(N-2) := by
    have hscaled := congrArg (fun x : ℝ => N^2*x) hsq
    nlinarith [hscaled, mul_pos hb hN2, mul_pos hN0 hh]
  apply le_trans (threePointVariance_sqrt_envelope a b c z ha hb hc hz hshape)
  apply (div_le_div_iff₀ (by positivity : 0<1+b/Real.sqrt (a*c))
    (by positivity : 0<2*(N-1))).mpr
  have hid : (1+b/Real.sqrt (a*c))*Real.sqrt (a*c)=Real.sqrt (a*c)+b := by
    field_simp
  have hgoal : 2*(N-1)*Real.sqrt (a*c)≤
      (N-2)*(1+b/Real.sqrt (a*c))*Real.sqrt (a*c) := by
    nlinarith [hid]
  exact (mul_le_mul_iff_left₀ hh).mp (by nlinarith [hgoal])

theorem hypergeomMass_two_zero (N k : ℕ) (hk : k≤N) :
    hypergeomMass N k 2 0 =
      ((N:ℝ)-k)*((N:ℝ)-k-1)/((N:ℝ)*((N:ℝ)-1)) := by
  simp only [hypergeomMass, hypergeomCount, Nat.choose_zero_right, one_mul,
    Nat.sub_zero, Nat.cast_choose_two, Nat.cast_sub hk]
  simp only [div_div_div_cancel_right₀ (by norm_num : (2:ℝ)≠0)]

theorem hypergeomMass_two_one (N k : ℕ) (hk : k≤N) :
    hypergeomMass N k 2 1 =
      2*(k:ℝ)*((N:ℝ)-k)/((N:ℝ)*((N:ℝ)-1)) := by
  simp only [hypergeomMass, hypergeomCount, show 2-1=1 by omega,
    Nat.choose_one_right, Nat.cast_mul, Nat.cast_sub hk, Nat.cast_choose_two]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem hypergeomMass_two_two (N k : ℕ) :
    hypergeomMass N k 2 2 =
      (k:ℝ)*((k:ℝ)-1)/((N:ℝ)*((N:ℝ)-1)) := by
  simp only [hypergeomMass, hypergeomCount, Nat.sub_self, Nat.choose_zero_right,
    mul_one, Nat.cast_choose_two]
  simp only [div_div_div_cancel_right₀ (by norm_num : (2:ℝ)≠0)]

/-- The curvature of the actual two-draw law is the rational three-mass formula. -/
theorem hypergeom_two_draw_curvature_formula (N k : ℕ)
    (hk : k≤N) (hN : 2≤N) (t : ℝ) :
    deriv (deriv (fun u => Real.log (hypergeomMGF N k 2 u))) t =
      threePointVariance
        (((N:ℝ)-k)*((N:ℝ)-k-1))
        ((k:ℝ)*((N:ℝ)-k)) ((k:ℝ)*((k:ℝ)-1)) (Real.exp t) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hN1 : (N:ℝ)-1≠0 := by
    have : (2:ℝ)≤N := by exact_mod_cast hN
    linarith
  rw [hypergeomLogMGF_second_deriv N k 2 hk hN t]
  simp only [finiteTiltFirst, finiteTiltSecond, hypergeomMGF, finiteMGF,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, mul_one,
    zero_pow, one_pow, Real.exp_zero, zero_mul, zero_add, one_mul, add_zero]
  rw [hypergeomMass_two_zero N k hk, hypergeomMass_two_one N k hk,
    hypergeomMass_two_two N k]
  rw [show t*2=t+t by ring, Real.exp_add]
  unfold threePointVariance
  field_simp

/-- Two draws satisfy the all-tilt sharp finite-population curvature bound. -/
theorem hypergeom_two_draw_curvature_le (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) (t : ℝ) :
    deriv (deriv (fun u => Real.log (hypergeomMGF N k 2 u))) t ≤
      ((N:ℝ)-2)/(2*((N:ℝ)-1)) := by
  have hkle : k≤N := by omega
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hNkR : (k:ℝ)+2≤N := by exact_mod_cast hNk
  have ha : 0<((N:ℝ)-k)*((N:ℝ)-k-1) := by
    apply mul_pos <;> linarith
  have hb : 0<(k:ℝ)*((N:ℝ)-k) := by
    apply mul_pos <;> linarith
  have hc : 0<(k:ℝ)*((k:ℝ)-1) := by
    apply mul_pos <;> linarith
  have hlow : 0≤4*((k:ℝ)-1)*((N:ℝ)-k-1)-(k:ℝ)*((N:ℝ)-k) := by
    have hprod : 0≤((k:ℝ)-2)*((N:ℝ)-k-2) := by
      apply mul_nonneg <;> linarith
    nlinarith
  have hshape : ((k:ℝ)*((N:ℝ)-k))^2≤
      4*(((N:ℝ)-k)*((N:ℝ)-k-1)*((k:ℝ)*((k:ℝ)-1))) := by
    have hmul := mul_nonneg (le_of_lt hb) hlow
    nlinarith only [hmul]
  have hbalance : (N:ℝ)^2*
      (((N:ℝ)-k)*((N:ℝ)-k-1)*((k:ℝ)*((k:ℝ)-1)))≤
      ((k:ℝ)*((N:ℝ)-k))^2*((N:ℝ)-2)^2 := by
    have hp : 0≤(k:ℝ)*((N:ℝ)-k)*((N:ℝ)-1)*((N:ℝ)-2*k)^2 := by
      apply mul_nonneg
      · apply mul_nonneg (le_of_lt hb); linarith
      · positivity
    nlinarith only [hp]
  rw [hypergeom_two_draw_curvature_formula N k hkle (by omega) t]
  exact threePointVariance_finite_population_bound (N:ℝ) _ _ _ _
    (by linarith) ha hb hc (Real.exp_pos t) hshape hbalance

/-- Balanced two-draw sampling attains the finite-population coefficient. -/
theorem hypergeom_two_draw_curvature_balanced (k : ℕ) (hk : 2≤k) :
    deriv (deriv (fun u => Real.log (hypergeomMGF (2*k) k 2 u))) 0 =
      (((2*k:ℕ):ℝ)-2)/(2*(((2*k:ℕ):ℝ)-1)) := by
  have hkm : k≤2*k := by omega
  have hN : 2≤2*k := by omega
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  rw [hypergeom_two_draw_curvature_formula (2*k) k hkm hN 0]
  simp only [Real.exp_zero, Nat.cast_mul, Nat.cast_ofNat]
  have hk0 : (k:ℝ)≠0 := by linarith
  have h2k : 2*(k:ℝ)-1≠0 := by linarith
  have hden : (2*(k:ℝ)-k)*(2*(k:ℝ)-k-1)+
      2*(k:ℝ)*(2*(k:ℝ)-k)+(k:ℝ)*((k:ℝ)-1)≠0 := by
    nlinarith
  unfold threePointVariance
  field_simp [hden,hk0,h2k]
  ring_nf
  have hlast : (4:ℝ)-(k:ℝ)*16+(k:ℝ)^2*16≠0 := by
    nlinarith [sq_nonneg ((k:ℝ)-2)]
  field_simp [hlast] <;> ring

end ExactHoeffding
