import ExactHoeffding.SmallSupportCurvature
import ExactHoeffding.HypergeometricODE
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ExactHoeffding

theorem two_mark_variance_envelope_eq_iff (rho q : ℝ)
    (hr : 0<rho) (hr2 : rho≤2) (hq : 1≤q) :
    (rho*q+1)/(rho+q)^2=1/(1+rho) ↔ q=1 := by
  have hd : 0<(rho+q)^2 := sq_pos_of_pos (by linarith)
  have h1 : 0<1+rho := by linarith
  constructor
  · intro heq
    have hc := (div_eq_div_iff hd.ne' h1.ne').mp heq
    by_contra hne
    have hq1 : 1<q := lt_of_le_of_ne hq (Ne.symm hne)
    have hshape : 0≤(2-rho)*(rho+1) := by positivity
    have hbr : 0<q+1+rho-rho^2 := by nlinarith
    have hp := mul_pos (sub_pos.mpr hq1) hbr
    nlinarith
  · rintro rfl
    field_simp
    ring

theorem threePointVariance_sqrt_envelope_eq_iff (a b c z : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hz : 0<z)
    (hshape : b^2≤4*(a*c)) :
    threePointVariance a b c z = 1/(1+b/Real.sqrt (a*c)) ↔ a=c*z^2 := by
  let h := Real.sqrt (a*c)
  have hh : 0<h := Real.sqrt_pos.mpr (mul_pos ha hc)
  have hsq : h^2=a*c := Real.sq_sqrt (mul_pos ha hc).le
  have hr : 0<b/h := div_pos hb hh
  have hr2 : b/h≤2 := by apply (div_le_iff₀ hh).mpr; nlinarith [hsq]
  have hden : 0<2*h*z := by positivity
  have hq : 1≤(a+c*z^2)/(2*h*z) := by
    apply (le_div_iff₀ hden).mpr
    have hid : (a+c*z^2)^2-(2*h*z)^2=(a-c*z^2)^2 := by
      linear_combination -4*z^2*hsq
    have hp : 0<a+c*z^2 := by positivity
    nlinarith [sq_nonneg (a-c*z^2)]
  rw [threePointVariance_normal_form a b c z h ha hb hc hz hh hsq]
  rw [two_mark_variance_envelope_eq_iff (b/h) ((a+c*z^2)/(2*h*z)) hr hr2 hq]
  rw [div_eq_one_iff_eq hden.ne']
  constructor
  · intro heq
    have hid : (a+c*z^2)^2-(2*h*z)^2=(a-c*z^2)^2 := by
      linear_combination -4*z^2*hsq
    rw [heq,sub_self] at hid
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hid.symm)
  · intro heq
    have he : (h*z)^2=a^2 := by nlinarith [hsq]
    have hhz : 0<h*z := mul_pos hh hz
    have hhz_a : h*z=a := by nlinarith
    linarith

theorem threePointVariance_finite_population_equality_necessary (N a b c z : ℝ)
    (hN : 2<N) (ha : 0<a) (hb : 0<b) (hc : 0<c) (hz : 0<z)
    (hshape : b^2≤4*(a*c))
    (hbalance : N^2*(a*c)≤b^2*(N-2)^2)
    (heq : threePointVariance a b c z=(N-2)/(2*(N-1))) :
    N^2*(a*c)=b^2*(N-2)^2 ∧ a=c*z^2 := by
  let h := Real.sqrt (a*c)
  have hh : 0<h := Real.sqrt_pos.mpr (mul_pos ha hc)
  have hsq : h^2=a*c := Real.sq_sqrt (mul_pos ha hc).le
  have hN0 : 0<N := by linarith
  have hN1 : 0<N-1 := by linarith
  have hN2 : 0<N-2 := by linarith
  have hlower : N*h≤b*(N-2) := by
    have hscaled := congrArg (fun x : ℝ => N^2*x) hsq
    nlinarith [hscaled,mul_pos hb hN2,mul_pos hN0 hh]
  have hden : 0<1+b/h := by positivity
  have henv : 1/(1+b/h)≤(N-2)/(2*(N-1)) := by
    apply (div_le_div_iff₀ hden (by positivity : 0<2*(N-1))).mpr
    have hid : (1+b/h)*h=h+b := by field_simp
    have hgoal : 2*(N-1)*h≤(N-2)*(1+b/h)*h := by nlinarith [hid]
    exact (mul_le_mul_iff_left₀ hh).mp (by nlinarith [hgoal])
  have henvEq : 1/(1+b/h)=(N-2)/(2*(N-1)) := by
    apply le_antisymm henv
    rw [← heq]
    exact threePointVariance_sqrt_envelope a b c z ha hb hc hz hshape
  have hmul := (div_eq_div_iff hden.ne' (by positivity : 2*(N-1)≠0)).mp henvEq
  have hid : (1+b/h)*h=h+b := by field_simp
  have hproduct : N*h=b*(N-2) := by
    linear_combination h*(hmul) + (N-2)*hid
  constructor
  · have hsquares := congrArg (fun x : ℝ => x^2) hproduct
    nlinarith only [hsquares,congrArg (fun x : ℝ => N^2*x) hsq]
  · apply (threePointVariance_sqrt_envelope_eq_iff a b c z ha hb hc hz hshape).mp
    exact heq.trans henvEq.symm

theorem hypergeom_two_draw_curvature_equality_necessary (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) (t : ℝ)
    (heq : deriv (deriv (fun u => Real.log (hypergeomMGF N k 2 u))) t =
      ((N:ℝ)-2)/(2*((N:ℝ)-1))) : N=2*k ∧ t=0 := by
  have hkle : k≤N := by omega
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hNkR : (k:ℝ)+2≤N := by exact_mod_cast hNk
  have ha : 0<((N:ℝ)-k)*((N:ℝ)-k-1) := by apply mul_pos <;> linarith
  have hb : 0<(k:ℝ)*((N:ℝ)-k) := by apply mul_pos <;> linarith
  have hc : 0<(k:ℝ)*((k:ℝ)-1) := by apply mul_pos <;> linarith
  have hlow : 0≤4*((k:ℝ)-1)*((N:ℝ)-k-1)-(k:ℝ)*((N:ℝ)-k) := by
    have hprod : 0≤((k:ℝ)-2)*((N:ℝ)-k-2) := by apply mul_nonneg <;> linarith
    nlinarith
  have hshape : ((k:ℝ)*((N:ℝ)-k))^2≤
      4*(((N:ℝ)-k)*((N:ℝ)-k-1)*((k:ℝ)*((k:ℝ)-1))) := by
    have hmul := mul_nonneg hb.le hlow
    nlinarith only [hmul]
  have hbalance : (N:ℝ)^2*
      (((N:ℝ)-k)*((N:ℝ)-k-1)*((k:ℝ)*((k:ℝ)-1)))≤
      ((k:ℝ)*((N:ℝ)-k))^2*((N:ℝ)-2)^2 := by
    have hp : 0≤(k:ℝ)*((N:ℝ)-k)*((N:ℝ)-1)*((N:ℝ)-2*k)^2 := by
      apply mul_nonneg
      · apply mul_nonneg hb.le; linarith
      · positivity
    nlinarith only [hp]
  rw [hypergeom_two_draw_curvature_formula N k hkle (by omega) t] at heq
  have hnec := threePointVariance_finite_population_equality_necessary (N:ℝ) _ _ _ _
    (by linarith) ha hb hc (Real.exp_pos t) hshape hbalance heq
  have hprod : (k:ℝ)*((N:ℝ)-k)*((N:ℝ)-1)*((N:ℝ)-2*k)^2=0 := by
    nlinarith only [hnec.1]
  have hfactor : (k:ℝ)*((N:ℝ)-k)*((N:ℝ)-1)≠0 :=
    (mul_pos hb (by linarith : 0<(N:ℝ)-1)).ne'
  have hN2k : (N:ℝ)=2*(k:ℝ) := by
    have := (mul_eq_zero.mp hprod).resolve_left hfactor
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)
  have hNnat : N=2*k := by exact_mod_cast hN2k
  have htEq : (Real.exp t)^2=1 := by
    have hz := hnec.2
    rw [hN2k] at hz
    have haEq : (2*(k:ℝ)-k)*(2*(k:ℝ)-k-1)=(k:ℝ)*((k:ℝ)-1) := by ring
    rw [haEq] at hz
    nlinarith
  have hzt : Real.exp t=1 := by nlinarith [Real.exp_pos t]
  exact ⟨hNnat, Real.exp_injective (by simpa using hzt)⟩

theorem hypergeom_two_draw_curvature_equality_iff (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) (t : ℝ) :
    deriv (deriv (fun u => Real.log (hypergeomMGF N k 2 u))) t =
      ((N:ℝ)-2)/(2*((N:ℝ)-1)) ↔ N=2*k ∧ t=0 := by
  constructor
  · exact hypergeom_two_draw_curvature_equality_necessary N k hk hNk t
  · rintro ⟨rfl,rfl⟩
    exact hypergeom_two_draw_curvature_balanced k hk

theorem bernoulli_rational_variance_equality_iff (p z : ℝ)
    (hp0 : 0<p) (hp1 : p<1) (hz : 0<z) :
    (p*z*(1-p+p*z)-(p*z)^2)/(1-p+p*z)^2=1/4 ↔ z=(1-p)/p := by
  have hd : 0<1-p+p*z := by positivity
  constructor
  · intro heq
    have hcross := (div_eq_div_iff (pow_ne_zero 2 hd.ne') (by norm_num : (4:ℝ)≠0)).mp heq
    have hzero : (p*z-(1-p))^2=0 := by nlinarith only [hcross]
    have hmul : p*z=1-p := sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)
    exact (eq_div_iff hp0.ne').mpr (by nlinarith only [hmul])
  · intro hzEq
    rw [hzEq]
    field_simp [hp0.ne', (sub_pos.mpr hp1).ne']
    ring

theorem hypergeom_one_draw_curvature_equality_iff (N k : ℕ)
    (hk0 : 0<k) (hkN : k<N) (t : ℝ) :
    deriv (deriv (fun u => Real.log (hypergeomMGF N k 1 u))) t=1/4 ↔
      t=Real.log (((N:ℝ)-k)/k) := by
  have hN0 : 0<N := by omega
  have hNR : (0:ℝ)<N := by exact_mod_cast hN0
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  have hkNR : (k:ℝ)<N := by exact_mod_cast hkN
  let p : ℝ := (k:ℝ)/N
  have hp0 : 0<p := div_pos hkR hNR
  have hp1 : p<1 := (div_lt_one hNR).mpr hkNR
  have hfirst : finiteTiltFirst (Finset.range (1+1))
      (hypergeomMass N k 1) (fun i => (i:ℝ)) t=p*Real.exp t := by
    simp [finiteTiltFirst,Finset.sum_range_succ,hypergeomMass_one_success,p]
  have hsecond : finiteTiltSecond (Finset.range (1+1))
      (hypergeomMass N k 1) (fun i => (i:ℝ)) t=p*Real.exp t := by
    simp [finiteTiltSecond,Finset.sum_range_succ,hypergeomMass_one_success,p]
  rw [hypergeomLogMGF_second_deriv N k 1 hkN.le (by omega) t,hfirst,hsecond,
    hypergeomMGF_singleton N k hkN.le hN0 t]
  simp only [bernoulliMGF, ← sq]
  change (p*Real.exp t*(1-p+p*Real.exp t)-(p*Real.exp t)^2)/(1-p+p*Real.exp t)^2=1/4 ↔ _
  rw [bernoulli_rational_variance_equality_iff p (Real.exp t) hp0 hp1 (Real.exp_pos t)]
  have hratio : (1-p)/p=((N:ℝ)-k)/k := by dsimp [p]; field_simp [hNR.ne',hkR.ne']
  rw [hratio]
  have hpos : 0<((N:ℝ)-k)/k := div_pos (sub_pos.mpr hkNR) hkR
  constructor
  · intro heq
    rw [← Real.log_exp t,heq]
  · rintro rfl
    exact Real.exp_log hpos


end ExactHoeffding
