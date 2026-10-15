import ExactHoeffding.SmallSupportCurvature
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Three-point quadratic proxy arguments

The calculus lemma records the tangent bound in the squared coordinate.
The finite-mass statements identify the nonzero contact point directly.
-/

namespace ExactHoeffding

/-- A decreasing derivative-to-argument ratio gives a tangent majorant in
the squared coordinate for every even differentiable real function. -/
theorem even_tangent_square_of_deriv_ratio_antitone
    (f f' : ℝ → ℝ) (heven : ∀ x, f (-x)=f x)
    (hd : ∀ x, HasDerivAt f (f' x) x)
    (hratio : AntitoneOn (fun x => f' x/x) (Set.Ioi 0))
    (a : ℝ) (ha : 0<a) (x : ℝ) :
    f x-f a≤f' a/(2*a)*(x^2-a^2) := by
  let c := f' a/(2*a)
  let g := fun y => f y-c*y^2
  have hc : 2*c*a=f' a := by dsimp [c]; field_simp
  have hgd (y : ℝ) : HasDerivAt g (f' y-2*c*y) y := by
    have h := (hd y).sub (((hasDerivAt_id y).pow 2).const_mul c)
    convert h using 1 <;> try rfl
    norm_num only [Nat.cast_ofNat, pow_one, id_eq]
    ring
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr (fun y => (hgd y).continuousAt)
  have hleft : MonotoneOn g (Set.Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a) hgcont.continuousOn
      (fun y _ => (hgd y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [interior_Icc] at hy
    rw [(hgd y).deriv]
    have hyr := hratio hy.1 ha (le_of_lt hy.2)
    have hmul := (div_le_div_iff₀ ha hy.1).mp hyr
    have hc' : f' a*y=2*c*y*a := by rw [← hc]; ring
    rw [hc'] at hmul
    nlinarith [hc]
  have hright : AntitoneOn g (Set.Ici a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici a) hgcont.continuousOn
      (fun y _ => (hgd y).differentiableAt.differentiableWithinAt)
    intro y hy
    rw [interior_Ici] at hy
    rw [(hgd y).deriv]
    have hy0 : 0<y := lt_trans ha hy
    have hyr := hratio ha hy0 (le_of_lt hy)
    have hmul := (div_le_div_iff₀ hy0 ha).mp hyr
    have hc' : f' a*y=2*c*y*a := by rw [← hc]; ring
    rw [hc'] at hmul
    nlinarith [hc]
  have hpos (y : ℝ) (hy : 0≤y) : g y≤g a := by
    by_cases hya : y≤a
    · exact hleft ⟨hy,hya⟩ ⟨ha.le,le_rfl⟩ hya
    · exact hright (show a∈Set.Ici a from le_refl a)
        (show y∈Set.Ici a from le_of_lt (lt_of_not_ge hya))
        (le_of_lt (lt_of_not_ge hya))
  by_cases hx : 0≤x
  · have h := hpos x hx
    dsimp [g,c] at h
    nlinarith
  · have h := hpos (-x) (by linarith)
    dsimp [g,c] at h
    rw [heven x] at h
    nlinarith

noncomputable def threeMassMGF (p0 p1 p2 t : ℝ) : ℝ :=
  p0+p1*Real.exp t+p2*Real.exp (2*t)

/-- The three-point MGF has a second exact contact at the log mass ratio. -/
theorem threeMassMGF_log_ratio (p0 p1 p2 : ℝ)
    (hp0 : 0<p0) (hp2 : 0<p2) (hn : p0+p1+p2=1) :
    threeMassMGF p0 p1 p2 (Real.log (p0/p2))=p0/p2 := by
  have he : Real.exp (Real.log (p0/p2))=p0/p2 := Real.exp_log (div_pos hp0 hp2)
  unfold threeMassMGF
  rw [show 2*Real.log (p0/p2)=Real.log (p0/p2)+Real.log (p0/p2) by ring,
    Real.exp_add, he]
  field_simp
  linear_combination hn

theorem threeMass_centered_log_ratio (p0 p1 p2 : ℝ)
    (hp0 : 0<p0) (hp2 : 0<p2) (hn : p0+p1+p2=1) :
    Real.log (threeMassMGF p0 p1 p2 (Real.log (p0/p2)))-
      (p1+2*p2)*Real.log (p0/p2)=(p0-p2)*Real.log (p0/p2) := by
  rw [threeMassMGF_log_ratio p0 p1 p2 hp0 hp2 hn]
  linear_combination -Real.log (p0/p2)*hn

/-- Candidate quadratic proxy attains equality at the log-ratio tilt. -/
theorem threeMass_candidate_proxy_equality (p0 p1 p2 : ℝ)
    (hp0 : 0<p0) (hp2 : 0<p2) (hn : p0+p1+p2=1)
    (hlog : Real.log (p0/p2)≠0) :
    Real.log (threeMassMGF p0 p1 p2 (Real.log (p0/p2)))-
      (p1+2*p2)*Real.log (p0/p2)=
      (2*(p0-p2)/Real.log (p0/p2))*Real.log (p0/p2)^2/2 := by
  rw [threeMass_centered_log_ratio p0 p1 p2 hp0 hp2 hn]
  field_simp

theorem hypergeom_two_draw_mgf_threeMass (N k : ℕ) (t : ℝ) :
    hypergeomMGF N k 2 t=threeMassMGF
      (hypergeomMass N k 2 0) (hypergeomMass N k 2 1) (hypergeomMass N k 2 2) t := by
  simp [hypergeomMGF, finiteMGF, threeMassMGF, Finset.sum_range_succ,
    mul_comm t 2]

theorem hypergeom_two_draw_mass_mean (N k : ℕ) (hk : k≤N) (hN : 2≤N) :
    hypergeomMass N k 2 1+2*hypergeomMass N k 2 2=2*(k:ℝ)/N := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hN1 : (N:ℝ)-1≠0 := by
    have : (2:ℝ)≤N := by exact_mod_cast hN
    linarith
  rw [hypergeomMass_two_one N k hk,hypergeomMass_two_two N k]
  field_simp
  ring

/-- Exact contact of the actual centered two-draw hypergeometric log MGF. -/
theorem hypergeom_two_draw_candidate_equality (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) :
    let t := Real.log (hypergeomMass N k 2 0 / hypergeomMass N k 2 2)
    Real.log (hypergeomMGF N k 2 t)-2*(k:ℝ)/(N:ℝ)*t=
      (hypergeomMass N k 2 0-hypergeomMass N k 2 2)*t := by
  have hkle : k≤N := by omega
  have hN : 2≤N := by omega
  have hnorm := hypergeomMass_total N k 2 hkle hN
  have hn : hypergeomMass N k 2 0+hypergeomMass N k 2 1+
      hypergeomMass N k 2 2=1 := by
    simpa [Finset.sum_range_succ] using hnorm
  have hd : 0<(Nat.choose N 2:ℝ) := by exact_mod_cast Nat.choose_pos hN
  have hp0 : 0<hypergeomMass N k 2 0 := by
    unfold hypergeomMass hypergeomCount
    apply div_pos _ hd
    norm_num only [Nat.choose_zero_right, Nat.sub_zero, one_mul]
    exact_mod_cast Nat.choose_pos (show 2≤N-k by omega)
  have hp2 : 0<hypergeomMass N k 2 2 := by
    unfold hypergeomMass hypergeomCount
    apply div_pos _ hd
    norm_num only [Nat.sub_self, Nat.choose_zero_right, mul_one]
    exact_mod_cast Nat.choose_pos hk
  dsimp only
  rw [hypergeom_two_draw_mgf_threeMass]
  rw [← hypergeom_two_draw_mass_mean N k hkle hN]
  exact threeMass_centered_log_ratio _ _ _ hp0 hp2 hn

noncomputable def logCoshMass (A B x : ℝ) := Real.log (A+B*Real.cosh x)
noncomputable def logCoshMassFirst (A B x : ℝ) :=
  B*Real.sinh x/(A+B*Real.cosh x)
noncomputable def logCoshMassSecond (A B x : ℝ) :=
  B*(A*Real.cosh x+B)/(A+B*Real.cosh x)^2
noncomputable def logCoshMassThird (A B x : ℝ) :=
  B*Real.sinh x*(A^2-A*B*Real.cosh x-2*B^2)/(A+B*Real.cosh x)^3

theorem logCoshMass_hasDerivAt (A B x : ℝ) (hA : 0<A) (hB : 0<B) :
    HasDerivAt (logCoshMass A B) (logCoshMassFirst A B x) x := by
  have hd : 0<A+B*Real.cosh x := by positivity
  exact ((Real.hasDerivAt_cosh x).const_mul B |>.const_add A).log (ne_of_gt hd)

theorem logCoshMassFirst_hasDerivAt (A B x : ℝ) (hA : 0<A) (hB : 0<B) :
    HasDerivAt (logCoshMassFirst A B) (logCoshMassSecond A B x) x := by
  have hd : A+B*Real.cosh x≠0 := ne_of_gt (by positivity)
  have h := ((Real.hasDerivAt_sinh x).const_mul B).div
    ((Real.hasDerivAt_cosh x).const_mul B |>.const_add A) hd
  convert h using 1 <;> try rfl
  unfold logCoshMassSecond
  field_simp [hd]
  linear_combination -B*(Real.cosh_sq_sub_sinh_sq x)

theorem logCoshMassSecond_hasDerivAt (A B x : ℝ) (hA : 0<A) (hB : 0<B) :
    HasDerivAt (logCoshMassSecond A B) (logCoshMassThird A B x) x := by
  have hd : A+B*Real.cosh x≠0 := ne_of_gt (by positivity)
  have hn := ((Real.hasDerivAt_cosh x).const_mul A |>.add_const B).const_mul B
  have hden := ((Real.hasDerivAt_cosh x).const_mul B |>.const_add A).pow 2
  have h := hn.div hden (pow_ne_zero 2 hd)
  convert h using 1 <;> try rfl
  unfold logCoshMassThird
  simp only [Pi.pow_apply, Nat.cast_ofNat]
  field_simp [hd]
  ring

theorem logCoshMassThird_nonpos (A B x : ℝ)
    (hA : 0<A) (hB : 0<B) (hAB : A≤2*B) (hx : 0≤x) :
    logCoshMassThird A B x≤0 := by
  have hbr : A^2-A*B*Real.cosh x-2*B^2≤0 := by
    have h1 := Real.one_le_cosh x
    have h2 := mul_nonneg (sub_nonneg.mpr hAB) (by positivity : 0≤A+B)
    have h3 := mul_nonneg (mul_nonneg hA.le hB.le) (sub_nonneg.mpr h1)
    nlinarith
  unfold logCoshMassThird
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hB.le (Real.sinh_nonneg_iff.mpr hx)) hbr
  · positivity

theorem logCoshMass_ratio_antitone (A B : ℝ)
    (hA : 0<A) (hB : 0<B) (hAB : A≤2*B) :
    AntitoneOn (fun x => logCoshMassFirst A B x/x) (Set.Ioi 0) := by
  have hconc : ConcaveOn ℝ (Set.Ici 0) (logCoshMassFirst A B) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 0)
      ((continuous_iff_continuousAt.mpr
        (fun x => (logCoshMassFirst_hasDerivAt A B x hA hB).continuousAt)).continuousOn)
      (fun x _ => (logCoshMassFirst_hasDerivAt A B x hA hB).hasDerivWithinAt)
      (fun x _ => (logCoshMassSecond_hasDerivAt A B x hA hB).hasDerivWithinAt)
    intro x hx
    rw [interior_Ici] at hx
    exact logCoshMassThird_nonpos A B x hA hB hAB (le_of_lt hx)
  intro x hx y hy hxy
  change 0<x at hx
  change 0<y at hy
  have h := hconc.neg.secant_mono (show (0:ℝ)∈Set.Ici 0 by simp)
    (show x∈Set.Ici 0 from le_of_lt hx) (show y∈Set.Ici 0 from le_of_lt hy)
    (ne_of_gt hx) (ne_of_gt hy) hxy
  simp only [Pi.neg_apply, logCoshMassFirst, Real.sinh_zero, mul_zero,
    zero_div, neg_zero, sub_zero, neg_div] at h
  dsimp [logCoshMassFirst]
  linarith

/-- The global squared-coordinate tangent inequality for the three-mass log. -/
theorem logCoshMass_tangent_square (A B a x : ℝ)
    (hA : 0<A) (hB : 0<B) (hAB : A≤2*B) (ha : 0<a) :
    logCoshMass A B x-logCoshMass A B a≤
      logCoshMassFirst A B a/(2*a)*(x^2-a^2) := by
  exact even_tangent_square_of_deriv_ratio_antitone
    (logCoshMass A B) (logCoshMassFirst A B)
    (fun y => by simp [logCoshMass])
    (fun y => logCoshMass_hasDerivAt A B y hA hB)
    (logCoshMass_ratio_antitone A B hA hB hAB) a ha x

/-- Algebraic hyperbolic representation after balancing the two endpoint masses. -/
theorem threeMassMGF_cosh_representation (p0 p1 p2 B a t : ℝ)
    (h0 : B*Real.exp a/2=p0) (h2 : B*Real.exp (-a)/2=p2) :
    threeMassMGF p0 p1 p2 t=
      Real.exp t*(p1+B*Real.cosh (t-a)) := by
  have hp0 : B*Real.exp a=2*p0 := by linarith
  have hp2 : B*Real.exp (-a)=2*p2 := by linarith
  have ht : Real.exp (2*t)=Real.exp t*Real.exp t := by
    rw [show 2*t=t+t by ring,Real.exp_add]
  have he : Real.exp t*Real.exp (-t)=1 := by rw [← Real.exp_add]; simp
  unfold threeMassMGF
  rw [Real.cosh_eq, show t-a=t+(-a) by ring,Real.exp_add,
    show -(t+-a)=a+(-t) by ring,Real.exp_add,ht]
  have h02 := congrArg (fun y : ℝ => y*Real.exp t^2) hp2
  have h00 : B*Real.exp a*Real.exp t*Real.exp (-t)=2*p0 := by
    calc
      _ = (B*Real.exp a)*(Real.exp t*Real.exp (-t)) := by ring
      _ = 2*p0 := by rw [he,hp0]; ring
  nlinarith [he]

theorem threeMass_balance_cosh (p0 p1 p2 B a : ℝ)
    (h0 : B*Real.exp a/2=p0) (h2 : B*Real.exp (-a)/2=p2)
    (hn : p0+p1+p2=1) : p1+B*Real.cosh a=1 := by
  rw [Real.cosh_eq]
  nlinarith

theorem threeMass_balance_sinh (p0 p2 B a : ℝ)
    (h0 : B*Real.exp a/2=p0) (h2 : B*Real.exp (-a)/2=p2) :
    B*Real.sinh a=p0-p2 := by
  rw [Real.sinh_eq]
  linarith

/-- The three-mass quadratic inequality from the proved squared-coordinate tangent. -/
theorem threeMass_quadratic_bound_of_balanced_parameters
    (p0 p1 p2 B a t : ℝ) (hp1 : 0<p1) (hB : 0<B)
    (hshape : p1≤2*B) (ha : 0<a)
    (h0 : B*Real.exp a/2=p0) (h2 : B*Real.exp (-a)/2=p2)
    (hn : p0+p1+p2=1) :
    Real.log (threeMassMGF p0 p1 p2 t)-(p1+2*p2)*t≤
      ((p0-p2)/a)*t^2/2 := by
  have hb := threeMass_balance_cosh p0 p1 p2 B a h0 h2 hn
  have hs := threeMass_balance_sinh p0 p2 B a h0 h2
  have hf : logCoshMass p1 B a=0 := by simp [logCoshMass,hb]
  have hfp : logCoshMassFirst p1 B a=p0-p2 := by
    simp [logCoshMassFirst,hb,hs]
  have htan := logCoshMass_tangent_square p1 B a (t-a) hp1 hB hshape ha
  rw [hf,hfp,sub_zero] at htan
  rw [threeMassMGF_cosh_representation p0 p1 p2 B a t h0 h2]
  rw [Real.log_mul (Real.exp_ne_zero t)
    (ne_of_gt (by positivity : 0<p1+B*Real.cosh (t-a))),Real.log_exp]
  unfold logCoshMass at htan
  have hn' : 1-(p1+2*p2)=p0-p2 := by linarith
  have hr : (p0-p2)/(2*a)*(t-a)^2-(p0-p2)/(2*a)*a^2+
      (p0-p2)*t=((p0-p2)/a)*t^2/2 := by field_simp; ring
  nlinarith

/-- Positive endpoint masses produce the hyperbolic balancing parameters. -/
theorem threeMass_balance_parameters (p0 p2 : ℝ) (hp0 : 0<p0) (hp2 : 0<p2) :
    let B := 2*Real.sqrt (p0*p2)
    let a := Real.log (p0/p2)/2
    B*Real.exp a/2=p0 ∧ B*Real.exp (-a)/2=p2 := by
  let h := Real.sqrt (p0*p2)
  let a := Real.log (p0/p2)/2
  have hh : 0<h := Real.sqrt_pos.mpr (mul_pos hp0 hp2)
  have hsq : h^2=p0*p2 := Real.sq_sqrt (mul_nonneg hp0.le hp2.le)
  have hexp : (Real.exp a)^2=p0/p2 := by
    rw [pow_two, ← Real.exp_add]
    dsimp [a]
    rw [add_halves,Real.exp_log (div_pos hp0 hp2)]
  have hq : (p0/p2)*p2=p0 := by field_simp
  have hleftsq : (h*Real.exp a)^2=p0^2 := by
    rw [mul_pow,hsq,hexp]
    field_simp
  have hleft : h*Real.exp a=p0 := by
    have hpos := mul_pos hh (Real.exp_pos a)
    nlinarith [hleftsq]
  have hright : h*Real.exp (-a)=p2 := by
    rw [Real.exp_neg]
    apply (mul_left_cancel₀ (ne_of_gt (Real.exp_pos a)))
    field_simp
    nlinarith [hsq,hleft]
  dsimp only
  change 2*h*Real.exp a/2=p0 ∧ 2*h*Real.exp (-a)/2=p2
  constructor <;> nlinarith [hleft,hright]

/-- The asymmetric three-point sharp quadratic upper bound, with all hypotheses explicit. -/
theorem threeMass_asymmetric_quadratic_bound (p0 p1 p2 t : ℝ)
    (hp0 : 0<p0) (hp1 : 0<p1) (hp2 : 0<p2) (horder : p2<p0)
    (hn : p0+p1+p2=1) (hshape : p1≤4*Real.sqrt (p0*p2)) :
    Real.log (threeMassMGF p0 p1 p2 t)-(p1+2*p2)*t≤
      (2*(p0-p2)/Real.log (p0/p2))*t^2/2 := by
  have hparams := threeMass_balance_parameters p0 p2 hp0 hp2
  have ha : 0<Real.log (p0/p2)/2 := by
    have hr : 1<p0/p2 := (lt_div_iff₀ hp2).mpr (by simpa using horder)
    exact div_pos (Real.log_pos hr) (by norm_num)
  have h := threeMass_quadratic_bound_of_balanced_parameters
    p0 p1 p2 (2*Real.sqrt (p0*p2)) (Real.log (p0/p2)/2) t
    hp1 (by positivity) (by linarith) ha hparams.1 hparams.2 hn
  convert h using 1
  ring

/-- Three-mass admissibility for the actual two-draw hypergeometric probabilities. -/
theorem hypergeom_two_draw_threeMass_admissible (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) :
    0<hypergeomMass N k 2 0 ∧ 0<hypergeomMass N k 2 1 ∧
    0<hypergeomMass N k 2 2 ∧
    hypergeomMass N k 2 1≤4*Real.sqrt
      (hypergeomMass N k 2 0*hypergeomMass N k 2 2) := by
  have hkle : k≤N := by omega
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hNkR : (k:ℝ)+2≤N := by exact_mod_cast hNk
  have hN0 : (0:ℝ)<N := by linarith
  have hN1 : (0:ℝ)<(N:ℝ)-1 := by linarith
  have ha : 0<((N:ℝ)-k)*((N:ℝ)-k-1) := by
    apply mul_pos <;> linarith
  have hb : 0<(k:ℝ)*((N:ℝ)-k) := by
    apply mul_pos <;> linarith
  have hc : 0<(k:ℝ)*((k:ℝ)-1) := by
    apply mul_pos <;> linarith
  have hp0 : 0<hypergeomMass N k 2 0 := by
    rw [hypergeomMass_two_zero N k hkle]
    exact div_pos ha (mul_pos hN0 hN1)
  have hp1 : 0<hypergeomMass N k 2 1 := by
    rw [hypergeomMass_two_one N k hkle]
    exact div_pos (by nlinarith [hb]) (mul_pos hN0 hN1)
  have hp2 : 0<hypergeomMass N k 2 2 := by
    rw [hypergeomMass_two_two]
    exact div_pos hc (mul_pos hN0 hN1)
  refine ⟨hp0,hp1,hp2,?_⟩
  have hprod : 0≤((k:ℝ)-2)*((N:ℝ)-k-2) := by
    apply mul_nonneg <;> linarith
  have hbr : 0≤4*((k:ℝ)-1)*((N:ℝ)-k-1)-(k:ℝ)*((N:ℝ)-k) := by
    nlinarith
  have hmul := mul_nonneg hb.le hbr
  have hsquare : (hypergeomMass N k 2 1)^2≤
      16*(hypergeomMass N k 2 0*hypergeomMass N k 2 2) := by
    rw [hypergeomMass_two_zero N k hkle,hypergeomMass_two_one N k hkle,
      hypergeomMass_two_two]
    field_simp
    have hscaled := mul_nonneg
      (show (0:ℝ)≤(N:ℝ)-k by linarith) hbr
    nlinarith only [hscaled]
  have hsqrt := Real.sq_sqrt (mul_nonneg hp0.le hp2.le)
  have hsq0 := Real.sqrt_nonneg (hypergeomMass N k 2 0*hypergeomMass N k 2 2)
  nlinarith

/-- All-tilt AAM quadratic bound specialized to actual two-draw sampling,
on the orientation where the zero mass exceeds the two-success mass. -/
theorem hypergeom_two_draw_proxy_upper (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) (hhalf : 2*k<N) (t : ℝ) :
    Real.log (hypergeomMGF N k 2 t)-2*(k:ℝ)/(N:ℝ)*t≤
      (2*(hypergeomMass N k 2 0-hypergeomMass N k 2 2)/
        Real.log (hypergeomMass N k 2 0/hypergeomMass N k 2 2))*t^2/2 := by
  have hkle : k≤N := by omega
  have hN : 2≤N := by omega
  have hh : 2*(k:ℝ)<N := by exact_mod_cast hhalf
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hN0 : (0:ℝ)<N := by linarith
  have hN1 : (0:ℝ)<(N:ℝ)-1 := by linarith
  obtain ⟨hp0,hp1,hp2,hshape⟩ := hypergeom_two_draw_threeMass_admissible N k hk hNk
  have horder : hypergeomMass N k 2 2<hypergeomMass N k 2 0 := by
    rw [hypergeomMass_two_zero N k hkle,hypergeomMass_two_two]
    apply (div_lt_div_iff_of_pos_right (mul_pos hN0 hN1)).mpr
    have hp : 0<((N:ℝ)-2*k)*((N:ℝ)-1) := by
      apply mul_pos <;> linarith
    nlinarith
  have hn : hypergeomMass N k 2 0+hypergeomMass N k 2 1+
      hypergeomMass N k 2 2=1 := by
    simpa [Finset.sum_range_succ] using hypergeomMass_total N k 2 hkle hN
  rw [hypergeom_two_draw_mgf_threeMass,← hypergeom_two_draw_mass_mean N k hkle hN]
  exact threeMass_asymmetric_quadratic_bound _ _ _ t hp0 hp1 hp2 horder hn hshape

end ExactHoeffding
