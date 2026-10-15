import ExactHoeffding.JointAnalyticOptimizer
import ExactHoeffding.JointParameterSymmetry
import ExactHoeffding.BernoulliSharpBounds
import ExactHoeffding.AnalyticContractionCoefficient

/-! # The unique, nondegenerate optimizer on the binomial axis -/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

/-- The ratio of the log-cosh derivative to its argument is strictly decreasing. -/
theorem bernoulli_tanh_ratio_strictAnti :
    StrictAntiOn (fun x : ℝ => Real.tanh x / x) (Ioi 0) := by
  have hd (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun y : ℝ => Real.tanh y / y)
        ((x / Real.cosh x^2 - Real.tanh x) / x^2) x := by
    simpa only [id_eq, mul_one, one_div_mul_eq_div] using!
      (bernoulli_tanh_hasDerivAt x).div (hasDerivAt_id x) hx.ne'
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi, mem_Ioi] at hx
    rw [(hd x hx).deriv]
    apply div_neg_of_neg_of_pos _ (sq_pos_of_pos hx)
    have hh := Real.self_lt_sinh_iff.mpr (show 0 < 2*x by linarith)
    rw [Real.sinh_two_mul] at hh
    rw [Real.tanh_eq_sinh_div_cosh]
    apply (sub_neg).mpr
    apply (div_lt_div_iff₀ (sq_pos_of_pos (Real.cosh_pos x)) (Real.cosh_pos x)).mpr
    nlinarith [Real.cosh_pos x]

/-- Strict squared-coordinate tangent bound; its two contacts are exactly ±a. -/
theorem bernoulli_log_cosh_tangent_square_strict (a x : ℝ) (ha : 0 < a)
    (hx : x^2 ≠ a^2) :
    Real.log (Real.cosh x) - Real.log (Real.cosh a) <
      Real.tanh a / (2*a) * (x^2-a^2) := by
  let c := Real.tanh a/(2*a)
  let g := fun y : ℝ => Real.log (Real.cosh y)-c*y^2
  have hc : 2*c*a=Real.tanh a := by dsimp [c]; field_simp
  have hd (y : ℝ) : HasDerivAt g (Real.tanh y-2*c*y) y := by
    have h := (bernoulli_log_cosh_hasDerivAt y).sub
      (((hasDerivAt_id y).pow 2).const_mul c)
    convert! h using 1
    simp only [id_eq, Nat.cast_ofNat, mul_one]
    ring
  have hcont : Continuous g := continuous_iff_continuousAt.mpr (fun y => (hd y).continuousAt)
  have hleft : StrictMonoOn g (Icc 0 a) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 a) hcont.continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(hd y).deriv]
    have hr := bernoulli_tanh_ratio_strictAnti hy.1 ha hy.2
    have hmul := (div_lt_div_iff₀ ha hy.1).mp hr
    rw [← hc] at hmul
    nlinarith
  have hright : StrictAntiOn g (Ici a) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici a) hcont.continuousOn
    intro y hy
    rw [interior_Ici] at hy
    rw [(hd y).deriv]
    have hr := bernoulli_tanh_ratio_strictAnti ha (lt_trans ha hy) hy
    have hmul := (div_lt_div_iff₀ (lt_trans ha hy) ha).mp hr
    rw [← hc] at hmul
    nlinarith
  have hpos (y : ℝ) (hy : 0 ≤ y) (hne : y ≠ a) : g y < g a := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hleft ⟨hy,hlt.le⟩ ⟨ha.le,le_rfl⟩ hlt
    · exact hright (le_refl a) hgt.le hgt
  by_cases hx0 : 0 ≤ x
  · have hne : x ≠ a := by intro h; apply hx; rw [h]
    have h := hpos x hx0 hne
    dsimp [g,c] at h
    linarith
  · have hne : -x ≠ a := by intro h; apply hx; nlinarith
    have h := hpos (-x) (by linarith) hne
    dsimp [g,c] at h
    rw [Real.cosh_neg,neg_sq] at h
    linarith


/-- Strict Bernoulli contact classification below the balanced parameter. -/
theorem bernoulli_subhalf_quadratic_strict_away_contacts (p t : ℝ)
    (hp : 0 < p) (hph : p < 1/2) (ht : t ≠ 0)
    (htc : t ≠ 2*Real.log ((1-p)/p)) :
    bernoulliCenteredLogMGF p t < bernoulliSharpBeta p*t^2/2 := by
  let a := Real.log ((1-p)/p)
  have ha : 0 < a := Real.log_pos ((lt_div_iff₀ hp).mpr (by linarith))
  have htanh : Real.tanh (a/2) = 1-2*p := by
    have hdr : 1-2*p ∈ Ioo (-1:ℝ) 1 := by constructor <;> linarith
    have hrel : Real.artanh (1-2*p) = a/2 := by
      rw [Real.artanh_eq_half_log ⟨hdr.1.le,hdr.2.le⟩]
      dsimp [a]
      have hr : (1+(1-2*p))/(1-(1-2*p)) = (1-p)/p := by
        field_simp
        ring
      rw [hr]
      ring
    rw [← hrel]
    exact Real.tanh_artanh hdr
  have hne : ((t-a)/2)^2 ≠ (a/2)^2 := by
    intro hsq
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with he | he
    · apply htc; change t = 2*a; linarith
    · apply ht; linarith
  have hs := bernoulli_log_cosh_tangent_square_strict (a/2) ((t-a)/2)
    (by linarith) hne
  rw [htanh] at hs
  rw [bernoulliSharpBeta_eq_formula p (by linarith),
    bernoulli_centered_log_mgf_cosh_representation p t hp hph]
  change Real.log (Real.cosh ((t-a)/2)) - Real.log (Real.cosh (a/2)) +
      (1-2*p)*t/2 < (1-2*p)/(2*a)*t^2/2
  have hid : (1-2*p)/(2*(a/2))*(((t-a)/2)^2-(a/2)^2) +
      (1-2*p)*t/2 = (1-2*p)/(2*a)*t^2/2 := by field_simp; ring
  linarith

/-- The optimal Bernoulli proxy exceeds its actual variance at every nonbalanced
interior margin. This separates the removable zero-tilt value from the maximum. -/
theorem bernoulliSharpBeta_gt_variance_subhalf (p : ℝ)
    (hp : 0 < p) (hph : p < 1/2) : p*(1-p) < bernoulliSharpBeta p := by
  have hd0 : 0 < 1-2*p := by linarith
  have hd1 : 1-2*p < 1 := by linarith
  have hg := logOdds_quadratic_strict (1-2*p) hd0 hd1
  have hrel : logOdds (1-2*p) = Real.log ((1-p)/p) := by
    unfold logOdds
    congr 1
    field_simp
    ring
  rw [hrel] at hg
  have ha : 0 < Real.log ((1-p)/p) :=
    Real.log_pos ((lt_div_iff₀ hp).mpr (by linarith))
  rw [bernoulliSharpBeta_eq_formula p (by linarith)]
  apply (lt_div_iff₀ (by positivity : 0 < 2*Real.log ((1-p)/p))).mpr
  nlinarith only [hg]


/-- Reflection extends strict Bernoulli contact to the entire interior interval. -/
theorem bernoulli_quadratic_strict_away_contacts (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hpne : p ≠ 1/2) (ht : t ≠ 0)
    (htc : t ≠ 2*Real.log ((1-p)/p)) :
    bernoulliCenteredLogMGF p t < bernoulliSharpBeta p*t^2/2 := by
  by_cases hph : p < 1/2
  · exact bernoulli_subhalf_quadratic_strict_away_contacts p t hp hph ht htc
  · have hpg : 1/2 < p := lt_of_le_of_ne (le_of_not_gt hph) (Ne.symm hpne)
    have hq0 : 0 < 1-p := by linarith
    have hqh : 1-p < 1/2 := by linarith
    have hlog : Real.log ((1-(1-p))/(1-p)) = -Real.log ((1-p)/p) := by
      rw [sub_sub_cancel,Real.log_div hp.ne' hq0.ne',Real.log_div hq0.ne' hp.ne']
      ring
    have hs := bernoulli_subhalf_quadratic_strict_away_contacts (1-p) (-t) hq0 hqh
      (neg_ne_zero.mpr ht) (by rw [hlog]; intro h; apply htc; linarith)
    rw [← bernoulli_centered_log_mgf_reflection p t hp hp1,
      bernoulliSharpBeta_reflection p hp hp1 hpne, neg_sq] at hs
    exact hs

theorem bernoulliSharpBeta_gt_variance (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hpne : p ≠ 1/2) :
    p*(1-p) < bernoulliSharpBeta p := by
  by_cases hph : p < 1/2
  · exact bernoulliSharpBeta_gt_variance_subhalf p hp hph
  · have hpg : 1/2 < p := lt_of_le_of_ne (le_of_not_gt hph) (Ne.symm hpne)
    have hs := bernoulliSharpBeta_gt_variance_subhalf (1-p) (by linarith) (by linarith)
    rw [bernoulliSharpBeta_reflection p hp hp1 hpne] at hs
    nlinarith only [hs]

/-- The binomial centered transform is exactly the multiple of its Bernoulli
factor, with no approximation in tilt. -/
theorem joint_binomial_centered_log (m : ℕ) (d t : ℝ) :
    Real.log (jointMGF m 0 d t) - jointMean m 0 d*t =
      (m:ℝ)*bernoulliCenteredLogMGF (jointSuccessFraction d) t := by
  rw [jointMGF_at_zero,Real.log_pow]
  unfold jointMean bernoulliCenteredLogMGF bernoulliMGF
  ring

/-- The free-imbalance binomial contact tilt. -/
def jointBinomialTilt (d : ℝ) : ℝ := 4*Real.artanh d

theorem jointBinomialTilt_eq_log (d : ℝ) (hd : d ∈ Ioo (-1:ℝ) 1) :
    jointBinomialTilt d = 2*Real.log ((1-jointSuccessFraction d)/jointSuccessFraction d) := by
  unfold jointBinomialTilt jointSuccessFraction
  rw [Real.artanh_eq_half_log ⟨hd.1.le,hd.2.le⟩]
  have hrat : (1-(1-d)/2)/((1-d)/2) = (1+d)/(1-d) := by field_simp; ring
  rw [hrat]
  ring

theorem jointBinomialTilt_ne_zero (d : ℝ) (hd : d ∈ Ioo (-1:ℝ) 1) (hne : d ≠ 0) :
    jointBinomialTilt d ≠ 0 := by
  unfold jointBinomialTilt
  intro hz
  have hz' : Real.artanh d = 0 := by linarith
  have htan := Real.tanh_artanh hd
  rw [hz',Real.tanh_zero] at htan
  exact hne htan.symm

/-- The exact binomial proxy value at its distinguished tilt. -/
theorem jointProxyExtension_binomial_contact (m : ℕ) (hm : 0 < m) (d : ℝ)
    (hd : d ∈ Ioo (-1:ℝ) 1) :
    jointProxyExtension m 0 d (jointBinomialTilt d) =
      (m:ℝ)*bernoulliSharpBeta (jointSuccessFraction d) := by
  let p := jointSuccessFraction d
  have hp : 0 < p := by dsimp [p,jointSuccessFraction]; linarith [hd.2]
  have hp1 : p < 1 := by dsimp [p,jointSuccessFraction]; linarith [hd.1]
  by_cases hd0 : d = 0
  · subst d
    rw [show jointBinomialTilt 0 = 0 by simp [jointBinomialTilt],
      jointProxyExtension_zero_tilt_formula m 0 0 (by norm_num)]
    norm_num only [jointSuccessFraction,sub_zero,zero_pow (by norm_num : (2:ℕ)≠0),
      mul_zero,mul_one,sub_zero,bernoulliSharpBeta_half]
    ring
  have ht := jointBinomialTilt_ne_zero d hd hd0
  have hpne : p ≠ 1/2 := by dsimp [p,jointSuccessFraction]; intro h; apply hd0; linarith
  rw [jointProxyExtension_eq_quotient m (by omega) 0 d _ ht,
    joint_binomial_centered_log,jointBinomialTilt_eq_log d hd]
  have hc : bernoulliCenteredLogMGF p (2*Real.log ((1-p)/p)) =
      bernoulliSharpBeta p*(2*Real.log ((1-p)/p))^2/2 := by
    by_cases hph : p < 1/2
    · exact bernoulli_subhalf_contact p hp hph
    · exact bernoulli_gt_half_contact p hp
        (lt_of_le_of_ne (le_of_not_gt hph) (Ne.symm hpne)) hp1
  change 2*((m:ℝ)*bernoulliCenteredLogMGF p (2*Real.log ((1-p)/p))) /
    (2*Real.log ((1-p)/p))^2 = _
  rw [hc]
  have hn : 2*Real.log ((1-p)/p) ≠ 0 := by
    simpa only [p,jointBinomialTilt_eq_log d hd] using ht
  change 2*((m:ℝ)*(bernoulliSharpBeta p*(2*Real.log ((1-p)/p))^2/2)) /
    (2*Real.log ((1-p)/p))^2 = (m:ℝ)*bernoulliSharpBeta p
  have hlog : Real.log ((1-p)/p) ≠ 0 := by
    intro hz
    exact hn (by rw [hz,mul_zero])
  field_simp [hlog]

/-- Every other real tilt has a strictly smaller actual binomial proxy value. -/
theorem jointProxyExtension_binomial_strict (m : ℕ) (hm : 0 < m) (d t : ℝ)
    (hd : d ∈ Ioo (-1:ℝ) 1) (ht : t ≠ jointBinomialTilt d) :
    jointProxyExtension m 0 d t < jointProxyExtension m 0 d (jointBinomialTilt d) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  by_cases hd0 : d = 0
  · subst d
    simp only [jointBinomialTilt,Real.artanh_zero,mul_zero] at ht ⊢
    rw [jointProxyExtension_balanced_axis]
    exact rescaledProxyExtension_limit_strict m hm 0 t ht
  let p := jointSuccessFraction d
  have hp : 0 < p := by dsimp [p,jointSuccessFraction]; linarith [hd.2]
  have hp1 : p < 1 := by dsimp [p,jointSuccessFraction]; linarith [hd.1]
  have hpne : p ≠ 1/2 := by dsimp [p,jointSuccessFraction]; intro h; apply hd0; linarith
  rw [jointProxyExtension_binomial_contact m hm d hd]
  by_cases ht0 : t=0
  · subst t
    rw [jointProxyExtension_zero_tilt_formula m 0 d (by norm_num)]
    have hv := mul_lt_mul_of_pos_left (bernoulliSharpBeta_gt_variance p hp hp1 hpne) hmR
    dsimp [p,jointSuccessFraction] at hv ⊢
    nlinarith only [hv]
  rw [jointProxyExtension_eq_quotient m (by omega) 0 d t ht0,
    joint_binomial_centered_log]
  apply (div_lt_iff₀ (sq_pos_of_ne_zero ht0)).mpr
  have hcontact : t ≠ 2*Real.log ((1-p)/p) := by
    simpa only [p,← jointBinomialTilt_eq_log d hd] using ht
  have hs := mul_lt_mul_of_pos_left
    (bernoulli_quadratic_strict_away_contacts p t hp hp1 hpne ht0 hcontact) hmR
  nlinarith only [hs]

/-- The whole open imbalance interval has a unique global binomial optimizer. -/
theorem jointProxyExtension_binomial_unique_max (m : ℕ) (hm : 0 < m) (d t : ℝ)
    (hd : d ∈ Ioo (-1:ℝ) 1) :
    IsMaxOn (jointProxyExtension m 0 d) univ t ↔ t=jointBinomialTilt d := by
  constructor
  · intro hmax
    by_contra ht
    have hh := hmax (mem_univ (jointBinomialTilt d))
    exact (not_le_of_gt (jointProxyExtension_binomial_strict m hm d t hd ht)) hh
  · rintro rfl
    intro s _
    change jointProxyExtension m 0 d s ≤ jointProxyExtension m 0 d (jointBinomialTilt d)
    by_cases hs : s=jointBinomialTilt d
    · rw [hs]
    · exact (jointProxyExtension_binomial_strict m hm d s hd hs).le


/-- At a nonzero binomial contact the actual proxy is analytic in the tilt. -/
theorem jointProxyExtension_binomial_analyticAt (m : ℕ) (hm : 0 < m) (d t : ℝ)
    (hd : d ∈ Ioo (-1:ℝ) 1) (ht : t ≠ 0) :
    AnalyticAt ℝ (jointProxyExtension m 0 d) t := by
  let p := jointSuccessFraction d
  have hp : 0 < p := by dsimp [p,jointSuccessFraction]; linarith [hd.2]
  have hp1 : p < 1 := by dsimp [p,jointSuccessFraction]; linarith [hd.1]
  have hZ : 0 < 1-p+p*Real.exp t := by positivity
  have hB : AnalyticAt ℝ (bernoulliCenteredLogMGF p) t := by
    unfold bernoulliCenteredLogMGF bernoulliMGF
    exact (analyticAt_log hZ).comp_of_eq
      (analyticAt_const.add (analyticAt_const.mul analyticAt_rexp)) rfl |>.sub
        (analyticAt_const.mul analyticAt_id)
  have hquot : AnalyticAt ℝ (fun s => 2*((m:ℝ)*bernoulliCenteredLogMGF p s)/s^2) t :=
    (analyticAt_const.mul (analyticAt_const.mul hB)).div (analyticAt_id.pow 2)
      (pow_ne_zero 2 ht)
  apply hquot.congr
  filter_upwards [eventually_ne_nhds ht] with s hs
  rw [jointProxyExtension_eq_quotient m (by omega) 0 d s hs,joint_binomial_centered_log]


/-- The first derivative of the actual centered Bernoulli log-MGF. -/
theorem bernoulliCenteredLogMGF_hasDerivAt_explicit (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (bernoulliCenteredLogMGF p)
      (p*Real.exp t/(1-p+p*Real.exp t)-p) t := by
  have hd := ((Real.hasDerivAt_exp t).const_mul p).const_add (1-p)
  have hZ : 0 < 1-p+p*Real.exp t := by positivity
  simpa only [bernoulliCenteredLogMGF,bernoulliMGF,Pi.sub_apply] using!
    (hd.log hZ.ne').sub (hasDerivAt_const_mul p)

/-- The Bernoulli second logarithmic derivative at its nonzero proxy contact
is its original variance. -/
theorem bernoulliCenteredLogMGF_second_deriv_contact (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    iteratedDeriv 2 (bernoulliCenteredLogMGF p) (2*Real.log ((1-p)/p)) = p*(1-p) := by
  have hfirst : deriv (bernoulliCenteredLogMGF p) =
      (fun t => p*Real.exp t/(1-p+p*Real.exp t)-p) := by
    funext t
    exact (bernoulliCenteredLogMGF_hasDerivAt_explicit p t hp hp1).deriv
  let t := 2*Real.log ((1-p)/p)
  have hq : 0 < 1-p := sub_pos.mpr hp1
  have hZ : 0 < 1-p+p*Real.exp t := by positivity
  have hd := (((Real.hasDerivAt_exp t).const_mul p).div
    (((Real.hasDerivAt_exp t).const_mul p).const_add (1-p)) hZ.ne').sub_const p
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,hfirst]
  change deriv (fun t => p*Real.exp t/(1-p+p*Real.exp t)-p) t = _
  have hderiv : deriv (fun s => p*Real.exp s/(1-p+p*Real.exp s)-p) t =
      (p*Real.exp t*(1-p+p*Real.exp t)-p*Real.exp t*(p*Real.exp t)) /
        (1-p+p*Real.exp t)^2 := by
    simpa only [Pi.div_apply] using hd.deriv
  rw [hderiv]
  have he : Real.exp t = ((1-p)/p)^2 := by
    dsimp [t]
    rw [two_mul,Real.exp_add,Real.exp_log (div_pos hq hp)]
    ring
  rw [he]
  field_simp [hp.ne',hq.ne']
  ring

/-- The unique binomial maximizer has a strictly negative Hessian throughout
its open imbalance domain, including the removable balanced case. -/
theorem jointProxyExtension_binomial_deriv2_neg (m : ℕ) (hm : 0 < m) (d : ℝ)
    (hd : d ∈ Ioo (-1:ℝ) 1) :
    iteratedDeriv 2 (jointProxyExtension m 0 d) (jointBinomialTilt d) < 0 := by
  by_cases hd0 : d=0
  · subst d
    simp only [jointBinomialTilt,Real.artanh_zero,mul_zero]
    rw [jointProxyExtension_balanced_axis]
    exact rescaledProxyExtension_limit_deriv2_neg m hm 0
  let p := jointSuccessFraction d
  let t := jointBinomialTilt d
  have hp : 0 < p := by dsimp [p,jointSuccessFraction]; linarith [hd.2]
  have hp1 : p < 1 := by dsimp [p,jointSuccessFraction]; linarith [hd.1]
  have hpne : p ≠ 1/2 := by dsimp [p,jointSuccessFraction]; intro h; apply hd0; linarith
  have ht : t ≠ 0 := jointBinomialTilt_ne_zero d hd hd0
  have hQ : AnalyticAt ℝ (jointProxyExtension m 0 d) t :=
    jointProxyExtension_binomial_analyticAt m hm d t hd ht
  have hlocal : IsLocalMax (jointProxyExtension m 0 d) t := by
    have hm' : IsMaxOn (jointProxyExtension m 0 d) univ t :=
      (jointProxyExtension_binomial_unique_max m hm d t hd).mpr rfl
    exact hm'.isLocalMax (by simp)
  have hderiv : deriv (jointProxyExtension m 0 d) t = 0 := hlocal.deriv_eq_zero
  have hB : AnalyticAt ℝ (bernoulliCenteredLogMGF p) t := by
    have hZ : 0 < 1-p+p*Real.exp t := by positivity
    unfold bernoulliCenteredLogMGF bernoulliMGF
    exact (analyticAt_log hZ).comp_of_eq
      (analyticAt_const.add (analyticAt_const.mul analyticAt_rexp)) rfl |>.sub
        (analyticAt_const.mul analyticAt_id)
  have hfactor : (fun s => (m:ℝ)*bernoulliCenteredLogMGF p s) =
      (fun s => s^2*jointProxyExtension m 0 d s/2) := by
    funext s
    rw [← joint_binomial_centered_log,joint_logMGF_quadratic_factor m (by omega)]
  have hsecond := congrArg (fun f : ℝ→ℝ => iteratedDeriv 2 f t) hfactor
  rw [iteratedDeriv_const_mul_field,iteratedDeriv_div_const,
    iteratedDeriv_fun_mul (by fun_prop) hQ.contDiffAt] at hsecond
  have hbc : iteratedDeriv 2 (bernoulliCenteredLogMGF p) t = p*(1-p) := by
    rw [show t=2*Real.log ((1-p)/p) from jointBinomialTilt_eq_log d hd]
    exact bernoulliCenteredLogMGF_second_deriv_contact p hp hp1
  rw [hbc] at hsecond
  norm_num only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose,
    iteratedDeriv_pow,iteratedDeriv_zero,iteratedDeriv_one,Nat.descFactorial,
    Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,zero_mul,one_mul,mul_zero,
    add_zero,zero_add,pow_zero,pow_one] at hsecond
  rw [hderiv,jointProxyExtension_binomial_contact m hm d hd] at hsecond
  have hgap := bernoulliSharpBeta_gt_variance p hp hp1 hpne
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hg := mul_lt_mul_of_pos_left hgap hmR
  have ht2 := sq_pos_of_ne_zero ht
  nlinarith only [hsecond,hg,ht2]

end
end ExactHoeffding
