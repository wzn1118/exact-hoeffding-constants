import ExactHoeffding.TwoDrawProxy
import ExactHoeffding.CurvatureBridge
import ExactHoeffding.BernoulliBalancedLimit
import Mathlib.Analysis.Calculus.LHopital

open Filter Set
open scoped Topology

namespace ExactHoeffding

/-- A coefficient valid for the whole centered log-Laplace transform. -/
def IsQuadraticProxy (ψ : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ t, ψ t ≤ C*t^2/2

/-- The least coefficient among all global quadratic bounds. -/
def IsOptimalQuadraticProxy (ψ : ℝ → ℝ) (C : ℝ) : Prop :=
  IsQuadraticProxy ψ C ∧ ∀ D, IsQuadraticProxy ψ D → C≤D

noncomputable def threeMassCenteredLog (p0 p1 p2 t : ℝ) : ℝ :=
  Real.log (threeMassMGF p0 p1 p2 t)-(p1+2*p2)*t

noncomputable def threeMassProxy (p0 p2 : ℝ) : ℝ :=
  if p0=p2 then 2*p0 else 2*(p0-p2)/Real.log (p0/p2)

theorem optimalQuadraticProxy_of_contact (ψ : ℝ → ℝ) (C t : ℝ)
    (hupper : IsQuadraticProxy ψ C) (ht : t≠0)
    (hcontact : ψ t=C*t^2/2) : IsOptimalQuadraticProxy ψ C := by
  refine ⟨hupper,?_⟩
  intro D hD
  have h := hD t
  rw [hcontact] at h
  have hp : 0<t^2 := sq_pos_of_ne_zero ht
  nlinarith

theorem threeMassMGF_pos (p0 p1 p2 t : ℝ)
    (hp0 : 0<p0) (hp1 : 0<p1) (hp2 : 0<p2) :
    0<threeMassMGF p0 p1 p2 t := by
  unfold threeMassMGF
  positivity

theorem threeMassMGF_reflection (p0 p1 p2 t : ℝ) :
    threeMassMGF p0 p1 p2 t=
      Real.exp (2*t)*threeMassMGF p2 p1 p0 (-t) := by
  have ht : Real.exp (2*t)=Real.exp t^2 := by
    rw [show 2*t=t+t by ring,Real.exp_add,pow_two]
  have hnt : Real.exp (2*(-t))=(Real.exp t)⁻¹^2 := by
    rw [show 2*(-t)=-(2*t) by ring,Real.exp_neg,ht,inv_pow]
  unfold threeMassMGF
  rw [ht,hnt,Real.exp_neg]
  field_simp
  ring

theorem threeMassCenteredLog_reflection (p0 p1 p2 t : ℝ)
    (hp0 : 0<p0) (hp1 : 0<p1) (hp2 : 0<p2)
    (hn : p0+p1+p2=1) :
    threeMassCenteredLog p0 p1 p2 t=threeMassCenteredLog p2 p1 p0 (-t) := by
  unfold threeMassCenteredLog
  rw [threeMassMGF_reflection p0 p1 p2 t,
    Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (threeMassMGF_pos p2 p1 p0 (-t) hp2 hp1 hp0)),
    Real.log_exp]
  linear_combination -2*t*hn

theorem threeMass_proxy_ratio_reflection (p0 p2 : ℝ)
    (hp0 : 0<p0) (hp2 : 0<p2) :
    2*(p2-p0)/Real.log (p2/p0)=2*(p0-p2)/Real.log (p0/p2) := by
  rw [Real.log_div (ne_of_gt hp2) (ne_of_gt hp0),
    Real.log_div (ne_of_gt hp0) (ne_of_gt hp2)]
  rw [show Real.log p2-Real.log p0=-(Real.log p0-Real.log p2) by ring,
    div_neg,show 2*(p2-p0)=-(2*(p0-p2)) by ring,neg_div,neg_neg]

/-- Reflection supplies the second asymmetric orientation. -/
theorem threeMass_asymmetric_proxy_upper (p0 p1 p2 : ℝ)
    (hp0 : 0<p0) (hp1 : 0<p1) (hp2 : 0<p2) (hne : p0≠p2)
    (hn : p0+p1+p2=1) (hshape : p1≤4*Real.sqrt (p0*p2)) :
    IsQuadraticProxy (threeMassCenteredLog p0 p1 p2)
      (2*(p0-p2)/Real.log (p0/p2)) := by
  intro t
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [threeMassCenteredLog_reflection p0 p1 p2 t hp0 hp1 hp2 hn]
    have h := threeMass_asymmetric_quadratic_bound p2 p1 p0 (-t)
      hp2 hp1 hp0 hlt (by linarith) (by simpa [mul_comm] using hshape)
    rw [threeMass_proxy_ratio_reflection p0 p2 hp0 hp2,neg_sq] at h
    exact h
  · exact threeMass_asymmetric_quadratic_bound p0 p1 p2 t hp0 hp1 hp2 hgt hn hshape

theorem threeMass_asymmetric_optimal_proxy (p0 p1 p2 : ℝ)
    (hp0 : 0<p0) (hp1 : 0<p1) (hp2 : 0<p2) (hne : p0≠p2)
    (hn : p0+p1+p2=1) (hshape : p1≤4*Real.sqrt (p0*p2)) :
    IsOptimalQuadraticProxy (threeMassCenteredLog p0 p1 p2)
      (2*(p0-p2)/Real.log (p0/p2)) := by
  have hlog : Real.log (p0/p2)≠0 := by
    intro h
    have hr := congrArg Real.exp h
    rw [Real.exp_log (div_pos hp0 hp2),Real.exp_zero] at hr
    have he : p0=p2 := (div_eq_one_iff_eq (ne_of_gt hp2)).mp hr
    exact hne he
  exact optimalQuadraticProxy_of_contact _ _ (Real.log (p0/p2))
    (threeMass_asymmetric_proxy_upper p0 p1 p2 hp0 hp1 hp2 hne hn hshape)
    hlog (threeMass_candidate_proxy_equality p0 p1 p2 hp0 hp2 hn hlog)

/-- Decreasing even curvature is maximal at the origin. -/
theorem logCoshMassSecond_le_zero (A B t : ℝ)
    (hA : 0<A) (hB : 0<B) (hAB : A≤2*B) :
    logCoshMassSecond A B t≤logCoshMassSecond A B 0 := by
  have hc : Continuous (logCoshMassSecond A B) :=
    continuous_iff_continuousAt.mpr (fun x => (logCoshMassSecond_hasDerivAt A B x hA hB).continuousAt)
  have hanti : AntitoneOn (logCoshMassSecond A B) (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hc.continuousOn
      (fun x _ => (logCoshMassSecond_hasDerivAt A B x hA hB).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Ici] at hx
    rw [(logCoshMassSecond_hasDerivAt A B x hA hB).deriv]
    exact logCoshMassThird_nonpos A B x hA hB hAB (le_of_lt hx)
  by_cases ht : 0≤t
  · exact hanti (by simp) ht ht
  · have h := hanti (by simp)
      (show -t∈Ici 0 by change 0≤-t; linarith) (by linarith : 0≤-t)
    simpa only [logCoshMassSecond,Real.cosh_neg] using h

/-- A curvature bound with zero value and slope gives a whole-line proxy. -/
theorem quadraticProxy_of_derivative_bound (ψ dψ ddψ : ℝ → ℝ) (C : ℝ)
    (hd : ∀t,HasDerivAt ψ (dψ t) t) (hdd : ∀t,HasDerivAt dψ (ddψ t) t)
    (h0 : ψ 0=0) (hd0 : dψ 0=0) (hbound : ∀t,ddψ t≤C) :
    IsQuadraticProxy ψ C := by
  let g := fun t => C*t^2/2-ψ t
  let dg := fun t => C*t-dψ t
  have hg (t : ℝ) : HasDerivAt g (dg t) t := by
    have h := ((((hasDerivAt_id t).pow 2).const_mul C).div_const 2).sub (hd t)
    convert h using 1 <;> try rfl
    norm_num only [Nat.cast_ofNat,pow_one,id_eq]
    dsimp [dg]
    ring
  have hdg (t : ℝ) : HasDerivAt dg (C-ddψ t) t := by
    have h := ((hasDerivAt_id t).const_mul C).sub (hdd t)
    convert h using 1 <;> try rfl
    simp only [mul_one]
  have hconv : ConvexOn ℝ univ g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
      ((continuous_iff_continuousAt.mpr (fun t => (hg t).continuousAt)).continuousOn)
      (fun t _ => (hg t).hasDerivWithinAt)
      (fun t _ => (hdg t).hasDerivWithinAt)
    intro t _
    exact sub_nonneg.mpr (hbound t)
  intro t
  apply quadratic_envelope_of_convex_gap ψ C hconv _ h0 t
  simpa [dg,hd0] using hg 0

theorem logCoshMass_origin_proxy (A B : ℝ)
    (hA : 0<A) (hB : 0<B) (hAB : A≤2*B) :
    IsQuadraticProxy (fun t => logCoshMass A B t-logCoshMass A B 0)
      (B/(A+B)) := by
  apply quadraticProxy_of_derivative_bound _ (logCoshMassFirst A B)
    (logCoshMassSecond A B) (B/(A+B))
  · intro t
    exact (logCoshMass_hasDerivAt A B t hA hB).sub_const _
  · exact fun t => logCoshMassFirst_hasDerivAt A B t hA hB
  · simp
  · simp [logCoshMassFirst]
  · intro t
    have h := logCoshMassSecond_le_zero A B t hA hB hAB
    have heq : logCoshMassSecond A B 0=B/(A+B) := by
      simp only [logCoshMassSecond,Real.cosh_zero,mul_one]
      field_simp
    rwa [heq] at h

theorem threeMass_balanced_centered_log (p q t : ℝ)
    (hp : 0<p) (hq : 0<q) (hn : p+q+p=1) :
    threeMassCenteredLog p q p t=logCoshMass q (2*p) t := by
  have hrep := threeMassMGF_cosh_representation p q p (2*p) 0 t
    (by simp) (by simp)
  simp only [sub_zero] at hrep
  unfold threeMassCenteredLog
  rw [hrep,Real.log_mul (Real.exp_ne_zero _)
    (ne_of_gt (by positivity : 0<q+2*p*Real.cosh t)),Real.log_exp]
  unfold logCoshMass
  linear_combination -t*hn

theorem threeMass_balanced_proxy_upper (p q : ℝ)
    (hp : 0<p) (hq : 0<q) (hn : p+q+p=1) (hshape : q≤4*p) :
    IsQuadraticProxy (threeMassCenteredLog p q p) (2*p) := by
  have h := logCoshMass_origin_proxy q (2*p) hq (by positivity) (by linarith)
  intro t
  rw [threeMass_balanced_centered_log p q t hp hq hn]
  have hn' : q+2*p=1 := by linarith
  have ht := h t
  simpa [logCoshMass,hn'] using ht

/-- The second-order quotient limit is a necessary lower bound on every proxy. -/
theorem quadraticProxy_lower_of_quotient_limit (ψ : ℝ → ℝ) (L D : ℝ)
    (hlim : Tendsto (fun t => ψ t/t^2) (𝓝[≠] (0:ℝ)) (𝓝 (L/2)))
    (hD : IsQuadraticProxy ψ D) : L≤D := by
  have hle : L/2≤D/2 := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t≠0 := ht
    apply (div_le_iff₀ (sq_pos_of_ne_zero ht0)).mpr
    have h := hD t
    nlinarith
  linarith

/-- The full three-mass formula, including the continuous balanced branch. -/
theorem threeMass_proxy_upper (p0 p1 p2 : ℝ)
    (hp0 : 0<p0) (hp1 : 0<p1) (hp2 : 0<p2)
    (hn : p0+p1+p2=1) (hshape : p1≤4*Real.sqrt (p0*p2)) :
    IsQuadraticProxy (threeMassCenteredLog p0 p1 p2) (threeMassProxy p0 p2) := by
  by_cases heq : p0=p2
  · subst p2
    simp only [threeMassProxy]
    apply threeMass_balanced_proxy_upper p0 p1 hp0 hp1 hn
    simpa only [Real.sqrt_mul_self hp0.le] using hshape
  · rw [threeMassProxy,if_neg heq]
    exact threeMass_asymmetric_proxy_upper p0 p1 p2 hp0 hp1 hp2 heq hn hshape

/-- The all-orientation, balanced-inclusive upper bound for actual two-draw laws. -/
theorem hypergeom_two_draw_proxy_upper_full (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) :
    IsQuadraticProxy (fun t => Real.log (hypergeomMGF N k 2 t)-2*(k:ℝ)/(N:ℝ)*t)
      (threeMassProxy (hypergeomMass N k 2 0) (hypergeomMass N k 2 2)) := by
  have hkle : k≤N := by omega
  have hN : 2≤N := by omega
  obtain ⟨hp0,hp1,hp2,hshape⟩ := hypergeom_two_draw_threeMass_admissible N k hk hNk
  have hn : hypergeomMass N k 2 0+hypergeomMass N k 2 1+
      hypergeomMass N k 2 2=1 := by
    simpa [Finset.sum_range_succ] using hypergeomMass_total N k 2 hkle hN
  have h := threeMass_proxy_upper _ _ _ hp0 hp1 hp2 hn hshape
  intro t
  dsimp only
  rw [hypergeom_two_draw_mgf_threeMass,←hypergeom_two_draw_mass_mean N k hkle hN]
  exact h t

/-- The balanced coefficient is necessary, by the genuine second-order limit. -/
theorem threeMass_balanced_optimal_proxy (p q : ℝ)
    (hp : 0<p) (hq : 0<q) (hn : p+q+p=1) (hshape : q≤4*p) :
    IsOptimalQuadraticProxy (threeMassCenteredLog p q p) (2*p) := by
  refine ⟨threeMass_balanced_proxy_upper p q hp hq hn hshape,?_⟩
  intro D hD
  have hn' : q+2*p=1 := by linarith
  have hd (t : ℝ) : HasDerivAt (logCoshMass q (2*p))
      (logCoshMassFirst q (2*p) t) t :=
    logCoshMass_hasDerivAt q (2*p) t hq (by positivity)
  have hdd : HasDerivAt (logCoshMassFirst q (2*p)) (2*p) 0 := by
    have h := logCoshMassFirst_hasDerivAt q (2*p) 0 hq (by positivity)
    simpa only [logCoshMassSecond,Real.cosh_zero,mul_one,hn',one_pow,div_one] using h
  have hf0 : logCoshMass q (2*p) 0=0 := by simp [logCoshMass,hn']
  have hdf0 : logCoshMassFirst q (2*p) 0=0 := by simp [logCoshMassFirst]
  have hlim := quadratic_quotient_limit hd hdd hf0 hdf0
  have heq : threeMassCenteredLog p q p=logCoshMass q (2*p) := by
    funext t
    exact threeMass_balanced_centered_log p q t hp hq hn
  rw [heq] at hD
  exact quadraticProxy_lower_of_quotient_limit _ (2*p) D hlim hD

/-- The AAM three-mass proxy formula is the least global quadratic coefficient. -/
theorem threeMass_optimal_proxy (p0 p1 p2 : ℝ)
    (hp0 : 0<p0) (hp1 : 0<p1) (hp2 : 0<p2)
    (hn : p0+p1+p2=1) (hshape : p1≤4*Real.sqrt (p0*p2)) :
    IsOptimalQuadraticProxy (threeMassCenteredLog p0 p1 p2) (threeMassProxy p0 p2) := by
  by_cases heq : p0=p2
  · subst p2
    simp only [threeMassProxy]
    exact threeMass_balanced_optimal_proxy p0 p1 hp0 hp1 hn
      (by simpa only [Real.sqrt_mul_self hp0.le] using hshape)
  · rw [threeMassProxy,if_neg heq]
    exact threeMass_asymmetric_optimal_proxy p0 p1 p2 hp0 hp1 hp2 heq hn hshape

/-- Actual two-draw hypergeometric laws have the stated least proxy in all orientations. -/
theorem hypergeom_two_draw_optimal_proxy (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) :
    IsOptimalQuadraticProxy
      (fun t => Real.log (hypergeomMGF N k 2 t)-2*(k:ℝ)/(N:ℝ)*t)
      (threeMassProxy (hypergeomMass N k 2 0) (hypergeomMass N k 2 2)) := by
  have hkle : k≤N := by omega
  have hN : 2≤N := by omega
  obtain ⟨hp0,hp1,hp2,hshape⟩ := hypergeom_two_draw_threeMass_admissible N k hk hNk
  have hn : hypergeomMass N k 2 0+hypergeomMass N k 2 1+
      hypergeomMass N k 2 2=1 := by
    simpa [Finset.sum_range_succ] using hypergeomMass_total N k 2 hkle hN
  have heq : (fun t => Real.log (hypergeomMGF N k 2 t)-2*(k:ℝ)/(N:ℝ)*t)=
      threeMassCenteredLog (hypergeomMass N k 2 0)
        (hypergeomMass N k 2 1) (hypergeomMass N k 2 2) := by
    funext t
    rw [hypergeom_two_draw_mgf_threeMass,←hypergeom_two_draw_mass_mean N k hkle hN]
    rfl
  rw [heq]
  exact threeMass_optimal_proxy _ _ _ hp0 hp1 hp2 hn hshape

end ExactHoeffding
