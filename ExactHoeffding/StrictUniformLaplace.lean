import ExactHoeffding.AllParameterCurvatureEquality
import ExactHoeffding.UniformLaplace
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set Filter
open scoped Topology

namespace ExactHoeffding

/-- A nonnegative derivative which can vanish at only one point gives strict
monotonicity. The proof uses local constancy on any hypothetical flat interval. -/
theorem strictMono_of_nonneg_derivative_except_one
    {f df : ℝ → ℝ} (c : ℝ) (hd : ∀x, HasDerivAt f (df x) x)
    (hn : ∀x, 0≤df x) (hp : ∀x, x≠c → 0<df x) : StrictMono f := by
  have hmono : Monotone f := monotone_of_hasDerivAt_nonneg hd hn
  intro a b hab
  have hle := hmono hab.le
  by_contra hnot
  have heq : f a=f b := le_antisymm hle (le_of_not_gt hnot)
  obtain ⟨z,haz,hzb,hzc⟩ : ∃z, a<z ∧ z<b ∧ z≠c := by
    obtain ⟨z,haz,hzb⟩ := exists_between hab
    by_cases hzc : z=c
    · obtain ⟨w,haw,hwz⟩ := exists_between haz
      exact ⟨w,haw,hwz.trans hzb,by rw [← hzc]; exact hwz.ne⟩
    · exact ⟨z,haz,hzb,hzc⟩
  have hflat : ∀x∈Icc a b, f x=f a := by
    intro x hx
    exact le_antisymm (by simpa only [heq] using hmono hx.2) (hmono hx.1)
  have hz : f z=f a := hflat z ⟨haz.le,hzb.le⟩
  have hlocal : IsLocalMax f z := by
    filter_upwards [Ioo_mem_nhds haz hzb] with x hx
    rw [hflat x ⟨hx.1.le,hx.2.le⟩,hz]
  have hzero := hlocal.hasDerivAt_eq_zero (hd z)
  linarith [hp z hzc]

/-- A quadratic envelope is strict away from its centered contact whenever
the true curvature can meet its ceiling at at most one real argument. -/
theorem strict_quadratic_envelope_of_curvature_single_contact
    {F y v : ℝ → ℝ} (C c : ℝ)
    (hFd : ∀t, HasDerivAt F (y t) t) (hyd : ∀t, HasDerivAt y (v t) t)
    (hv : ∀t, v t≤C) (heq : ∀t, v t=C → t=c)
    (hF0 : F 0=0) (hy0 : y 0=0) :
    ∀t, t≠0 → F t<C*t^2/2 := by
  let G : ℝ→ℝ := fun t => C*t^2/2-F t
  let dG : ℝ→ℝ := fun t => C*t-y t
  have hGd : ∀t, HasDerivAt G (dG t) t := by
    intro t
    have hquad := (((hasDerivAt_id t).fun_pow 2).const_mul C).div_const 2
    have hcalc := hquad.sub (hFd t)
    have hcoeff : C*((2:ℝ)*t^(2-1)*1)/2-y t=C*t-y t := by ring
    simpa only [G,dG,id_eq] using! hcalc.congr_deriv hcoeff
  have hdGd : ∀t, HasDerivAt dG (C-v t) t := by
    intro t
    exact (hasDerivAt_const_mul C).sub (hyd t)
  have hstrict : StrictMono dG := strictMono_of_nonneg_derivative_except_one c hdGd
    (fun t => sub_nonneg.mpr (hv t)) (fun t ht => sub_pos.mpr
      (lt_of_le_of_ne (hv t) (fun he => ht (heq t he))))
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun t => (hGd t).continuousAt
  have hderiv : deriv G=dG := funext fun t => (hGd t).deriv
  have hconv : StrictConvexOn ℝ univ G :=
    StrictMono.strictConvexOn_univ_of_deriv hGc (by rw [hderiv]; exact hstrict)
  have hG0 : G 0=0 := by simp [G,hF0]
  have hGd0 : HasDerivAt G 0 0 := by simpa [dG,hy0] using hGd 0
  intro t ht
  have hpos : 0<G t := by
    rcases lt_or_gt_of_ne ht with hlt | hgt
    · have hs := hconv.slope_lt_of_hasDerivAt (mem_univ t) (mem_univ 0) hlt hGd0
      rw [slope_def_field,hG0] at hs
      have hnum : 0-G t<0 := by
        have hh := (div_lt_iff₀ (by linarith : 0<0-t)).mp hs
        simpa only [zero_mul] using hh
      linarith
    · have hs := hconv.lt_slope_of_hasDerivAt (mem_univ 0) (mem_univ t) hgt hGd0
      rw [slope_def_field,hG0,sub_zero,sub_zero] at hs
      exact (div_pos_iff_of_pos_right hgt).mp hs
  dsimp [G] at hpos
  linarith

/-- For any nondegenerate legal hypergeometric law, the sharp curvature
ceiling has at most one contact tilt. -/
theorem hypergeom_curvature_contact_unique (N k m : ℕ)
    (hk0 : 0<k) (hkN : k<N) (hm0 : 0<m) (hmN : m<N) :
    ∃c:ℝ, ∀t, hypergeomTiltVariance N k m t=sharpCurvatureConstant N k m → t=c := by
  by_cases hm1 : m=1
  · subst m
    exact ⟨Real.log (((N:ℝ)-k)/k),fun t ht =>
      (hypergeomTiltVariance_one_draw_equality_iff N k hk0 hkN t).mp ht⟩
  by_cases hk1 : k=1
  · subst k
    exact ⟨Real.log (((N:ℝ)-m)/m),fun t ht =>
      (hypergeomTiltVariance_one_mark_equality_iff N m hm0 hmN t).mp ht⟩
  by_cases hmc : m=N-1
  · subst m
    exact ⟨-Real.log (((N:ℝ)-k)/k),fun t ht =>
      (hypergeomTiltVariance_complement_one_draw_equality_iff N k hk0 hkN t).mp ht⟩
  by_cases hkc : k=N-1
  · subst k
    exact ⟨-Real.log (((N:ℝ)-m)/m),fun t ht =>
      (hypergeomTiltVariance_complement_one_mark_equality_iff N m hm0 hmN t).mp ht⟩
  exact ⟨0,fun t ht => (hypergeomTiltVariance_interior_equality_iff N k m
    (by omega) (by omega) (by omega) (by omega) t).mp ht |>.1⟩

/-- The universal sharp-curvature Laplace bound is strict for every nonzero
tilt of every nondegenerate hypergeometric law. -/
theorem hypergeom_uniform_log_laplace_domination_strict (N k m : ℕ)
    (hk0 : 0<k) (hkN : k<N) (hm0 : 0<m) (hmN : m<N) (t : ℝ) (ht : t≠0) :
    hypergeomCenteredLogMGF N k m t<sharpCurvatureConstant N k m*t^2/2 := by
  obtain ⟨c,hc⟩ := hypergeom_curvature_contact_unique N k m hk0 hkN hm0 hmN
  let y : ℝ→ℝ := fun s => hypergeomTiltMean N k m s-(m:ℝ)*(k:ℝ)/(N:ℝ)
  have hyd (s : ℝ) : HasDerivAt y (hypergeomTiltVariance N k m s) s :=
    (hypergeomTiltMean_hasDerivAt N k m hkN.le hmN.le s).sub_const _
  have hy0 : y 0=0 := by dsimp [y]; rw [hypergeomTiltMean_zero N k m hkN.le hmN.le]; ring
  exact strict_quadratic_envelope_of_curvature_single_contact (sharpCurvatureConstant N k m) c
    (hypergeomCenteredLogMGF_hasDerivAt N k m hkN.le hmN.le) hyd
    (hypergeomTiltVariance_sharp N k m hkN.le hmN.le) hc
    (hypergeomCenteredLogMGF_zero N k m hkN.le hmN.le) hy0 t ht

theorem hypergeom_uniform_log_laplace_domination_equality_iff (N k m : ℕ)
    (hk0 : 0<k) (hkN : k<N) (hm0 : 0<m) (hmN : m<N) (t : ℝ) :
    hypergeomCenteredLogMGF N k m t=sharpCurvatureConstant N k m*t^2/2 ↔ t=0 := by
  constructor
  · intro heq
    by_contra ht
    exact (ne_of_lt (hypergeom_uniform_log_laplace_domination_strict N k m
      hk0 hkN hm0 hmN t ht)) heq
  · rintro rfl
    simp [hypergeomCenteredLogMGF_zero N k m hkN.le hmN.le]

end ExactHoeffding
