import ExactHoeffding.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Artanh

open Set

namespace ExactHoeffding

noncomputable def logOdds (x : ℝ) : ℝ := Real.log ((1+x)/(1-x))

theorem logOdds_hasDerivAt (x : ℝ) (hx : x∈Ioo (-1:ℝ) 1) :
    HasDerivAt logOdds (2/(1-x^2)) x := by
  have h1 : 1-x≠0 := ne_of_gt (by linarith [hx.2])
  have hplus : 1+x≠0 := ne_of_gt (by linarith [hx.1])
  have hsquare : 1-x^2≠0 := by nlinarith [hx.1,hx.2]
  have h2 : (1+x)/(1-x)≠0 := ne_of_gt (div_pos (by linarith [hx.1]) (by linarith [hx.2]))
  have hn := (hasDerivAt_id x).const_add 1
  have hd := (hasDerivAt_id x).const_sub 1
  have h := (hn.div hd h1).log h2
  convert h using 1 <;> try rfl
  simp only [Pi.div_apply,id_eq]
  field_simp
  ring

theorem logOdds_strictConvex : StrictConvexOn ℝ (Ico 0 1) logOdds := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ico 0 1)
  · intro x hx
    exact (logOdds_hasDerivAt x ⟨by linarith [hx.1],hx.2⟩).continuousAt.continuousWithinAt
  · intro x hx y hy hxy
    rw [interior_Ico] at hx hy
    rw [(logOdds_hasDerivAt x ⟨by linarith [hx.1],hx.2⟩).deriv,
      (logOdds_hasDerivAt y ⟨by linarith [hy.1],hy.2⟩).deriv]
    have hxpos : 0<1-x^2 := by nlinarith [hx.1,hx.2]
    have hypos : 0<1-y^2 := by nlinarith [hy.1,hy.2]
    apply (div_lt_div_iff₀ hxpos hypos).mpr
    have hsq := sq_lt_sq₀ (le_of_lt hx.1) (le_of_lt hy.1) |>.2 hxy
    nlinarith

theorem logOdds_ratio_strictMono : StrictMonoOn (fun x => logOdds x/x) (Ioo 0 1) := by
  intro x hx y hy hxy
  have h := logOdds_strictConvex.secant_strict_mono
    (show (0:ℝ)∈Ico 0 1 by simp) ⟨hx.1.le,hx.2⟩ ⟨hy.1.le,hy.2⟩
    (ne_of_gt hx.1) (ne_of_gt hy.1) hxy
  simpa [logOdds] using h

theorem artanh_ratio_strictMono : StrictMonoOn (fun x => Real.artanh x/x) (Ioo 0 1) := by
  intro x hx y hy hxy
  have h := logOdds_ratio_strictMono hx hy hxy
  dsimp only at h ⊢
  rw [Real.artanh_eq_half_log ⟨by linarith [hx.1],hx.2.le⟩,
    Real.artanh_eq_half_log ⟨by linarith [hy.1],hy.2.le⟩]
  dsimp [logOdds] at h
  convert mul_lt_mul_of_pos_left h (by norm_num : (0:ℝ)<1/2) using 1 <;> ring

/-- Dilating a positive argument strictly increases the normalized inverse tangent. -/
theorem logOdds_scale_strict (c d : ℝ) (hc : 1<c) (hd : 0<d) (hcd : c*d<1) :
    c*logOdds d<logOdds (c*d) := by
  have hcd0 : 0<c*d := mul_pos (by linarith) hd
  have hdlt : d<c*d := by nlinarith
  have hd1 : d<1 := lt_trans hdlt hcd
  have h := logOdds_ratio_strictMono ⟨hd,hd1⟩ ⟨hcd0,hcd⟩ hdlt
  have hm := (div_lt_div_iff₀ hd hcd0).mp h
  have heq : logOdds d*(c*d)=(c*logOdds d)*d := by ring
  rw [heq] at hm
  exact (mul_lt_mul_iff_left₀ hd).mp hm

end ExactHoeffding
