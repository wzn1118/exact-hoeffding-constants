import ExactHoeffding.RescaledQLimit
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # Strict global comparison for the limiting proxy -/

namespace ExactHoeffding

noncomputable section

open Set

local instance realAddCommGroup : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
local instance (priority := 10000) realModule : Module ℝ ℝ :=
  RCLike.toInnerProductSpaceReal.toModule

private def sinhGap (x : ℝ) : ℝ := x * Real.cosh x - Real.sinh x

private theorem sinhGap_continuous : Continuous sinhGap := by
  unfold sinhGap
  fun_prop

private theorem sinhGap_hasDerivAt (x : ℝ) :
    HasDerivAt sinhGap (x * Real.sinh x) x := by
  have h := (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
  have h' := h.sub (Real.hasDerivAt_sinh x)
  have hfun : (id * Real.cosh - Real.sinh) = sinhGap := by
    funext y
    simp [sinhGap, id, mul_comm]
  rw [← hfun]
  simpa [id, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'

private theorem sinhGap_pos {x : ℝ} (hx : 0 < x) : 0 < sinhGap x := by
  have hmono : StrictMonoOn sinhGap (Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    · exact sinhGap_continuous.continuousOn
    · intro y hy
      rw [interior_Ici, mem_Ioi] at hy
      rw [(sinhGap_hasDerivAt y).deriv]
      exact mul_pos hy (Real.sinh_pos_iff.mpr hy)
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp)
    (show x ∈ Ici 0 by exact hx.le) hx
  simpa [sinhGap] using h

private theorem tanh_lt_id_pos {x : ℝ} (hx : 0 < x) : Real.tanh x < x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  apply (div_lt_iff₀ (Real.cosh_pos x)).2
  have h := sinhGap_pos hx
  simpa [sinhGap, sub_pos, mul_comm] using h

private def logCoshGap (x : ℝ) : ℝ :=
  x ^ 2 / 2 - Real.log (Real.cosh x)

private theorem logCoshGap_continuous : Continuous logCoshGap := by
  unfold logCoshGap
  apply Continuous.sub
  · fun_prop
  · exact Real.continuous_cosh.log (fun x => ne_of_gt (Real.cosh_pos x))

private theorem logCoshGap_hasDerivAt (x : ℝ) :
    HasDerivAt logCoshGap (x - Real.tanh x) x := by
  change HasDerivAt (fun y : ℝ => y ^ 2 / 2 - Real.log (Real.cosh y))
    (x - Real.tanh x) x
  have hquad : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    simpa [pow_two] using ((hasDerivAt_id x).pow 2).div_const 2
  have hlog := (Real.hasDerivAt_cosh x).log (ne_of_gt (Real.cosh_pos x))
  have hsub := hquad.sub hlog
  have hfun :
      ((fun y : ℝ => y ^ 2 / 2) - (fun y => Real.log (Real.cosh y))) =
        (fun y : ℝ => y ^ 2 / 2 - Real.log (Real.cosh y)) := by
    funext y
    rfl
  rw [← hfun]
  simpa [realAddCommGroup, realModule, logCoshGap, Real.tanh_eq_sinh_div_cosh] using
    hsub

private theorem logCoshGap_pos {x : ℝ} (hx : 0 < x) : 0 < logCoshGap x := by
  have hmono : StrictMonoOn logCoshGap (Ici (0 : ℝ)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici (0 : ℝ))
    · exact logCoshGap_continuous.continuousOn
    · intro y hy
      rw [interior_Ici, mem_Ioi] at hy
      rw [(logCoshGap_hasDerivAt y).deriv]
      linarith [tanh_lt_id_pos hy]
  have h := hmono (show (0 : ℝ) ∈ Ici 0 by simp)
    (show x ∈ Ici 0 by exact hx.le) hx
  simpa [logCoshGap] using h

theorem real_log_cosh_lt_sq_div_two {x : ℝ} (hx : x ≠ 0) :
    Real.log (Real.cosh x) < x ^ 2 / 2 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hpos : 0 < -x := neg_pos.mpr hxneg
    have h := logCoshGap_pos hpos
    simpa [logCoshGap, Real.cosh_neg, neg_sq] using h
  · have h := logCoshGap_pos hxpos
    simpa [logCoshGap] using h

theorem limiting_proxy_strict (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : t ≠ 0) :
    2 * (m : ℝ) * Real.log (Real.cosh (t / 2)) / t ^ 2 <
      (m : ℝ) / 4 := by
  have harg : t / 2 ≠ 0 := by exact div_ne_zero ht (by norm_num)
  have hlog := real_log_cosh_lt_sq_div_two harg
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have h2m : 0 < 2 * (m : ℝ) := by nlinarith
  have hmul := mul_lt_mul_of_pos_left hlog h2m
  apply (div_lt_iff₀ ht2).2
  calc
    2 * (m : ℝ) * Real.log (Real.cosh (t / 2)) <
        2 * (m : ℝ) * ((t / 2) ^ 2 / 2) := hmul
    _ = (m : ℝ) / 4 * t ^ 2 := by ring

end

end ExactHoeffding
