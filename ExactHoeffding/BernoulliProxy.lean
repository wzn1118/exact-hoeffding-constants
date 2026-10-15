import ExactHoeffding.BernoulliKL
import ExactHoeffding.TwoDrawProxy
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Bernoulli quadratic proxy: the balanced case

The general sharp coefficient requires the two-contact-point argument from
the manuscript.  This file first closes the balanced case without assuming
that argument: the centered Bernoulli log-MGF becomes `log (cosh (t/2))`, and
Mathlib's kernel-checked `cosh_le_exp_half_sq` supplies the global quadratic
bound.  The equality-at-zero statement is kept explicit.
-/

namespace ExactHoeffding

theorem bernoulli_half_mgf_factorization (t : ℝ) :
    bernoulliMGF (1 / 2 : ℝ) t =
      Real.exp (t / 2) * Real.cosh (t / 2) := by
  unfold bernoulliMGF
  rw [Real.cosh_eq]
  rw [Real.exp_neg]
  have ht : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [ht]
  field_simp [Real.exp_ne_zero]
  ring

theorem bernoulli_half_centered_log_mgf_eq_log_cosh (t : ℝ) :
    bernoulliCenteredLogMGF (1 / 2 : ℝ) t =
      Real.log (Real.cosh (t / 2)) := by
  rw [bernoulliCenteredLogMGF, bernoulli_half_mgf_factorization,
    Real.log_mul (Real.exp_pos (t / 2)).ne' (Real.cosh_pos _).ne',
    Real.log_exp]
  ring

/-- Balanced Bernoulli has the global Hoeffding quadratic bound with coefficient
`1/4`, proved through the exact centered `log cosh` representation. -/
theorem bernoulli_half_quadratic_bound (t : ℝ) :
    bernoulliCenteredLogMGF (1 / 2 : ℝ) t ≤ (1 / 4 : ℝ) * t ^ 2 / 2 := by
  rw [bernoulli_half_centered_log_mgf_eq_log_cosh]
  have hcosh := Real.cosh_le_exp_half_sq (t / 2)
  have hlog := Real.log_le_log (Real.cosh_pos (t / 2)) hcosh
  rw [Real.log_exp] at hlog
  nlinarith

theorem bernoulli_half_quadratic_bound_at_zero :
    bernoulliCenteredLogMGF (1 / 2 : ℝ) 0 =
      (1 / 4 : ℝ) * (0 : ℝ) ^ 2 / 2 := by
  simp [bernoulliCenteredLogMGF, bernoulliMGF]

theorem bernoulli_mgf_pos (p t : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < bernoulliMGF p t := by
  unfold bernoulliMGF
  exact add_pos (sub_pos.mpr hp1) (mul_pos hp (Real.exp_pos _))

theorem bernoulli_mgf_cosh_factorization (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) :
    bernoulliMGF p t *
        Real.cosh (Real.log ((1 - p) / p) / 2) =
      Real.exp (t / 2) *
        Real.cosh ((t - Real.log ((1 - p) / p)) / 2) := by
  let α : ℝ := Real.log ((1 - p) / p)
  have hα : 0 < α := by
    dsimp [α]
    exact Real.log_pos (by
      apply (lt_div_iff₀ hp).2
      linarith)
  have heα : Real.exp α = (1 - p) / p := by
    exact Real.exp_log (div_pos (sub_pos.mpr (by linarith)) hp)
  have hhalf : Real.exp α =
      Real.exp (α / 2) * Real.exp (α / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsq : 1 - p = p * (Real.exp (α / 2)) ^ 2 := by
    calc
      1 - p = p * Real.exp α := by
        rw [heα]
        field_simp [ne_of_gt hp]
      _ = p * (Real.exp (α / 2) * Real.exp (α / 2)) := by
        rw [hhalf]
      _ = p * (Real.exp (α / 2)) ^ 2 := by ring
  have ht : Real.exp t = Real.exp (t / 2) * Real.exp (t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have harg₁ : (t - α) / 2 = t / 2 + (-α / 2) := by ring
  have harg₂ : -((t - α) / 2) = -t / 2 + α / 2 := by ring
  unfold bernoulliMGF
  change
    (1 - p + p * Real.exp t) * Real.cosh (α / 2) =
      Real.exp (t / 2) * Real.cosh ((t - α) / 2)
  rw [Real.cosh_eq, Real.cosh_eq, harg₂, harg₁,
    Real.exp_add, Real.exp_add, Real.exp_neg, ht]
  have hneg_t : Real.exp (-t / 2) = (Real.exp (t / 2))⁻¹ := by
    rw [show -t / 2 = -(t / 2) by ring, Real.exp_neg]
  have hneg_a : Real.exp (-α / 2) = (Real.exp (α / 2))⁻¹ := by
    rw [show -α / 2 = -(α / 2) by ring, Real.exp_neg]
  rw [hneg_t, hneg_a]
  field_simp [Real.exp_ne_zero]
  have hnorm : p * ((Real.exp (α / 2)) ^ 2 + 1) = 1 := by
    nlinarith [hsq]
  nlinarith [hsq, hnorm]

theorem bernoulli_centered_log_mgf_cosh_representation (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) :
    bernoulliCenteredLogMGF p t =
      Real.log (Real.cosh ((t - Real.log ((1 - p) / p)) / 2)) -
        Real.log (Real.cosh (Real.log ((1 - p) / p) / 2)) +
          (1 - 2 * p) * t / 2 := by
  let α : ℝ := Real.log ((1 - p) / p)
  have hα : 0 < α := by
    dsimp [α]
    exact Real.log_pos (by
      apply (lt_div_iff₀ hp).2
      linarith)
  have hca : 0 < Real.cosh (α / 2) := Real.cosh_pos _
  have hcx : 0 < Real.cosh ((t - α) / 2) := Real.cosh_pos _
  have hm : 0 < bernoulliMGF p t := bernoulli_mgf_pos p t hp (by linarith)
  have hfactor := bernoulli_mgf_cosh_factorization p t hp hp1
  have hratio : bernoulliMGF p t =
      (Real.exp (t / 2) * Real.cosh ((t - α) / 2)) /
        Real.cosh (α / 2) := by
    exact (eq_div_iff hca.ne').2 hfactor
  unfold bernoulliCenteredLogMGF
  rw [hratio,
    Real.log_div (mul_ne_zero (Real.exp_pos _).ne' hcx.ne') hca.ne',
    Real.log_mul (Real.exp_pos _).ne' hcx.ne', Real.log_exp]
  dsimp [α]
  ring

theorem bernoulli_log_cosh_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (Real.cosh y)) (Real.tanh x) x := by
  simpa only [Real.tanh_eq_sinh_div_cosh] using
    (Real.hasDerivAt_cosh x).log (ne_of_gt (Real.cosh_pos x))

theorem bernoulli_tanh_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.tanh y)
      (1 / Real.cosh x ^ 2) x := by
  have hcosh : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hcosh
  have hfun : (fun y : ℝ => Real.tanh y) =
      (fun y => Real.sinh y) / (fun y => Real.cosh y) := by
    funext y
    simp only [Real.tanh_eq_sinh_div_cosh, Pi.div_apply]
  rw [hfun]
  apply h.congr_deriv
  field_simp [hcosh]
  rw [Real.cosh_sq_sub_sinh_sq]

theorem bernoulli_tanh_deriv_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 / Real.cosh y ^ 2)
      (-2 * Real.sinh x / Real.cosh x ^ 3) x := by
  have hcosh : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  have hden := (Real.hasDerivAt_cosh x).pow 2
  have h := (hasDerivAt_const x (1 : ℝ)).div hden (pow_ne_zero 2 hcosh)
  have hfun : (fun y : ℝ => 1 / Real.cosh y ^ 2) =
      (fun y => (1 : ℝ)) / (fun y => Real.cosh y) ^ 2 := by
    funext y
    rfl
  rw [hfun]
  apply h.congr_deriv
  simp only [Pi.pow_apply]
  field_simp [hcosh]
  ring

theorem bernoulli_tanh_ratio_antitone :
    AntitoneOn (fun x : ℝ => Real.tanh x / x) (Set.Ioi 0) := by
  have hconc : ConcaveOn ℝ (Set.Ici 0) (fun x : ℝ => Real.tanh x) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Ici 0)
      ((continuous_iff_continuousAt.mpr
        (fun x => (bernoulli_tanh_hasDerivAt x).continuousAt)).continuousOn)
      (fun x _ => (bernoulli_tanh_hasDerivAt x).hasDerivWithinAt)
      (fun x _ => (bernoulli_tanh_deriv_hasDerivAt x).hasDerivWithinAt)
    intro x hx
    rw [interior_Ici] at hx
    have hs : 0 ≤ Real.sinh x :=
      (Real.sinh_nonneg_iff).2 (le_of_lt hx)
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [hs]
    · positivity
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have h := hconc.neg.secant_mono (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show x ∈ Set.Ici 0 from le_of_lt hx)
    (show y ∈ Set.Ici 0 from le_of_lt hy)
    (ne_of_gt hx) (ne_of_gt hy) hxy
  simp only [Pi.neg_apply, Real.tanh_zero, zero_div, neg_zero, sub_zero,
    neg_div] at h
  linarith

theorem bernoulli_log_cosh_tangent_square (a x : ℝ) (ha : 0 < a) :
    Real.log (Real.cosh x) - Real.log (Real.cosh a) ≤
      Real.tanh a / (2 * a) * (x ^ 2 - a ^ 2) := by
  exact even_tangent_square_of_deriv_ratio_antitone
    (fun y : ℝ => Real.log (Real.cosh y)) Real.tanh
    (fun y => by simp [Real.cosh_neg])
    (fun y => bernoulli_log_cosh_hasDerivAt y)
    bernoulli_tanh_ratio_antitone a ha x

theorem bernoulli_quadratic_bound_lt_half
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1 / 2) (t : ℝ) :
    bernoulliCenteredLogMGF p t ≤
      (1 - 2 * p) / (2 * Real.log ((1 - p) / p)) * t ^ 2 / 2 := by
  let α : ℝ := Real.log ((1 - p) / p)
  have hα : 0 < α := by
    dsimp [α]
    exact Real.log_pos (by
      apply (lt_div_iff₀ hp).2
      linarith)
  have ha : 0 < α / 2 := by linarith
  have htan := bernoulli_log_cosh_tangent_square (α / 2) ((t - α) / 2) ha
  have htanha : Real.tanh (α / 2) = 1 - 2 * p := by
    rw [Real.tanh_eq]
    have heα : Real.exp α = (1 - p) / p := by
      exact Real.exp_log (div_pos (sub_pos.mpr (by linarith)) hp)
    have hhalf : Real.exp α =
        Real.exp (α / 2) * Real.exp (α / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsq : (Real.exp (α / 2)) ^ 2 = Real.exp α := by
      calc
        (Real.exp (α / 2)) ^ 2 =
            Real.exp (α / 2) * Real.exp (α / 2) := by ring
        _ = Real.exp α := hhalf.symm
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
    rw [hsq, heα]
    field_simp [ne_of_gt hp]
    ring
  rw [bernoulli_centered_log_mgf_cosh_representation p t hp hp1]
  change Real.log (Real.cosh ((t - α) / 2)) -
      Real.log (Real.cosh (α / 2)) + (1 - 2 * p) * t / 2 ≤
    (1 - 2 * p) / (2 * α) * t ^ 2 / 2
  rw [htanha] at htan
  calc
    Real.log (Real.cosh ((t - α) / 2)) - Real.log (Real.cosh (α / 2)) +
        (1 - 2 * p) * t / 2 ≤
        (1 - 2 * p) / (α / 2) *
          (((t - α) / 2) ^ 2 - (α / 2) ^ 2) / 2 +
        (1 - 2 * p) * t / 2 := by
          have h := add_le_add_right htan ((1 - 2 * p) * t / 2)
          convert h using 1 <;> ring
    _ = (1 - 2 * p) / (2 * α) * t ^ 2 / 2 := by
      field_simp [ne_of_gt hα]
      ring

end ExactHoeffding
