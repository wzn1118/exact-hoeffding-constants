import ExactHoeffding.Laplace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Bernoulli KL/Fenchel identities

This module isolates the exact algebra behind the Bernoulli Legendre rate.
It does not claim the finite-population comparison or the global quadratic
proxy theorem.  The interior identity records the exact finite optimizer;
the two endpoint identities use Lean's totalized `Real.log` convention.
-/

namespace ExactHoeffding

/-- Bernoulli relative entropy, with the totalized endpoint convention inherited
from `Real.log` and real multiplication. -/
noncomputable def bernoulliKL (p x : ℝ) : ℝ :=
  x * Real.log (x / p) + (1 - x) * Real.log ((1 - x) / (1 - p))

/-- The centered Bernoulli log-Laplace transform. -/
noncomputable def bernoulliCenteredLogMGF (p t : ℝ) : ℝ :=
  Real.log (bernoulliMGF p t) - p * t

/-- The finite tilt at which the Bernoulli Legendre transform is attained. -/
noncomputable def bernoulliFenchelTilt (p x : ℝ) : ℝ :=
  Real.log ((x * (1 - p)) / (p * (1 - x)))

/-- The Bernoulli parameter induced by an arbitrary exponential tilt. -/
noncomputable def bernoulliTiltedProb (p t : ℝ) : ℝ :=
  p * Real.exp t / bernoulliMGF p t

theorem bernoulli_centered_log_mgf_zero (p : ℝ) :
    bernoulliCenteredLogMGF p 0 = 0 := by
  simp [bernoulliCenteredLogMGF, bernoulliMGF]

theorem bernoulli_mgf_at_fenchel_tilt (p x : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1) :
    bernoulliMGF p (bernoulliFenchelTilt p x) = (1 - p) / (1 - x) := by
  have hnum : 0 < x * (1 - p) := mul_pos hx (sub_pos.mpr hp1)
  have hden : 0 < p * (1 - x) := mul_pos hp (sub_pos.mpr hx1)
  have hexp : Real.exp (bernoulliFenchelTilt p x) =
      (x * (1 - p)) / (p * (1 - x)) := by
    exact Real.exp_log (div_pos hnum hden)
  unfold bernoulliMGF
  rw [hexp]
  field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr hx1)]
  ring

theorem bernoulli_fenchel_identity (p x : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1) :
    bernoulliFenchelTilt p x * (x - p) -
        bernoulliCenteredLogMGF p (bernoulliFenchelTilt p x) =
      bernoulliKL p x := by
  have hpm : (1 - p) ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  have hxm : (1 - x) ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hlog_tilt :
      bernoulliFenchelTilt p x =
        Real.log x + Real.log (1 - p) - Real.log p - Real.log (1 - x) := by
    unfold bernoulliFenchelTilt
    rw [Real.log_div (mul_ne_zero hx.ne' hpm)
      (mul_ne_zero hp.ne' hxm),
      Real.log_mul hx.ne' hpm, Real.log_mul hp.ne' hxm]
    ring
  have hlog_mgf :
      Real.log (bernoulliMGF p (bernoulliFenchelTilt p x)) =
        Real.log (1 - p) - Real.log (1 - x) := by
    rw [bernoulli_mgf_at_fenchel_tilt p x hp hp1 hx hx1,
      Real.log_div hpm hxm]
  have hlog_xp : Real.log (x / p) = Real.log x - Real.log p := by
    exact Real.log_div hx.ne' hp.ne'
  have hlog_q :
      Real.log ((1 - x) / (1 - p)) =
        Real.log (1 - x) - Real.log (1 - p) := by
    exact Real.log_div hxm hpm
  unfold bernoulliCenteredLogMGF bernoulliKL
  rw [hlog_mgf, hlog_tilt, hlog_xp, hlog_q]
  ring

theorem bernoulliKL_nonneg (p x : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1) :
    0 ≤ bernoulliKL p x := by
  have hfirst := Real.log_le_sub_one_of_pos (div_pos hp hx)
  have hsecond := Real.log_le_sub_one_of_pos
    (div_pos (sub_pos.mpr hp1) (sub_pos.mpr hx1))
  have hfirst' := mul_le_mul_of_nonneg_left hfirst hx.le
  have hsecond' := mul_le_mul_of_nonneg_left hsecond
    (sub_pos.mpr hx1).le
  have hlog_first : Real.log (p / x) = -Real.log (x / p) := by
    have hinv : p / x = (x / p)⁻¹ := by
      field_simp [ne_of_gt hp, ne_of_gt hx]
    rw [hinv, Real.log_inv]
  have hlog_second :
      Real.log ((1 - p) / (1 - x)) =
        -Real.log ((1 - x) / (1 - p)) := by
    have hinv : (1 - p) / (1 - x) = ((1 - x) / (1 - p))⁻¹ := by
      field_simp [ne_of_gt (sub_pos.mpr hp1), ne_of_gt (sub_pos.mpr hx1)]
    rw [hinv, Real.log_inv]
  rw [hlog_first] at hfirst'
  rw [hlog_second] at hsecond'
  have hfirst'' :
      -x * Real.log (x / p) ≤ p - x := by
    calc
      -x * Real.log (x / p) = x * (-Real.log (x / p)) := by ring
      _ ≤ x * (p / x - 1) := hfirst'
      _ = p - x := by field_simp [ne_of_gt hx]
  have hsecond'' :
      -(1 - x) * Real.log ((1 - x) / (1 - p)) ≤ x - p := by
    calc
      -(1 - x) * Real.log ((1 - x) / (1 - p)) =
          (1 - x) * (-Real.log ((1 - x) / (1 - p))) := by ring
      _ ≤ (1 - x) * ((1 - p) / (1 - x) - 1) := hsecond'
      _ = x - p := by field_simp [ne_of_gt (sub_pos.mpr hx1)]; ring
  unfold bernoulliKL
  linarith

theorem bernoulli_tilted_prob_pos (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    0 < bernoulliTiltedProb p t := by
  unfold bernoulliTiltedProb bernoulliMGF
  apply div_pos
  · exact mul_pos hp (Real.exp_pos _)
  · exact add_pos (sub_pos.mpr hp1) (mul_pos hp (Real.exp_pos _))

theorem bernoulli_tilted_prob_lt_one (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    bernoulliTiltedProb p t < 1 := by
  have hM : 0 < bernoulliMGF p t := by
    unfold bernoulliMGF
    exact add_pos (sub_pos.mpr hp1) (mul_pos hp (Real.exp_pos _))
  apply (div_lt_iff₀ hM).2
  unfold bernoulliMGF
  linarith [sub_pos.mpr hp1]

theorem bernoulli_fenchel_gap_identity (p x t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1) :
    bernoulliKL p x -
        (x * t - Real.log (bernoulliMGF p t)) =
      bernoulliKL (bernoulliTiltedProb p t) x := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hxm : 0 < 1 - x := sub_pos.mpr hx1
  have hr : 0 < bernoulliTiltedProb p t :=
    bernoulli_tilted_prob_pos p t hp hp1
  have hr1 : bernoulliTiltedProb p t < 1 :=
    bernoulli_tilted_prob_lt_one p t hp hp1
  have hM : 0 < bernoulliMGF p t := by
    unfold bernoulliMGF
    exact add_pos hq (mul_pos hp (Real.exp_pos _))
  have hone :
      1 - bernoulliTiltedProb p t =
        (1 - p) / bernoulliMGF p t := by
    unfold bernoulliTiltedProb
    field_simp [ne_of_gt hM]
    unfold bernoulliMGF
    ring
  have hlog_r :
      Real.log (bernoulliTiltedProb p t) =
        Real.log p + t - Real.log (bernoulliMGF p t) := by
    unfold bernoulliTiltedProb
    rw [Real.log_div (mul_ne_zero hp.ne' (Real.exp_pos t).ne') hM.ne',
      Real.log_mul hp.ne' (Real.exp_pos t).ne', Real.log_exp]
  have hlog_one_r :
      Real.log (1 - bernoulliTiltedProb p t) =
        Real.log (1 - p) - Real.log (bernoulliMGF p t) := by
    rw [hone, Real.log_div hq.ne' hM.ne']
  have hlog_xp : Real.log (x / p) = Real.log x - Real.log p :=
    Real.log_div hx.ne' hp.ne'
  have hlog_xr :
      Real.log (x / bernoulliTiltedProb p t) =
        Real.log x - Real.log p - t + Real.log (bernoulliMGF p t) := by
    rw [Real.log_div hx.ne' hr.ne', hlog_r]
    ring
  have hlog_qp :
      Real.log ((1 - x) / (1 - p)) =
        Real.log (1 - x) - Real.log (1 - p) :=
    Real.log_div hxm.ne' hq.ne'
  have hlog_xr' :
      Real.log ((1 - x) / (1 - bernoulliTiltedProb p t)) =
        Real.log (1 - x) - Real.log (1 - p) +
          Real.log (bernoulliMGF p t) := by
    rw [Real.log_div hxm.ne' (sub_pos.mpr hr1).ne', hlog_one_r]
    ring
  unfold bernoulliKL
  rw [hlog_xr, hlog_xp, hlog_xr', hlog_qp]
  ring

theorem bernoulli_fenchel_upper_interior (p x t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1) :
    x * t - Real.log (bernoulliMGF p t) ≤ bernoulliKL p x := by
  have hgap := bernoulli_fenchel_gap_identity p x t hp hp1 hx hx1
  have hnonneg := bernoulliKL_nonneg (bernoulliTiltedProb p t) x
    (bernoulli_tilted_prob_pos p t hp hp1)
    (bernoulli_tilted_prob_lt_one p t hp hp1) hx hx1
  linarith

theorem bernoulliKL_zero_endpoint (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    bernoulliKL p 0 = -Real.log (1 - p) := by
  simp [bernoulliKL, Real.log_inv]

theorem bernoulliKL_one_endpoint (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    bernoulliKL p 1 = -Real.log p := by
  simp [bernoulliKL, Real.log_inv]

theorem bernoulli_fenchel_upper_zero (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    0 * t - Real.log (bernoulliMGF p t) ≤ bernoulliKL p 0 := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hM : 0 < bernoulliMGF p t := by
    unfold bernoulliMGF
    exact add_pos hq (mul_pos hp (Real.exp_pos _))
  have hle : 1 - p ≤ bernoulliMGF p t := by
    unfold bernoulliMGF
    linarith [mul_nonneg hp.le (Real.exp_pos t).le]
  have hlog := Real.log_le_log hq hle
  rw [bernoulliKL_zero_endpoint p hp hp1]
  linarith

theorem bernoulli_fenchel_upper_one (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    1 * t - Real.log (bernoulliMGF p t) ≤ bernoulliKL p 1 := by
  have hq : 0 < 1 - p := sub_pos.mpr hp1
  have hM : 0 < bernoulliMGF p t := by
    unfold bernoulliMGF
    exact add_pos hq (mul_pos hp (Real.exp_pos _))
  have hpe : 0 < p * Real.exp t := mul_pos hp (Real.exp_pos _)
  have hle : p * Real.exp t ≤ bernoulliMGF p t := by
    unfold bernoulliMGF
    linarith [hq]
  have hlog := Real.log_le_log hpe hle
  have hlog_pe : Real.log (p * Real.exp t) = Real.log p + t := by
    rw [Real.log_mul hp.ne' (Real.exp_pos t).ne', Real.log_exp]
  rw [hlog_pe] at hlog
  rw [bernoulliKL_one_endpoint p hp hp1]
  linarith

theorem bernoulli_fenchel_upper (p x t : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x * t - Real.log (bernoulliMGF p t) ≤ bernoulliKL p x := by
  rcases eq_or_lt_of_le hx0 with rfl | hx
  · exact bernoulli_fenchel_upper_zero p t hp hp1
  rcases lt_or_eq_of_le hx1 with hxlt | rfl
  · exact bernoulli_fenchel_upper_interior p x t hp hp1 hx hxlt
  · exact bernoulli_fenchel_upper_one p t hp hp1

end ExactHoeffding
