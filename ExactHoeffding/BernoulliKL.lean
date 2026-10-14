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

theorem bernoulliKL_zero_endpoint (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    bernoulliKL p 0 = -Real.log (1 - p) := by
  simp [bernoulliKL, Real.log_inv]

theorem bernoulliKL_one_endpoint (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1) :
    bernoulliKL p 1 = -Real.log p := by
  simp [bernoulliKL, Real.log_inv]

end ExactHoeffding
