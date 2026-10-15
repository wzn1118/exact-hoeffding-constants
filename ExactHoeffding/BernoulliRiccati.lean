import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ExactHoeffding

noncomputable def scaledBernoulliDenom (p a t : ℝ) : ℝ :=
  1 - p + p * Real.exp (a * t)

noncomputable def scaledBernoulliMean (M p a t : ℝ) : ℝ :=
  M / a * (p * Real.exp (a * t) / scaledBernoulliDenom p a t - p)

noncomputable def scaledBernoulliLogLaplace (M p a t : ℝ) : ℝ :=
  M / a^2 * (Real.log (scaledBernoulliDenom p a t) - p * a * t)

theorem scaledBernoulliDenom_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (a t : ℝ) :
    0 < scaledBernoulliDenom p a t := by
  unfold scaledBernoulliDenom
  exact add_pos (sub_pos.mpr hp1) (mul_pos hp0 (Real.exp_pos _))

theorem scaledBernoulliDenom_hasDerivAt (p a t : ℝ) :
    HasDerivAt (scaledBernoulliDenom p a)
      (p * (Real.exp (a * t) * a)) t := by
  unfold scaledBernoulliDenom
  have hlin : HasDerivAt (fun s : ℝ => a*s) a t := hasDerivAt_const_mul a
  exact ((hlin.exp.const_mul p).const_add (1-p))

theorem scaledBernoulliMean_hasDerivAt
    {M p a : ℝ} (hM : M ≠ 0) (ha : a ≠ 0) (hp0 : 0 < p) (hp1 : p < 1) (t : ℝ) :
    HasDerivAt (scaledBernoulliMean M p a)
      (M*p*(1-p) + a*(1-2*p)*scaledBernoulliMean M p a t -
        a^2/M*(scaledBernoulliMean M p a t)^2) t := by
  have hD : scaledBernoulliDenom p a t ≠ 0 :=
    (scaledBernoulliDenom_pos hp0 hp1 a t).ne'
  have hn := ((hasDerivAt_id t).const_mul a).exp.const_mul p
  have hd := scaledBernoulliDenom_hasDerivAt p a t
  have hcalc := ((hn.div hd hD).sub_const p).const_mul (M/a)
  apply hcalc.congr_deriv
  unfold scaledBernoulliMean scaledBernoulliDenom at *
  simp only [id_eq, mul_one]
  field_simp [hM, ha, hD]
  ring

theorem scaledBernoulliLogLaplace_hasDerivAt
    {M p a : ℝ} (ha : a ≠ 0) (hp0 : 0 < p) (hp1 : p < 1) (t : ℝ) :
    HasDerivAt (scaledBernoulliLogLaplace M p a) (scaledBernoulliMean M p a t) t := by
  have hD : scaledBernoulliDenom p a t ≠ 0 :=
    (scaledBernoulliDenom_pos hp0 hp1 a t).ne'
  have hd := scaledBernoulliDenom_hasDerivAt p a t
  have hlin : HasDerivAt (fun t : ℝ => p*a*t) (p*a) t := hasDerivAt_const_mul (p*a)
  have hcalc := ((hd.log hD).sub hlin).const_mul (M/a^2)
  apply hcalc.congr_deriv
  unfold scaledBernoulliMean
  field_simp [ha, hD]

@[simp] theorem scaledBernoulliMean_zero (M p a : ℝ) :
    scaledBernoulliMean M p a 0 = 0 := by
  simp [scaledBernoulliMean, scaledBernoulliDenom]

@[simp] theorem scaledBernoulliLogLaplace_zero (M p a : ℝ) :
    scaledBernoulliLogLaplace M p a 0 = 0 := by
  simp [scaledBernoulliLogLaplace, scaledBernoulliDenom]

@[simp] theorem scaledBernoulliMean_probability_zero (M a t : ℝ) :
    scaledBernoulliMean M 0 a t = 0 := by
  simp [scaledBernoulliMean, scaledBernoulliDenom]

@[simp] theorem scaledBernoulliMean_probability_one (M a t : ℝ) :
    scaledBernoulliMean M 1 a t = 0 := by
  simp [scaledBernoulliMean, scaledBernoulliDenom, Real.exp_ne_zero]

@[simp] theorem scaledBernoulliLogLaplace_probability_zero (M a t : ℝ) :
    scaledBernoulliLogLaplace M 0 a t = 0 := by
  simp [scaledBernoulliLogLaplace, scaledBernoulliDenom]

@[simp] theorem scaledBernoulliLogLaplace_probability_one (M a t : ℝ) :
    scaledBernoulliLogLaplace M 1 a t = 0 := by
  simp [scaledBernoulliLogLaplace, scaledBernoulliDenom, Real.log_exp]

theorem scaledBernoulliMean_continuous
    {M p a : ℝ} (hM : M ≠ 0) (ha : a ≠ 0) (hp0 : 0 < p) (hp1 : p < 1) :
    Continuous (scaledBernoulliMean M p a) :=
  continuous_iff_continuousAt.mpr fun t =>
    (scaledBernoulliMean_hasDerivAt hM ha hp0 hp1 t).continuousAt

theorem scaledBernoulliLogLaplace_continuous
    {M p a : ℝ} (ha : a ≠ 0) (hp0 : 0 < p) (hp1 : p < 1) :
    Continuous (scaledBernoulliLogLaplace M p a) :=
  continuous_iff_continuousAt.mpr fun t =>
    (scaledBernoulliLogLaplace_hasDerivAt ha hp0 hp1 t).continuousAt

noncomputable def balancedBernoulliMean (M p t : ℝ) : ℝ := M*p*(1-p)*t

noncomputable def balancedBernoulliLogLaplace (M p t : ℝ) : ℝ := M*p*(1-p)*t^2/2

theorem balancedBernoulliMean_hasDerivAt (M p t : ℝ) :
    HasDerivAt (balancedBernoulliMean M p) (M*p*(1-p)) t :=
  hasDerivAt_const_mul _

theorem balancedBernoulliMean_riccati (M p t : ℝ) :
    HasDerivAt (balancedBernoulliMean M p)
      (M*p*(1-p) + (0:ℝ)*(1-2*p)*balancedBernoulliMean M p t -
        (0:ℝ)^2/M*(balancedBernoulliMean M p t)^2) t := by
  simpa using balancedBernoulliMean_hasDerivAt M p t

theorem balancedBernoulliLogLaplace_hasDerivAt (M p t : ℝ) :
    HasDerivAt (balancedBernoulliLogLaplace M p) (balancedBernoulliMean M p t) t := by
  have hcalc := (((hasDerivAt_id t).pow 2).const_mul (M*p*(1-p))).div_const 2
  apply hcalc.congr_deriv
  unfold balancedBernoulliMean
  simp only [id_eq]
  ring

@[simp] theorem balancedBernoulliMean_zero (M p : ℝ) : balancedBernoulliMean M p 0 = 0 := by
  simp [balancedBernoulliMean]

@[simp] theorem balancedBernoulliLogLaplace_zero (M p : ℝ) :
    balancedBernoulliLogLaplace M p 0 = 0 := by
  simp [balancedBernoulliLogLaplace]

theorem balancedBernoulliMean_continuous (M p : ℝ) :
    Continuous (balancedBernoulliMean M p) :=
  continuous_iff_continuousAt.mpr fun t =>
    (balancedBernoulliMean_hasDerivAt M p t).continuousAt

theorem balancedBernoulliLogLaplace_continuous (M p : ℝ) :
    Continuous (balancedBernoulliLogLaplace M p) :=
  continuous_iff_continuousAt.mpr fun t =>
    (balancedBernoulliLogLaplace_hasDerivAt M p t).continuousAt


end ExactHoeffding
