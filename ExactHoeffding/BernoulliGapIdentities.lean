import ExactHoeffding.BernoulliOptimal
import ExactHoeffding.BernoulliProxy
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Reflection and differential identities for the Bernoulli proxy gap -/

namespace ExactHoeffding
noncomputable section

def bernoulliProxyGap (p t : ℝ) : ℝ :=
  bernoulliSharpBeta p * t ^ 2 / 2 - bernoulliCenteredLogMGF p t

private theorem bernoulliSharpBeta_subhalf_formula (p : ℝ)
    (_hp : 0 < p) (hp1 : p < 1 / 2) :
    bernoulliSharpBeta p = (1-2*p)/(2*Real.log ((1-p)/p)) := by
  exact bernoulliSharpBeta_eq_formula p (by linarith)

private theorem bernoulliGap_tanh_half_logOdds (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) :
    Real.tanh (Real.log ((1-p)/p)/2) = 1-2*p := by
  let α : ℝ := Real.log ((1-p)/p)
  rw [Real.tanh_eq]
  have heα : Real.exp α = (1-p)/p := by
    exact Real.exp_log (div_pos (sub_pos.mpr (by linarith)) hp)
  have hhalf : Real.exp α = Real.exp (α/2) * Real.exp (α/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsq : (Real.exp (α/2))^2 = Real.exp α := by
    calc
      (Real.exp (α/2))^2 = Real.exp (α/2)*Real.exp (α/2) := by ring
      _ = Real.exp α := hhalf.symm
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  rw [hsq, heα]
  field_simp [hp.ne']
  ring

private theorem bernoulliGap_logOdds_pos (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) : 0 < Real.log ((1-p)/p) := by
  apply Real.log_pos
  apply (lt_div_iff₀ hp).2
  linarith

private theorem bernoulliGap_derivative_formula (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) :
    deriv (bernoulliProxyGap p) t =
      bernoulliSharpBeta p*t - Real.tanh ((t-Real.log ((1-p)/p))/2)/2 - (1-2*p)/2 := by
  let α : ℝ := Real.log ((1-p)/p)
  let d : ℝ := 1-2*p
  have hcosh : HasDerivAt (fun s : ℝ => Real.log (Real.cosh ((s-α)/2)))
      (Real.tanh ((t-α)/2)/2) t := by
    have hin : HasDerivAt (fun s : ℝ => (s-α)/2) (1/2) t := by
      simpa [id_eq] using (((hasDerivAt_id t).sub_const α).div_const (2:ℝ))
    have h := (bernoulli_log_cosh_hasDerivAt ((t-α)/2)).comp t hin
    have hfun : (fun s : ℝ => Real.log (Real.cosh ((s-α)/2))) =
        (fun s => (fun y : ℝ => Real.log (Real.cosh y)) ((s-α)/2)) := by
      funext s
      rfl
    have hderiv : Real.tanh ((t-α)/2) * (1/2) =
        Real.tanh ((t-α)/2)/2 := by ring
    exact (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => congrFun hfun s)).congr_deriv hderiv
  have hlinear : HasDerivAt (fun s : ℝ => d*s/2) (d/2) t := by
    simpa [id_eq, mul_comm, mul_left_comm, mul_assoc] using
      ((hasDerivAt_id t).mul_const d).div_const (2:ℝ)
  have hconstant : HasDerivAt (fun s : ℝ => Real.log (Real.cosh (α/2))) 0 t :=
    hasDerivAt_const _ _
  have hcg := hcosh.sub hconstant |>.add hlinear
  have hquad : HasDerivAt (fun s : ℝ => bernoulliSharpBeta p*s^2/2)
      (bernoulliSharpBeta p*t) t := by
    have hsq : HasDerivAt (fun s : ℝ => s^2) (2*t) t := by
      have h := (hasDerivAt_id t).pow 2
      have hfun : (fun s : ℝ => s^2) = (fun s => id s ^ 2) := by
        funext s
        rfl
      have hderiv : (2:ℝ) * id t ^ (2-1) * 1 = 2*t := by simp
      exact (h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => congrFun hfun s)).congr_deriv hderiv
    have h := hsq.const_mul (bernoulliSharpBeta p/2)
    have hfun : (fun s : ℝ => bernoulliSharpBeta p*s^2/2) =
        (fun s => bernoulliSharpBeta p/2*s^2) := by
      funext s
      ring
    have hderiv : bernoulliSharpBeta p/2*(2*t) = bernoulliSharpBeta p*t := by ring
    exact (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => congrFun hfun s)).congr_deriv hderiv
  have hf := hquad.sub hcg
  have hrep (s : ℝ) : bernoulliCenteredLogMGF p s =
      Real.log (Real.cosh ((s-α)/2))-Real.log (Real.cosh (α/2))+d*s/2 := by
    rw [bernoulli_centered_log_mgf_cosh_representation p s hp hp1]
  have hgap : bernoulliProxyGap p =
      (fun s : ℝ => bernoulliSharpBeta p*s^2/2) -
        ((fun s => Real.log (Real.cosh ((s-α)/2))) -
          (fun _ : ℝ => Real.log (Real.cosh (α/2))) +
          (fun s => d*s/2)) := by
    funext s
    simp only [bernoulliProxyGap, hrep]
    rfl
  rw [hgap, hf.deriv]
  dsimp [α, d]
  ring

theorem bernoulliProxyGap_reflection (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) :
    bernoulliProxyGap p (2*Real.log ((1-p)/p)-t) = bernoulliProxyGap p t := by
  let α : ℝ := Real.log ((1-p)/p)
  let d : ℝ := 1-2*p
  have hα : α ≠ 0 := ne_of_gt (bernoulliGap_logOdds_pos p hp hp1)
  have hbeta : bernoulliSharpBeta p = d/(2*α) := by
    dsimp [α,d]
    exact bernoulliSharpBeta_subhalf_formula p hp hp1
  have hrep (s : ℝ) : bernoulliCenteredLogMGF p s =
      Real.log (Real.cosh ((s-α)/2))-Real.log (Real.cosh (α/2))+d*s/2 := by
    rw [bernoulli_centered_log_mgf_cosh_representation p s hp hp1]
  have hcosh : Real.cosh ((2*α-t-α)/2) = Real.cosh ((t-α)/2) := by
    rw [show (2*α-t-α)/2 = -((t-α)/2) by ring, Real.cosh_neg]
  unfold bernoulliProxyGap
  rw [hrep (2*α-t), hrep t, hcosh, hbeta]
  field_simp [hα]
  ring

theorem bernoulliProxyGap_deriv_zero (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) :
    deriv (bernoulliProxyGap p) 0 = 0 := by
  rw [bernoulliGap_derivative_formula p 0 hp hp1]
  have ht := bernoulliGap_tanh_half_logOdds p hp hp1
  have hα := ne_of_gt (bernoulliGap_logOdds_pos p hp hp1)
  rw [show (0-Real.log ((1-p)/p))/2 = -(Real.log ((1-p)/p)/2) by ring,
    Real.tanh_neg, ht, bernoulliSharpBeta_subhalf_formula p hp hp1]
  field_simp [hα]
  ring

theorem bernoulliProxyGap_deriv_logOdds (p : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) :
    deriv (bernoulliProxyGap p) (Real.log ((1-p)/p)) = 0 := by
  let α : ℝ := Real.log ((1-p)/p)
  rw [bernoulliGap_derivative_formula p α hp hp1]
  have hα := ne_of_gt (bernoulliGap_logOdds_pos p hp hp1)
  rw [show (α-Real.log ((1-p)/p))/2 = 0 by dsimp [α]; ring,
    Real.tanh_zero, bernoulliSharpBeta_subhalf_formula p hp hp1]
  dsimp [α]
  field_simp [hα]
  ring

theorem bernoulliProxyGap_second_derivative (p t : ℝ)
    (hp : 0 < p) (hp1 : p < 1 / 2) :
    deriv (deriv (bernoulliProxyGap p)) t =
      bernoulliSharpBeta p -
        1/(4*Real.cosh ((t-Real.log ((1-p)/p))/2)^2) := by
  let α : ℝ := Real.log ((1-p)/p)
  have hfirst : deriv (bernoulliProxyGap p) = fun s : ℝ =>
      bernoulliSharpBeta p*s-Real.tanh ((s-α)/2)/2-(1-2*p)/2 := by
    funext s
    simpa [α] using bernoulliGap_derivative_formula p s hp hp1
  rw [hfirst]
  have hin : HasDerivAt (fun s : ℝ => (s-α)/2) (1/2) t := by
    simpa [id_eq] using (((hasDerivAt_id t).sub_const α).div_const (2:ℝ))
  have htanh := (bernoulli_tanh_hasDerivAt ((t-α)/2)).comp t hin
  have hterm : HasDerivAt (fun s : ℝ => Real.tanh ((s-α)/2)/2)
      (1/(4*Real.cosh ((t-α)/2)^2)) t := by
    have hC : Real.cosh ((t-α)/2)^2 ≠ 0 :=
      pow_ne_zero 2 ((Real.cosh_pos ((t-α)/2)).ne')
    have hfun : (fun s : ℝ => Real.tanh ((s-α)/2)/2) =
        (fun s => ((fun y : ℝ => Real.tanh y) ∘ (fun u => (u-α)/2)) s / 2) := by
      funext s
      rfl
    have hderiv : (1 / Real.cosh ((t-α)/2)^2 * (1/2))/2 =
        1/(4*Real.cosh ((t-α)/2)^2) := by
      field_simp [hC]
      ring
    exact (htanh.div_const (2:ℝ)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => congrFun hfun s) |>.congr_deriv hderiv
  have hlin := (hasDerivAt_id t).const_mul (bernoulliSharpBeta p)
  have hconst : HasDerivAt (fun s : ℝ => (1-2*p)/2) 0 t := hasDerivAt_const _ _
  have h := hlin.sub hterm |>.sub hconst
  have hfun : (fun y : ℝ => bernoulliSharpBeta p * id y) -
      (fun s => Real.tanh ((s-α)/2)/2) - (fun _ : ℝ => (1-2*p)/2) =
      (fun s : ℝ => bernoulliSharpBeta p*s - Real.tanh ((s-α)/2)/2 - (1-2*p)/2) := by
    funext s
    rfl
  rw [← hfun]
  rw [h.deriv]
  dsimp [α]
  ring

end
end ExactHoeffding
