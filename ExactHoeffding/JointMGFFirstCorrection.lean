import ExactHoeffding.JointPopulationFirstCorrection

/-! # First inverse-population correction of the actual finite-law MGF -/

namespace ExactHoeffding
noncomputable section
open Filter Asymptotics
open scoped Topology

/-- Summing the first mass correction uses the two factorial moments of the
binomial generating polynomial, including the reflected factorial moment. -/
theorem binomial_population_correction_weight_sum (m : ℕ) (hm : 2 ≤ m)
    (p z : ℝ) (hp : p ≠ 0) (hq : 1-p ≠ 0) :
    (∑ i ∈ Finset.range (m+1),
      (((m.choose i : ℝ)*p^i*(1-p)^(m-i))/2 *
        ((m:ℝ)*((m:ℝ)-1) - (i:ℝ)*((i:ℝ)-1)/p -
          ((m-i:ℕ):ℝ)*(((m-i:ℕ):ℝ)-1)/(1-p))) * z^i) =
      ((m:ℝ)*((m:ℝ)-1)/2) *
        ((1-p+p*z)^m - (p*z^2+(1-p))*(1-p+p*z)^(m-2)) := by
  have h0 := binomial_mass_weight_sum m p (1-p) z
  have h2 := binomial_factorial_weight_sum m 2 hm p (1-p) z
  have hq2 := binomial_complement_factorial_weight_sum m hm p (1-p) z
  simp only [Nat.cast_descFactorial_two] at h2 hq2
  have hs : (∑ i ∈ Finset.range (m+1),
      (((m.choose i : ℝ)*p^i*(1-p)^(m-i))/2 *
        ((m:ℝ)*((m:ℝ)-1) - (i:ℝ)*((i:ℝ)-1)/p -
          ((m-i:ℕ):ℝ)*(((m-i:ℕ):ℝ)-1)/(1-p))) * z^i) =
      ((m:ℝ)*((m:ℝ)-1)/2) *
        (∑ i ∈ Finset.range (m+1), (m.choose i:ℝ)*p^i*(1-p)^(m-i)*z^i) -
      (1/(2*p)) * (∑ i ∈ Finset.range (m+1), (i:ℝ)*((i:ℝ)-1)*
        (m.choose i:ℝ)*p^i*(1-p)^(m-i)*z^i) -
      (1/(2*(1-p))) * (∑ i ∈ Finset.range (m+1), ((m-i:ℕ):ℝ)*
        (((m-i:ℕ):ℝ)-1)*(m.choose i:ℝ)*p^i*(1-p)^(m-i)*z^i) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hp, hq]
  rw [hs, h0, h2, hq2]
  rw [show p*z+(1-p)=1-p+p*z by ring]
  field_simp [hp, hq]
  ring

/-- At zero inverse population, the actual finite-law MGF is binomial. -/
theorem realMarginMGF_population_zero (m : ℕ) (p t : ℝ) :
    finiteMGF (Finset.range (m+1)) (realMarginMass m 0 p)
      (fun i => (i:ℝ)) t = (1-p+p*Real.exp t)^m := by
  unfold finiteMGF
  simp only [realMarginMass, scaledFalling_step_zero, one_pow, div_one]
  simp_rw [mul_comm t, Real.exp_nat_mul]
  exact binomial_mass_weight_sum m p (1-p) (Real.exp t)

/-- The actual MGF has the manuscript's closed first population derivative. -/
theorem realMarginMGF_hasDerivAt_population_zero (m : ℕ) (hm : 2 ≤ m)
    (p t : ℝ) (hp : p ≠ 0) (hq : 1-p ≠ 0) :
    HasDerivAt (fun e => finiteMGF (Finset.range (m+1)) (realMarginMass m e p)
      (fun i => (i:ℝ)) t)
      (((m:ℝ)*((m:ℝ)-1)/2) * ((1-p+p*Real.exp t)^m -
        (p*Real.exp (2*t)+(1-p))*(1-p+p*Real.exp t)^(m-2))) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.range (m+1))
    (fun i _ => (realMarginMass_hasDerivAt_population_zero m i p hp hq).mul_const
      (Real.exp (t*(i:ℝ))))
  change HasDerivAt (fun e => finiteMGF (Finset.range (m+1))
    (realMarginMass m e p) (fun i => (i:ℝ)) t) _ 0 at h
  apply h.congr_deriv
  simp_rw [mul_comm t, Real.exp_nat_mul]
  rw [binomial_population_correction_weight_sum m hm p (Real.exp t) hp hq]
  rw [show Real.exp (2*t)=(Real.exp t)^2 by rw [two_mul,Real.exp_add]; ring]


/-- The actual finite-law MGF is analytic in inverse population at the binomial
axis for every fixed success fraction and real tilt. -/
theorem realMarginMGF_analyticAt_population_zero (m : ℕ) (p t : ℝ) :
    AnalyticAt ℝ (fun e => finiteMGF (Finset.range (m+1)) (realMarginMass m e p)
      (fun i => (i:ℝ)) t) 0 := by
  unfold finiteMGF
  apply Finset.analyticAt_fun_sum
  intro i hi
  exact ((realMarginMass_joint_analytic m i (0,p) (by simp)).comp_of_eq
    (analyticAt_id.prod analyticAt_const) rfl).mul analyticAt_const

/-- First correction of the centered actual log-MGF, at arbitrary real tilt. -/
theorem realMarginCenteredLogMGF_hasDerivAt_population_zero (m : ℕ) (hm : 2 ≤ m)
    (p t : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun e => Real.log (finiteMGF (Finset.range (m+1))
      (realMarginMass m e p) (fun i => (i:ℝ)) t) - (m:ℝ)*p*t)
      (((m:ℝ)*((m:ℝ)-1)/2) *
        (1-(p*Real.exp (2*t)+(1-p))/(1-p+p*Real.exp t)^2)) 0 := by
  have hZ : 0 < 1-p+p*Real.exp t := by positivity
  have hM : finiteMGF (Finset.range (m+1)) (realMarginMass m 0 p)
      (fun i => (i:ℝ)) t ≠ 0 := by
    rw [realMarginMGF_population_zero]
    exact pow_ne_zero m hZ.ne'
  have h := ((realMarginMGF_hasDerivAt_population_zero m hm p t hp.ne'
    (sub_pos.mpr hp1).ne').log hM).sub_const ((m:ℝ)*p*t)
  apply h.congr_deriv
  rw [realMarginMGF_population_zero]
  have hpow : (1-p+p*Real.exp t)^m =
      (1-p+p*Real.exp t)^(m-2)*(1-p+p*Real.exp t)^2 := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  rw [hpow]
  field_simp [hZ.ne']

/-- The closed logarithmic correction has an analytic second-order remainder.
This is the expansion of the actual real-margin law, not a formal mass ansatz. -/
theorem realMarginCenteredLogMGF_first_population_analytic_expansion
    (m : ℕ) (hm : 2 ≤ m) (p t : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      (∀ e, Real.log (finiteMGF (Finset.range (m+1)) (realMarginMass m e p)
        (fun i => (i:ℝ)) t) - (m:ℝ)*p*t =
          (m:ℝ)*Real.log (1-p+p*Real.exp t) - (m:ℝ)*p*t +
          (((m:ℝ)*((m:ℝ)-1)/2) *
            (1-(p*Real.exp (2*t)+(1-p))/(1-p+p*Real.exp t)^2))*e + e^2*R e) ∧
      (fun e => Real.log (finiteMGF (Finset.range (m+1)) (realMarginMass m e p)
        (fun i => (i:ℝ)) t) - (m:ℝ)*p*t -
          ((m:ℝ)*Real.log (1-p+p*Real.exp t) - (m:ℝ)*p*t) -
          (((m:ℝ)*((m:ℝ)-1)/2) *
            (1-(p*Real.exp (2*t)+(1-p))/(1-p+p*Real.exp t)^2))*e)
        =O[𝓝 0] (fun e => e^2) := by
  have hZ : 0 < 1-p+p*Real.exp t := by positivity
  have hM : 0 < finiteMGF (Finset.range (m+1)) (realMarginMass m 0 p)
      (fun i => (i:ℝ)) t := by
    rw [realMarginMGF_population_zero]
    exact pow_pos hZ m
  have han : AnalyticAt ℝ (fun e => Real.log (finiteMGF (Finset.range (m+1))
      (realMarginMass m e p) (fun i => (i:ℝ)) t) - (m:ℝ)*p*t) 0 :=
    ((analyticAt_log hM).comp_of_eq
      (realMarginMGF_analyticAt_population_zero m p t) rfl).sub analyticAt_const
  obtain ⟨R,hR,heq,hO⟩ := analytic_linear_remainder _ han
  have hz : Real.log (finiteMGF (Finset.range (m+1)) (realMarginMass m 0 p)
      (fun i => (i:ℝ)) t) - (m:ℝ)*p*t =
      (m:ℝ)*Real.log (1-p+p*Real.exp t) - (m:ℝ)*p*t := by
    rw [realMarginMGF_population_zero, Real.log_pow]
  have hd := (realMarginCenteredLogMGF_hasDerivAt_population_zero m hm p t hp hp1).deriv
  exact ⟨R,hR,by simpa only [hz,hd] using heq,by simpa only [hz,hd] using hO⟩


/-- The actual MGF itself has the same analytic second-order control. -/
theorem realMarginMGF_first_population_analytic_expansion (m : ℕ) (hm : 2 ≤ m)
    (p t : ℝ) (hp : p ≠ 0) (hq : 1-p ≠ 0) :
    ∃ R : ℝ → ℝ, AnalyticAt ℝ R 0 ∧
      (∀ e, finiteMGF (Finset.range (m+1)) (realMarginMass m e p)
        (fun i => (i:ℝ)) t = (1-p+p*Real.exp t)^m +
          (((m:ℝ)*((m:ℝ)-1)/2) * ((1-p+p*Real.exp t)^m -
            (p*Real.exp (2*t)+(1-p))*(1-p+p*Real.exp t)^(m-2)))*e + e^2*R e) ∧
      (fun e => finiteMGF (Finset.range (m+1)) (realMarginMass m e p)
        (fun i => (i:ℝ)) t - (1-p+p*Real.exp t)^m -
          (((m:ℝ)*((m:ℝ)-1)/2) * ((1-p+p*Real.exp t)^m -
            (p*Real.exp (2*t)+(1-p))*(1-p+p*Real.exp t)^(m-2)))*e)
        =O[𝓝 0] (fun e => e^2) := by
  obtain ⟨R,hR,heq,hO⟩ := analytic_linear_remainder _
    (realMarginMGF_analyticAt_population_zero m p t)
  have hd := (realMarginMGF_hasDerivAt_population_zero m hm p t hp hq).deriv
  exact ⟨R,hR,by simpa only [realMarginMGF_population_zero,hd] using heq,
    by simpa only [realMarginMGF_population_zero,hd] using hO⟩

end
end ExactHoeffding
