import ExactHoeffding.ActualNormalizedThirdCoefficient

/-! # Parity of analytic germs and their exact remainder orders -/
namespace ExactHoeffding
noncomputable section
open Filter Asymptotics
open scoped Topology

/-- An odd analytic germ has no quadratic Taylor coefficient. -/
theorem analytic_odd_germ_deriv2_zero (f:ℝ→ℝ)
    (hodd:∀ᶠ d in 𝓝 (0:ℝ), f (-d)= -f d) : iteratedDeriv 2 f 0=0 := by
  have heq : (fun d:ℝ=>f (-d)) =ᶠ[𝓝 0] (fun d=> -f d) := hodd
  have h := heq.iteratedDeriv_eq 2
  rw [iteratedDeriv_comp_neg,iteratedDeriv_fun_neg] at h
  norm_num at h
  linarith

/-- An even analytic germ has no first or third Taylor coefficient. -/
theorem analytic_even_germ_odd_derivatives (f:ℝ→ℝ)
    (heven:∀ᶠ d in 𝓝 (0:ℝ), f (-d)=f d) :
    deriv f 0=0 ∧ iteratedDeriv 3 f 0=0 := by
  have heq : (fun d:ℝ=>f (-d)) =ᶠ[𝓝 0] f := heven
  have h1 := heq.iteratedDeriv_eq 1
  have h3 := heq.iteratedDeriv_eq 3
  rw [iteratedDeriv_comp_neg] at h1 h3
  norm_num at h1 h3
  constructor <;> linarith

/-- Oddness improves the linear response to a cubic analytic remainder. -/
theorem analytic_odd_linear_cubic_remainder (f:ℝ→ℝ) (hf:AnalyticAt ℝ f 0)
    (hz:f 0=0) (hodd:∀ᶠ d in 𝓝 (0:ℝ), f (-d)= -f d) :
    ∃U:ℝ→ℝ, AnalyticAt ℝ U 0 ∧
      (∀d:ℝ,f d=deriv f 0*d+d^3*U d) ∧
      (fun d=>f d-deriv f 0*d) =O[𝓝 0] (fun d=>d^3) := by
  obtain ⟨U,hU,heq,hO⟩ := analytic_quadratic_remainder f hf
  have h2 := analytic_odd_germ_deriv2_zero f hodd
  refine ⟨U,hU,?_,?_⟩
  · simpa only [hz,h2,zero_div,zero_mul,zero_add,add_zero] using heq
  · simpa only [hz,h2,zero_div,zero_mul,sub_zero] using hO

/-- Evenness improves the quadratic optimized-value response to fourth order. -/
theorem analytic_even_quadratic_quartic_remainder (f:ℝ→ℝ) (hf:AnalyticAt ℝ f 0)
    (heven:∀ᶠ d in 𝓝 (0:ℝ), f (-d)=f d) :
    ∃V:ℝ→ℝ, AnalyticAt ℝ V 0 ∧
      (∀d:ℝ,f d=f 0+iteratedDeriv 2 f 0/2*d^2+d^4*V d) ∧
      (fun d=>f d-f 0-iteratedDeriv 2 f 0/2*d^2) =O[𝓝 0] (fun d=>d^4) := by
  obtain ⟨V,hV,heq,hO⟩ := analytic_cubic_remainder f hf
  obtain ⟨h1,h3⟩ := analytic_even_germ_odd_derivatives f heven
  refine ⟨V,hV,?_,?_⟩
  · simpa only [h1,h3,zero_div,zero_mul,add_zero] using heq
  · simpa only [h1,h3,zero_div,zero_mul,sub_zero] using hO

end
end ExactHoeffding
