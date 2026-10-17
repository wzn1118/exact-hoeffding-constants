import ExactHoeffding.HypergeomBernsteinComparison

open Set

namespace ExactHoeffding
noncomputable section

/-- The Bennett exponent has zero value and zero derivative at the origin. -/
theorem bennettRate_contact_at_zero {v₀ : ℝ} (hv₀ : 0 < v₀) :
    bennettRate v₀ 0 = 0 ∧ HasDerivAt (bennettRate v₀) 0 0 := by
  constructor
  · simp [bennettRate, bennettKernel]
  · have harg : HasDerivAt (fun z : ℝ => 1+z/v₀) (1/v₀) 0 := by
      simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using
        ((hasDerivAt_id 0).div_const v₀).const_add 1
    have hmul := (Real.hasDerivAt_mul_log (by norm_num : (1+(0:ℝ)/v₀) ≠ 0)).comp 0 harg
    have hsub := hmul.sub ((hasDerivAt_id 0).div_const v₀)
    have h := hsub.const_mul v₀
    change HasDerivAt (fun z : ℝ => v₀*((1+z/v₀)*Real.log (1+z/v₀)-z/v₀)) 0 0
    apply h.congr_deriv
    field_simp [hv₀.ne']
    simp [hv₀.ne']

/-- The scaled KL rate has zero value and zero derivative at its center. -/
theorem scaledKLRate_contact_at_mean {M p a μ : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hp : 0 < p) (hp1 : p < 1) :
    scaledKLRate M p a μ μ = 0 ∧
      HasDerivAt (scaledKLRate M p a μ) 0 μ := by
  have hθ : p+a*(μ-μ)/M ∈ Ioo 0 1 := by
    rw [sub_self, mul_zero, zero_div, add_zero]
    exact ⟨hp,hp1⟩
  have hderiv := scaledKLRate_hasDerivAt hM ha hp hp1 hθ
  have hslope : scaledKLSlope M p a μ μ = 0 := by
    simp [scaledKLSlope, bernoulliFenchelTilt, hp.ne',
      (sub_pos.mpr hp1).ne']
  constructor
  · simp [scaledKLRate, bernoulliKL, hp.ne', (sub_pos.mpr hp1).ne']
  · rw [hslope] at hderiv
    exact hderiv

/-- The exact finite-population Bennett exponent vanishes at the mean. -/
theorem hypergeomBennettRate_at_mean (N k m : ℕ) :
    hypergeomBennettRate N k m ((m : ℝ) * k / N) = 0 := by
  simp [hypergeomBennettRate, bennettRate, bennettKernel]

/-- At the mean, the Bennett exponent, Bernstein exponent, and piecewise
rate all vanish. -/
theorem hypergeomBennettBernsteinRates_at_mean (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2 * k ≤ N)
    (hhalf : 2 * m < N) :
    hypergeomBennettRate N k m ((m : ℝ) * k / N) = 0 ∧
      hypergeomBernsteinRate N k m ((m : ℝ) * k / N) = 0 ∧
      canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ)
        ((m : ℝ) * k / N) = 0 := by
  exact ⟨hypergeomBennettRate_at_mean N k m,
    (hypergeomBernsteinRate_at_mean N k m hm hmk hk hhalf).1,
    (hypergeomBernsteinRate_at_mean N k m hm hmk hk hhalf).2⟩


end
end ExactHoeffding
