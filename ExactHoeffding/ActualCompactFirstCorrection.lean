import ExactHoeffding.CanonicalOptimizedPopulationRemainder

/-! # Closed first population correction uniformly through balance -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

/-- The explicit first inverse-population coefficient of the actual normalized
optimum, with its removable balanced value. -/
def actualCompactFirstCorrection (m : ℕ) (d : ℝ) : ℝ :=
  if d=0 then 1 else (m:ℝ)*(d/Real.artanh d)-((m:ℝ)-1)*d^2/
    ((2*Real.artanh d)^2*jointSuccessFraction d*(1-jointSuccessFraction d))

@[simp] theorem actualCompactFirstCorrection_zero (m : ℕ) :
    actualCompactFirstCorrection m 0=1 := by simp [actualCompactFirstCorrection]

/-- At balance the actual optimized normalized value has the exact germ
`1/(1-e)`, so its first population derivative is one for every sample size. -/
theorem jointOptimalValue_balanced_hasDerivAt_population_zero
    (m : ℕ) (hm : 0<m) :
    HasDerivAt (fun e:ℝ => jointOptimalValue m (e,0)) 1 0 := by
  obtain ⟨τ,_,_,hmax,hbal,_⟩ := jointProxyExtension_analytic_global_optimizer m hm
  have heq : (fun e:ℝ => jointOptimalValue m (e,0))=ᶠ[𝓝 (0:ℝ)]
      (fun e:ℝ => 1/(1-e)) := by
    have hc : Tendsto (fun e:ℝ => (e,(0:ℝ))) (𝓝 0) (𝓝 (0,0)) :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hc.eventually (jointOptimalValue_eventually_eq_branch m (0,0) τ hmax),
      jointNormalizedValue_balanced m hm τ hbal] with e he hb
    exact he.trans hb
  have hd := (hasDerivAt_const (0:ℝ) (1:ℝ)).div
    ((hasDerivAt_id (0:ℝ)).const_sub 1) (by norm_num)
  have h : HasDerivAt (fun e:ℝ => 1/(1-e)) 1 0 := by
    simpa only [id_eq,mul_zero,sub_zero,one_pow,div_one,zero_mul,mul_neg_one,
      sub_neg_eq_add,zero_add,Pi.div_apply,one_mul] using! hd
  exact h.congr_of_eventuallyEq heq

/-- The closed formula, including its value at zero, is the directional
derivative of the actual canonical optimum throughout the nonnegative axis. -/
theorem actualCompactFirstCorrection_eq_parameterPartial
    (m : ℕ) (hm : 2≤m) (d : ℝ) (hd₀ : 0≤d) (hd₁ : d<1) :
    actualCompactFirstCorrection m d=parameterPartial (jointOptimalValue m) (1,0) (0,d) := by
  have hd : d∈Ioo (-1:ℝ) 1 := ⟨by linarith,hd₁⟩
  rw [parameterPartial_fst_eq_deriv (jointOptimalValue m) (0,d)
    (jointOptimalValue_analytic_full_axis m (by omega) d hd).differentiableAt]
  by_cases hz : d=0
  · subst d
    simpa only [actualCompactFirstCorrection_zero] using
      (jointOptimalValue_balanced_hasDerivAt_population_zero m (by omega)).deriv.symm
  · rw [actualCompactFirstCorrection,if_neg hz]
    exact (jointOptimalValue_hasDerivAt_population_zero m hm d
      (lt_of_le_of_ne hd₀ (Ne.symm hz)) hd₁).deriv.symm

/-- The explicit first coefficient extends continuously through zero, with
value one, as a consequence of actual joint analyticity of the optimized value. -/
theorem actualCompactFirstCorrection_continuousOn
    (m : ℕ) (hm : 2≤m) (d₀ : ℝ) (hd₁ : d₀<1) :
    ContinuousOn (actualCompactFirstCorrection m) (Icc 0 d₀) := by
  have hEq : EqOn (actualCompactFirstCorrection m)
      (fun d => parameterPartial (jointOptimalValue m) (1,0) (0,d)) (Icc 0 d₀) := by
    intro d hd
    exact actualCompactFirstCorrection_eq_parameterPartial m hm d hd.1 (lt_of_le_of_lt hd.2 hd₁)
  apply ContinuousOn.congr _ hEq
  intro d hd
  have hdi : d∈Ioo (-1:ℝ) 1 := ⟨by linarith [hd.1],lt_of_le_of_lt hd.2 hd₁⟩
  exact ((parameterPartial_analytic (jointOptimalValue m) (1,0) (0,d)
    (jointOptimalValue_analytic_full_axis m (by omega) d hdi)).continuousAt.comp_of_eq
      (continuousAt_const.prodMk continuousAt_id) rfl).continuousWithinAt

/-- The manuscript's first population expansion has one uniform quadratic
error constant on the full compact interval, with the balanced coefficient
explicitly equal to one. -/
theorem jointOptimalValue_uniform_explicit_first_correction
    (m : ℕ) (hm : 2≤m) (d₀ : ℝ) (hd₀ : 0≤d₀) (hd₁ : d₀<1) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ e in 𝓝 (0:ℝ),∀ d∈Icc 0 d₀,
      |jointOptimalValue m (e,d)-4*bernoulliSharpBeta (jointSuccessFraction d)-
        e*(if d=0 then 1 else (m:ℝ)*(d/Real.artanh d)-((m:ℝ)-1)*d^2/
          ((2*Real.artanh d)^2*jointSuccessFraction d*(1-jointSuccessFraction d)))|≤C*e^2 := by
  obtain ⟨C,hC,hrem⟩ := jointOptimalValue_uniform_population_remainder m (by omega) d₀ hd₀ hd₁
  refine ⟨C,hC,?_⟩
  filter_upwards [hrem] with e he
  intro d hd
  have h := actualCompactFirstCorrection_eq_parameterPartial m hm d hd.1
    (lt_of_le_of_lt hd.2 hd₁)
  change |jointOptimalValue m (e,d)-4*bernoulliSharpBeta (jointSuccessFraction d)-
    e*actualCompactFirstCorrection m d|≤C*e^2
  rw [h]
  exact he d hd

end
end ExactHoeffding
