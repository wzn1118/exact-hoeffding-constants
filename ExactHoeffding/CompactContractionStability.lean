import ExactHoeffding.CompactContractionBoundary

/-! # Uniform persistence of the positive contraction coefficient -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

/-- A continuous two-parameter factor with the actual positive contraction
boundary stays uniformly positive on a compact imbalance interval. -/
theorem compactContractionFactor_eventually_uniform_pos
    (m : ℕ) (hm : 2 ≤ m) (d₀ : ℝ) (hd₀ : 0 ≤ d₀) (hd₁ : d₀ < 1)
    (B : ℝ × ℝ → ℝ)
    (hB : ∀ d ∈ Icc 0 d₀, ContinuousAt B (0,d))
    (haxis : ∀ d ∈ Icc 0 d₀, B (0,d)=compactContractionBoundary m d) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ e in 𝓝 (0 : ℝ), ∀ d ∈ Icc 0 d₀, c ≤ B (e,d) := by
  obtain ⟨c,hc,hmin⟩ := compactContractionBoundary_uniform_pos m hm d₀ hd₀ hd₁
  refine ⟨c/2, by linarith, ?_⟩
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro d hd
  have hp : c/2 < B (0,d) := by rw [haxis d hd]; linarith [hmin d hd]
  exact ((continuousAt_const.eventually_lt (hB d hd) hp).mono fun u hu => hu.le)

/-- Exact analytic factorization converts the uniform boundary sign into
strict finite-population separation at every nonzero imbalance. -/
theorem compactContraction_factorized_strict_comparison
    (m : ℕ) (hm : 2 ≤ m) (d₀ : ℝ) (hd₀ : 0 ≤ d₀) (hd₁ : d₀ < 1)
    (B R₁ Rm : ℝ × ℝ → ℝ)
    (hB : ∀ d ∈ Icc 0 d₀, ContinuousAt B (0,d))
    (haxis : ∀ d ∈ Icc 0 d₀, B (0,d)=compactContractionBoundary m d)
    (hfactor : ∀ᶠ e in 𝓝 (0 : ℝ), ∀ d ∈ Icc 0 d₀,
      R₁ (e,d)-Rm (e,d)=e*d^2*B (e,d)) :
    ∀ᶠ e in 𝓝 (0 : ℝ), 0 < e → ∀ d ∈ Icc 0 d₀,
      Rm (e,d) ≤ R₁ (e,d) ∧ (Rm (e,d)=R₁ (e,d) ↔ d=0) := by
  obtain ⟨c,hc,hpos⟩ := compactContractionFactor_eventually_uniform_pos m hm d₀ hd₀ hd₁ B hB haxis
  filter_upwards [hpos,hfactor] with e he hf
  intro he0 d hd
  have hb : 0 < B (e,d) := lt_of_lt_of_le hc (he d hd)
  have hnon : 0 ≤ e*d^2*B (e,d) := mul_nonneg (mul_nonneg he0.le (sq_nonneg d)) hb.le
  constructor
  · linarith [hf d hd]
  · constructor
    · intro heq
      have hzero : e*d^2*B (e,d)=0 := by linarith [hf d hd]
      rcases mul_eq_zero.mp hzero with hleft | hright
      · rcases mul_eq_zero.mp hleft with hez | hdz
        · exact False.elim (ne_of_gt he0 hez)
        · nlinarith [sq_nonneg d]
      · exact False.elim (ne_of_gt hb hright)
    · intro hd0
      subst d
      have h := hf 0 hd
      simp only [sq, zero_mul, mul_zero] at h
      linarith

end
end ExactHoeffding
