import ExactHoeffding.BernsteinKernel
import ExactHoeffding.PiecewiseKLFourRates

open Set
namespace ExactHoeffding
noncomputable section

/-- The Bernstein rational exponent is bounded by Bennett's exponent for a
positive variance scale and a nonnegative deviation. -/
theorem bernsteinRate_le_bennettRate {v₀ x : ℝ}
    (hv₀ : 0 < v₀) (hx : 0 ≤ x) :
    bernsteinRate v₀ x ≤ bennettRate v₀ x := by
  have hz : 0 ≤ x / v₀ := div_nonneg hx hv₀.le
  have h := bennettKernel_ge_bernsteinKernel hz
  have hmul := mul_le_mul_of_nonneg_left h hv₀.le
  dsimp [bennettRate, bernsteinRate, bennettKernel, bernsteinKernel] at hmul ⊢
  field_simp [hv₀.ne'] at hmul ⊢
  nlinarith

private theorem canonicalPiecewiseRate_at_mean (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ)
      ((m : ℝ) * (k : ℝ) / N) = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2 * (k : ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2 * (m : ℝ) < N := by exact_mod_cast hhalf
  have hr := kl_switching_points_full_domain (N : ℝ) k m hmR hmkR hkR hhR
  have hJ : canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ)
      ((m : ℝ) * (k : ℝ) / N) =
      scaledKLRate (envelopeM (N : ℝ) (m : ℝ)) ((k : ℝ) / N)
        (envelopeScale (N : ℝ) (m : ℝ))
        ((m : ℝ) * (k : ℝ) / N) ((m : ℝ) * (k : ℝ) / N) := by
    unfold canonicalPiecewiseRate
    rw [piecewiseKLRate_eq_central hr.2.1.le hr.2.2.1.le]
    rfl
  rw [hJ]
  unfold scaledKLRate
  have hp : 0 < (k : ℝ) / N := by
    have hk0 : 0 < k := by omega
    positivity
  have hp1 : (k : ℝ) / N < 1 := by
    apply (div_lt_one hN).2
    exact_mod_cast (show k < N by omega)
  have harg : (k : ℝ) / N + envelopeScale (N : ℝ) (m : ℝ) *
      ((m : ℝ) * (k : ℝ) / N - (m : ℝ) * (k : ℝ) / N) /
      envelopeM (N : ℝ) (m : ℝ) = (k : ℝ) / N := by ring
  rw [harg, bernoulliKL_self hp hp1]
  ring

/-- The actual hypergeometric Bernstein exponent is bounded by the closed
piecewise rate on both supported tails. -/
theorem hypergeomBernsteinRate_le_canonicalPiecewiseRate_upper
    (N k m : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N)
    (hhalf : 2*m < N) (v : ℝ)
    (hvμ : (m : ℝ) * k / N < v) (hvm : v ≤ m) :
    hypergeomBernsteinRate N k m v ≤
      canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) v := by
  have hb := hypergeomBennettRate_lt_canonicalPiecewiseRate_upper
    N k m hm hmk hk hhalf v hvμ hvm
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hmN : (m : ℝ) < N := by
    exact_mod_cast (show m < N by omega)
  have hp : 0 < (k : ℝ) / N := by
    have hk0 : 0 < k := by omega
    positivity
  have hp1 : (k : ℝ) / N < 1 := by
    apply (div_lt_one hN).2
    exact_mod_cast (show k < N by omega)
  have hM : 0 < envelopeM (N : ℝ) (m : ℝ) := by
    exact envelopeM_positive (N : ℝ) (m : ℝ)
      (by exact_mod_cast hm) (by exact_mod_cast hhalf)
  have hv0 : 0 < envelopeM (N : ℝ) (m : ℝ) * ((k : ℝ) / N) *
      (1 - (k : ℝ) / N) := by positivity
  have hx : 0 ≤ |v - (m : ℝ) * k / N| := abs_nonneg _
  have hscalar := bernsteinRate_le_bennettRate hv0 hx
  have hrel : hypergeomBernsteinRate N k m v ≤ hypergeomBennettRate N k m v := by
    simpa [hypergeomBernsteinRate, hypergeomBennettRate] using hscalar
  exact hrel.trans hb.le

theorem hypergeomBernsteinRate_le_canonicalPiecewiseRate_lower
    (N k m : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N)
    (hhalf : 2*m < N) (v : ℝ)
    (hvμ : v < (m : ℝ) * k / N) (hv0 : 0 ≤ v) :
    hypergeomBernsteinRate N k m v ≤
      canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) v := by
  have hb := hypergeomBennettRate_lt_canonicalPiecewiseRate_lower
    N k m hm hmk hk hhalf v hv0 hvμ
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < (k : ℝ) / N := by
    have hk0 : 0 < k := by omega
    positivity
  have hp1 : (k : ℝ) / N < 1 := by
    apply (div_lt_one hN).2
    exact_mod_cast (show k < N by omega)
  have hM : 0 < envelopeM (N : ℝ) (m : ℝ) := by
    exact envelopeM_positive (N : ℝ) (m : ℝ)
      (by exact_mod_cast hm) (by exact_mod_cast hhalf)
  have hv0M : 0 < envelopeM (N : ℝ) (m : ℝ) * ((k : ℝ) / N) *
      (1 - (k : ℝ) / N) := by positivity
  have hscalar := bernsteinRate_le_bennettRate hv0M (abs_nonneg (v - (m : ℝ) * k / N))
  have hrel : hypergeomBernsteinRate N k m v ≤ hypergeomBennettRate N k m v := by
    simpa [hypergeomBernsteinRate, hypergeomBennettRate] using hscalar
  exact hrel.trans hb.le

/-- At the mean both Bernstein and the closed rate vanish. -/
theorem hypergeomBernsteinRate_at_mean
    (N k m : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N)
    (hhalf : 2*m < N) :
    hypergeomBernsteinRate N k m ((m : ℝ) * k / N) = 0 ∧
      canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ)
        ((m : ℝ) * k / N) = 0 := by
  constructor
  · simp [hypergeomBernsteinRate, bernsteinRate]
  · exact canonicalPiecewiseRate_at_mean N k m hm hmk hk hhalf

end
end ExactHoeffding
