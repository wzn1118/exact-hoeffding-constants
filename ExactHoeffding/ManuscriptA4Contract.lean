import ExactHoeffding.BennettMeanEndpoint
import ExactHoeffding.StrictBernoulliProxyComparison

namespace ExactHoeffding
noncomputable section

/-- Typed statement contract for the manuscript's exact-variance Bennett and
Bernstein comparison paragraph.  On the canonical hypergeometric parameter
range, the actual zero-tilt variance is the scale `M p (1-p)`.  On each
supported side, every noncentral deviation has strictly larger scaled KL and
piecewise rates than the Bennett rate; the Bernstein rate is bounded by
Bennett and is itself strictly below both rates.  The support endpoints are
included, while at the mean all three rates vanish. -/
theorem manuscript_A4_exact_variance_bennett_bernstein_contract
    (N k m : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2 * k ≤ N)
    (hhalf : 2 * m < N) :
    hypergeomTiltVariance N k m 0 =
        envelopeM (N : ℝ) (m : ℝ) * ((k : ℝ) / N) * (1 - (k : ℝ) / N) ∧
    (∀ v : ℝ, (m : ℝ) * k / N < v → v ≤ m →
      hypergeomBernsteinRate N k m v ≤ hypergeomBennettRate N k m v ∧
      hypergeomBennettRate N k m v <
        scaledKLRate (envelopeM (N : ℝ) (m : ℝ)) ((k : ℝ) / N)
          (envelopeScale (N : ℝ) (m : ℝ)) ((m : ℝ) * k / N) v ∧
      hypergeomBernsteinRate N k m v <
        scaledKLRate (envelopeM (N : ℝ) (m : ℝ)) ((k : ℝ) / N)
          (envelopeScale (N : ℝ) (m : ℝ)) ((m : ℝ) * k / N) v ∧
      hypergeomBennettRate N k m v <
        canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) v ∧
      hypergeomBernsteinRate N k m v <
        canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) v) ∧
    (∀ v : ℝ, 0 ≤ v → v < (m : ℝ) * k / N →
      hypergeomBernsteinRate N k m v ≤ hypergeomBennettRate N k m v ∧
      hypergeomBennettRate N k m v <
        scaledKLRate (envelopeM (N : ℝ) (m : ℝ)) ((k : ℝ) / N)
          (envelopeScale (N : ℝ) (m : ℝ)) ((m : ℝ) * k / N) v ∧
      hypergeomBernsteinRate N k m v <
        scaledKLRate (envelopeM (N : ℝ) (m : ℝ)) ((k : ℝ) / N)
          (envelopeScale (N : ℝ) (m : ℝ)) ((m : ℝ) * k / N) v ∧
      hypergeomBennettRate N k m v <
        canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) v ∧
      hypergeomBernsteinRate N k m v <
        canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) v) ∧
    hypergeomBennettRate N k m ((m : ℝ) * k / N) = 0 ∧
      hypergeomBernsteinRate N k m ((m : ℝ) * k / N) = 0 ∧
      canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ)
        ((m : ℝ) * k / N) = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hhalfR : 2 * (m : ℝ) < N := by exact_mod_cast hhalf
  have hp : 0 < (k : ℝ) / N := by
    have hk0 : 0 < k := by omega
    positivity
  have hp1 : (k : ℝ) / N < 1 := by
    apply (div_lt_one hN).2
    have hkN : k < N := by omega
    exact_mod_cast hkN
  have hM : 0 < envelopeM (N : ℝ) (m : ℝ) :=
    envelopeM_positive (N : ℝ) (m : ℝ) hmR hhalfR
  have hvarianceScale :
      0 < envelopeM (N : ℝ) (m : ℝ) * ((k : ℝ) / N) *
        (1 - (k : ℝ) / N) := by positivity
  have hbernstein_le (v : ℝ) :
      hypergeomBernsteinRate N k m v ≤ hypergeomBennettRate N k m v := by
    have h := bernsteinRate_le_bennettRate hvarianceScale
      (abs_nonneg (v - (m : ℝ) * k / N))
    simpa [hypergeomBernsteinRate, hypergeomBennettRate] using h
  have hvariance := hypergeomTiltVariance_zero_eq_scaled_bernoulli_variance
    N k m (by omega) (by omega) (by omega)
  have hupper : ∀ v : ℝ, (m : ℝ) * k / N < v → v ≤ m →
      hypergeomBernsteinRate N k m v ≤ hypergeomBennettRate N k m v ∧
      hypergeomBennettRate N k m v <
        scaledKLRate (envelopeM (N : ℝ) (m : ℝ)) ((k : ℝ) / N)
          (envelopeScale (N : ℝ) (m : ℝ)) ((m : ℝ) * k / N) v ∧
      hypergeomBernsteinRate N k m v <
        scaledKLRate (envelopeM (N : ℝ) (m : ℝ)) ((k : ℝ) / N)
          (envelopeScale (N : ℝ) (m : ℝ)) ((m : ℝ) * k / N) v ∧
      hypergeomBennettRate N k m v <
        canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) v ∧
      hypergeomBernsteinRate N k m v <
        canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) v := by
    intro v hvμ hvm
    have hBscaled := hypergeomBennettRate_lt_scaledKLRate_upper
      N k m hm hmk hk hhalf v hvμ hvm
    have hBpiece := hypergeomBennettRate_lt_canonicalPiecewiseRate_upper
      N k m hm hmk hk hhalf v hvμ hvm
    have hBernpiece := hypergeomBernsteinRate_lt_canonicalPiecewiseRate_upper
      N k m hm hmk hk hhalf v hvμ hvm
    exact ⟨hbernstein_le v, hBscaled, (hbernstein_le v).trans_lt hBscaled,
      hBpiece, hBernpiece⟩
  have hlower : ∀ v : ℝ, 0 ≤ v → v < (m : ℝ) * k / N →
      hypergeomBernsteinRate N k m v ≤ hypergeomBennettRate N k m v ∧
      hypergeomBennettRate N k m v <
        scaledKLRate (envelopeM (N : ℝ) (m : ℝ)) ((k : ℝ) / N)
          (envelopeScale (N : ℝ) (m : ℝ)) ((m : ℝ) * k / N) v ∧
      hypergeomBernsteinRate N k m v <
        scaledKLRate (envelopeM (N : ℝ) (m : ℝ)) ((k : ℝ) / N)
          (envelopeScale (N : ℝ) (m : ℝ)) ((m : ℝ) * k / N) v ∧
      hypergeomBennettRate N k m v <
        canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) v ∧
      hypergeomBernsteinRate N k m v <
        canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) v := by
    intro v hv0 hvμ
    have hBscaled := hypergeomBennettRate_lt_scaledKLRate_lower
      N k m hm hmk hk hhalf v hv0 hvμ
    have hBpiece := hypergeomBennettRate_lt_canonicalPiecewiseRate_lower
      N k m hm hmk hk hhalf v hv0 hvμ
    have hBernpiece := hypergeomBernsteinRate_lt_canonicalPiecewiseRate_lower
      N k m hm hmk hk hhalf v hv0 hvμ
    exact ⟨hbernstein_le v, hBscaled, (hbernstein_le v).trans_lt hBscaled,
      hBpiece, hBernpiece⟩
  have hmean := hypergeomBennettBernsteinRates_at_mean N k m hm hmk hk hhalf
  exact ⟨hvariance, hupper, hlower, hmean.1, hmean.2.1, hmean.2.2⟩

end
end ExactHoeffding
