import ExactHoeffding.NormalizedProxy
import ExactHoeffding.HypergeometricTail
import ExactHoeffding.FiniteExchangeability

/-!
# Necessary coefficients from genuine finite Hamming examples

The hypotheses below concern the explicitly defined finite Hamming MGF
family. The optimal-proxy and variance conclusions are derived from it.
-/

namespace ExactHoeffding

/-- A bound on the concrete centered MGF controls its normalized optimal proxy. -/
theorem normalizedHypergeomProxy_le_of_centered_mgf_bound (N k m : ℕ)
    (hk : k ≤ N) (hm0 : 0 < m) (hmN : m < N) (C : ℝ)
    (hC : ∀ s : ℝ, centeredHypergeomMGF N k m s ≤
      Real.exp (C * (m : ℝ) * ((N : ℝ) - m) * s ^ 2 / (8 * N))) :
    normalizedHypergeomProxy N k m ≤ C := by
  have hN : 0 < N := hm0.trans hmN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmNR : (m : ℝ) < N := by exact_mod_cast hmN
  have hp : IsQuadraticProxy (hypergeomCenteredLogMGF N k m)
      (C * (m : ℝ) * ((N : ℝ) - m) / (4 * N)) := by
    intro s
    have hs := hC s
    rw [centeredHypergeomMGF_eq_exp_log N k m hk hmN.le s] at hs
    have hlog := Real.exp_le_exp.mp hs
    convert hlog using 1 <;> ring
  have hopt := optimalProxy_le (hypergeomCenteredLogMGF N k m) _ hp
  have hscaled := mul_le_mul_of_nonneg_left hopt
    (show 0 ≤ 4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m)) by positivity)
  change normalizedHypergeomProxy N k m ≤ _ at hscaled
  have hcancel :
      (4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) *
        (C * (m : ℝ) * ((N : ℝ) - m) / (4 * N)) = C := by
    field_simp [hNR.ne', hmR.ne', (sub_pos.mpr hmNR).ne']
  exact hscaled.trans_eq hcancel

/-- The same concrete MGF bound is at least the actual normalized variance,
as a consequence of the certified zero-tilt quadratic limit. -/
theorem normalizedHypergeomVariance_le_of_centered_mgf_bound (N k m : ℕ)
    (hk : k ≤ N) (hm0 : 0 < m) (hmN : m < N) (C : ℝ)
    (hC : ∀ s : ℝ, centeredHypergeomMGF N k m s ≤
      Real.exp (C * (m : ℝ) * ((N : ℝ) - m) * s ^ 2 / (8 * N))) :
    (4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) *
      hypergeomTiltVariance N k m 0 ≤ C := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmNR : (m : ℝ) < N := by exact_mod_cast hmN
  have h := mul_le_mul_of_nonneg_left (hypergeomOptimalProxy_ge_variance N k m hk hmN.le)
    (show 0 ≤ 4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m)) by positivity)
  exact h.trans (normalizedHypergeomProxy_le_of_centered_mgf_bound N k m hk hm0 hmN C hC)

/-- An effective coefficient for the actual half-scaled Hamming contrasts
must dominate the corresponding normalized hypergeometric proxy. -/
theorem normalized_proxy_le_hamming_coefficient {N : ℕ} (k : ℕ)
    (hk : k ≤ N) (M : Finset (Fin N)) (hM0 : 0 < M.card) (hMN : M.card < N)
    (C : ℝ)
    (hC : ∀ s : ℝ,
      hammingSliceAverage
        (fun S => Real.exp (booleanContrast (fun i => twoLevelVector M s i / 2) S)) k ≤
      Real.exp (C * (∑ i : Fin N, (twoLevelVector M s i / 2) ^ 2) / 2)) :
    normalizedHypergeomProxy N k M.card ≤ C := by
  have hN : 0 < N := hM0.trans hMN
  apply normalizedHypergeomProxy_le_of_centered_mgf_bound N k M.card hk hM0 hMN C
  intro s
  have hs := hC s
  rw [booleanTwoLevel_slice_mgf M k hk s hN, booleanTwoLevel_sq_norm M s hN] at hs
  convert hs using 1 <;> ring

/-- Concrete Hamming contrasts also force the normalized variance lower bound. -/
theorem normalized_variance_le_hamming_coefficient {N : ℕ} (k : ℕ)
    (hk : k ≤ N) (M : Finset (Fin N)) (hM0 : 0 < M.card) (hMN : M.card < N)
    (C : ℝ)
    (hC : ∀ s : ℝ,
      hammingSliceAverage
        (fun S => Real.exp (booleanContrast (fun i => twoLevelVector M s i / 2) S)) k ≤
      Real.exp (C * (∑ i : Fin N, (twoLevelVector M s i / 2) ^ 2) / 2)) :
    (4 * (N : ℝ) / ((M.card : ℝ) * ((N : ℝ) - M.card))) *
      hypergeomTiltVariance N k M.card 0 ≤ C := by
  have hN : 0 < N := hM0.trans hMN
  apply normalizedHypergeomVariance_le_of_centered_mgf_bound N k M.card hk hM0 hMN C
  intro s
  have hs := hC s
  rw [booleanTwoLevel_slice_mgf M k hk s hN, booleanTwoLevel_sq_norm M s hN] at hs
  convert hs using 1 <;> ring

end ExactHoeffding
