import ExactHoeffding.HypergeometricODE
import ExactHoeffding.TiltedAdmissibilityDirect
import ExactHoeffding.RiccatiCertificates

/-!
# Population-parameter interfaces for actual hypergeometric Riccati identities

All recurrences, derivatives, and positivity facts retain the original
population parameters `N,k,m`. The only support restriction is `m <= k`
and `k + m <= N`, with positive sample size for strict positivity.
-/

namespace ExactHoeffding

private theorem margin_remainder_cast (N k m : ℕ) (hkm : k + m ≤ N) :
    ((N - (k + m) : ℕ) : ℝ) = (N : ℝ) - k - m := by
  rw [Nat.cast_sub hkm, Nat.cast_add]
  ring

theorem hypergeomMass_pos_of_margins (N k m i : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hi : i ≤ m) :
    0 < hypergeomMass N k m i := by
  have hn : k + m + (N - (k + m)) = N := Nat.add_sub_of_le hkm
  simpa only [hn] using hypergeomMass_pos_canonical k m (N - (k + m)) i hmk hi

theorem hypergeomTiltMean_pos_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hm : 0 < m) (t : ℝ) :
    0 < hypergeomTiltMean N k m t := by
  have hn : k + m + (N - (k + m)) = N := Nat.add_sub_of_le hkm
  simpa only [hn] using hypergeomTiltMean_pos k m (N - (k + m)) hmk hm t

theorem hypergeomTiltMean_lt_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hm : 0 < m) (t : ℝ) :
    hypergeomTiltMean N k m t < (m : ℝ) := by
  have hn : k + m + (N - (k + m)) = N := Nat.add_sub_of_le hkm
  simpa only [hn] using hypergeomTiltMean_lt k m (N - (k + m)) hmk hm t

theorem hypergeomTiltMean_mem_Ioo_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hm : 0 < m) (t : ℝ) :
    hypergeomTiltMean N k m t ∈ Set.Ioo (0 : ℝ) m := by
  exact ⟨hypergeomTiltMean_pos_of_margins N k m hmk hkm hm t,
    hypergeomTiltMean_lt_of_margins N k m hmk hkm hm t⟩

theorem hypergeomTiltVariance_pos_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hm : 0 < m) (t : ℝ) :
    0 < hypergeomTiltVariance N k m t := by
  have hn : k + m + (N - (k + m)) = N := Nat.add_sub_of_le hkm
  simpa only [hn] using hypergeomTiltVariance_pos k m (N - (k + m)) hmk hm t

theorem hypergeomTiltVariance_differential_balance_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (t : ℝ) :
    let u := hypergeomTiltMean N k m t
    let v := hypergeomTiltVariance N k m t
    let w := deriv (hypergeomTiltVariance N k m) t
    (2 * u + (N : ℝ) - k - m) * v + w =
      Real.exp t * (((k : ℝ) - u) * ((m : ℝ) - u) + v) +
        Real.exp t * ((2 * u - k - m) * v + w) := by
  have hn : k + m + (N - (k + m)) = N := Nat.add_sub_of_le hkm
  have h := hypergeomTiltVariance_differential_balance k m (N - (k + m)) hmk t
  dsimp only at h ⊢
  rw [hn, margin_remainder_cast N k m hkm] at h
  convert h using 1
  ring

theorem hypergeomTiltVariance_stationary_balance_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (t : ℝ)
    (hw : deriv (hypergeomTiltVariance N k m) t = 0) :
    let u := hypergeomTiltMean N k m t
    let v := hypergeomTiltVariance N k m t
    Real.exp t * (((k : ℝ) - u) * ((m : ℝ) - u) -
      v * ((k : ℝ) + m - 2 * u - 1)) = v * ((N : ℝ) - k - m + 2 * u) := by
  have h := hypergeomTiltVariance_differential_balance_of_margins N k m hmk hkm t
  dsimp only at h ⊢
  rw [hw] at h
  nlinarith only [h]

/-- The actual variance derivative satisfies the certificate polynomial identity. -/
theorem hypergeomTiltVariance_curve_identity_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (t : ℝ) :
    let u := hypergeomTiltMean N k m t
    let v := hypergeomTiltVariance N k m t
    let w := deriv (hypergeomTiltVariance N k m) t
    ((k : ℝ) * m - N * u) * w = riccatiF N k m u v := by
  have hn : k + m + (N - (k + m)) = N := Nat.add_sub_of_le hkm
  have h := hypergeomTiltVariance_curve_identity k m (N - (k + m)) hmk t
  dsimp only at h ⊢
  rw [hn, margin_remainder_cast N k m hkm] at h
  unfold riccatiF riccatiA riccatiC
  nlinarith only [h]

/-- Centering the coefficient gives the exact form used at barrier contacts. -/
theorem hypergeomTiltVariance_centered_curve_identity (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hN : 0 < N) (t : ℝ) :
    let u := hypergeomTiltMean N k m t
    let v := hypergeomTiltVariance N k m t
    riccatiF N k m u v +
      (N : ℝ) * (u - (m : ℝ) * k / N) * deriv (hypergeomTiltVariance N k m) t = 0 := by
  have h := hypergeomTiltVariance_curve_identity_of_margins N k m hmk hkm t
  dsimp only at h ⊢
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hc : (N : ℝ) * (hypergeomTiltMean N k m t - (m : ℝ) * k / N) =
      N * hypergeomTiltMean N k m t - (k : ℝ) * m := by
    field_simp [hN']
  rw [hc]
  nlinarith only [h]

theorem hypergeomTiltMeanVariance_den_pos_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hm : 0 < m) (t : ℝ) :
    0 < riccatiC k m (hypergeomTiltMean N k m t) + hypergeomTiltVariance N k m t := by
  have hn : k + m + (N - (k + m)) = N := Nat.add_sub_of_le hkm
  simpa only [hn, riccatiC] using
    hypergeomTiltMeanVariance_den_pos k m (N - (k + m)) hmk hm t

theorem hypergeomTiltExp_ratio_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hm : 0 < m) (t : ℝ) :
    let u := hypergeomTiltMean N k m t
    let v := hypergeomTiltVariance N k m t
    Real.exp t = (riccatiA N k m u + v) / (riccatiC k m u + v) := by
  dsimp only
  apply (eq_div_iff (ne_of_gt
    (hypergeomTiltMeanVariance_den_pos_of_margins N k m hmk hkm hm t))).mpr
  exact (hypergeomTiltMeanVariance_balance_of_margins N k m hmk hkm t).symm

/-- The quadratic barrier at its center is the finite-population variance. -/
theorem varianceBarrier_center_probability (N m p : ℝ) :
    varianceBarrier N m (1 - 2 * p) 0 = envelopeM N m * p * (1 - p) := by
  unfold varianceBarrier
  ring

theorem varianceBarrier_center_success_fraction (N k m : ℝ)
    (hN : N ≠ 0) (hN1 : N - 1 ≠ 0) :
    varianceBarrier N m (1 - 2 * k / N) 0 =
      m * k * (N - k) * (N - m) / (N ^ 2 * (N - 1)) := by
  unfold varianceBarrier envelopeM
  field_simp [hN, hN1]
  ring

end ExactHoeffding
