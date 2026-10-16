import ExactHoeffding.GoalBFixedSample
import ExactHoeffding.FinitePopulationBernoulliEnvelope

namespace ExactHoeffding
noncomputable section

/-- The ordinary central variance benchmark used in the fixed-sample gap. -/
def fixedSampleCentralVariance (N m : ℕ) : ℝ :=
  ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) *
    (((N / 2 : ℕ) : ℝ) * ((N : ℝ) - (N / 2 : ℕ))) / (N : ℝ) ^ 2

/-- The explicit individual-margin gap on the canonical triangle. -/
def fixedSampleIndividualGap (N k m : ℕ) : ℝ :=
  let W := fixedSampleCentralVariance N m
  let M := (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)
  let d := 1 - 2 * (k : ℝ) / (N : ℝ)
  if m ≤ k then W - M / (4 * (1 + d ^ 2 / 3))
  else W - ((k : ℝ) * ((N : ℝ) - k)) / (4 * ((N : ℝ) - 1))

private lemma bernoulli_beta_cubic_le (N k : ℕ)
    (hN : 0 < N) (hk : 0 < k) (hkhalf : 2 * k < N) :
    bernoulliSharpBeta ((k : ℝ) / N) ≤
      1 / (4 * (1 + (1 - 2 * (k : ℝ) / N) ^ 2 / 3)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hp0 : (0 : ℝ) < (k : ℝ) / N := by positivity
  have hp1 : (k : ℝ) / N < 1 / 2 := by
    apply (div_lt_iff₀ hNR).2
    have hh : 2 * (k : ℝ) < N := by exact_mod_cast hkhalf
    linarith
  have hd0 : 0 < 1 - 2 * (k : ℝ) / N := by
    have hh : 2 * (k : ℝ) / N < 1 := by
      apply (div_lt_one hNR).2
      exact_mod_cast hkhalf
    linarith
  have hratio_pos : 0 < 2 * (k : ℝ) / N := by positivity
  have hd1 : 1 - 2 * (k : ℝ) / N < 1 := by linarith
  have hne : (k : ℝ) / N ≠ 1 / 2 := by linarith
  have hlog : logOdds (1 - 2 * (k : ℝ) / N) =
      Real.log ((1 - (k : ℝ) / N) / ((k : ℝ) / N)) := by
    unfold logOdds
    congr 1
    field_simp [hNR.ne', hkR.ne']
    ring
  rw [bernoulliSharpBeta_eq_formula _ hne, ← hlog]
  have hfac := imbalanceFactor_cubic_upper (1 - 2 * (k : ℝ) / N) hd0 hd1
  unfold imbalanceFactor at hfac
  have hL : 0 < logOdds (1 - 2 * (k : ℝ) / N) :=
    logOdds_pos (1 - 2 * (k : ℝ) / N) hd0 hd1
  have hfac' := (div_le_iff₀ hL).mp hfac
  have hbeta_bound :
      (1 - 2 * (k : ℝ) / N) /
          (2 * logOdds (1 - 2 * (k : ℝ) / N)) ≤
        1 / (4 * (1 + (1 - 2 * (k : ℝ) / N) ^ 2 / 3)) := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hL)).2
    have hdenA : 0 < 1 + (1 - 2 * (k : ℝ) / N) ^ 2 / 3 := by positivity
    field_simp [hdenA.ne'] at hfac' ⊢
    nlinarith [hfac']
  convert hbeta_bound using 1 <;> ring

private lemma canonical_proxy_le_bernoulli_cubic (N k m : ℕ)
    (hN : 0 < N) (hm : 0 < m) (hmN : m < N)
    (hk : 0 < k) (hkhalf : 2 * k < N) (hmk : m ≤ k) :
    hypergeomOptimalProxy N k m ≤
      ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) /
        (4 * (1 + (1 - 2 * (k : ℝ) / N) ^ 2 / 3)) := by
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hden : 0 < (N : ℝ) - 1 := by linarith
  have hmle : (m : ℝ) ≤ N := by
    exact_mod_cast (Nat.le_of_lt hmN)
  have hM : 0 ≤ (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1) := by
    apply div_nonneg
    · apply mul_nonneg
      · positivity
      · linarith
    · exact hden.le
  have hbeta := bernoulli_beta_cubic_le N k hN hk hkhalf
  by_cases hm1 : m = 1
  · subst m
    rw [hypergeomOptimalProxy_singleton_subhalf N k hk (by omega)]
    have hne : (k : ℝ) / N ≠ 1 / 2 := by
      intro h
      have hc := (div_eq_iff (show (N : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN))).mp h
      have hh : 2 * (k : ℝ) = N := by linarith
      have hh' : 2 * (k : ℝ) < N := by exact_mod_cast hkhalf
      linarith
    rw [bernoulliSharpBeta_eq_formula _ hne] at hbeta
    have hbeta' : (1 - 2 * (k : ℝ) / N) /
        (2 * Real.log ((1 - (k : ℝ) / N) / ((k : ℝ) / N))) ≤
        1 / (4 * (1 + (1 - 2 * (k : ℝ) / N) ^ 2 / 3)) := by
      convert hbeta using 1 <;> ring
    have hden_ne : (N : ℝ) - 1 ≠ 0 := ne_of_gt hden
    convert hbeta' using 1 <;> field_simp [hden_ne] <;> ring
  · have hm2 : 2 ≤ m := by omega
    have henv := hypergeom_proxy_lt_scaled_bernoulli_subhalf N k m hm2 hmk hkhalf
    have hM_eq : envelopeM (N : ℝ) (m : ℝ) =
        (m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1) := by rfl
    rw [hM_eq] at henv
    have hbeta' : bernoulliSharpBeta ((k : ℝ) / N) ≤
        (4 * (1 + (1 - 2 * (k : ℝ) / N) ^ 2 / 3))⁻¹ := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbeta
    have hmul := mul_le_mul_of_nonneg_left hbeta' hM
    calc
      hypergeomOptimalProxy N k m ≤
          ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) *
            bernoulliSharpBeta ((k : ℝ) / N) := henv.le
      _ ≤ ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) *
            (4 * (1 + (1 - 2 * (k : ℝ) / N) ^ 2 / 3))⁻¹ := hmul
      _ = ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) /
            (4 * (1 + (1 - 2 * (k : ℝ) / N) ^ 2 / 3)) := by
              ring

/-- On the canonical triangle, the explicit branchwise gap is a valid
individual certificate for every noncentral margin. -/
theorem hypergeomOptimalProxy_le_canonical_individual_gap
    (N k m : ℕ) (hN : 2 ≤ N) (hk : 0 < k) (hkhalf : 2 * k ≤ N)
    (hnoncentral : 2 * k ≠ N)
    (hm : 0 < m) (hmhalf : 2 * m ≤ N) (hmN : m < N) :
    hypergeomOptimalProxy N k m ≤
      fixedSampleCentralVariance N m - fixedSampleIndividualGap N k m := by
  have hkhalf' : 2 * k < N := by omega
  unfold fixedSampleIndividualGap
  dsimp
  by_cases hmk : m ≤ k
  · have hbound := canonical_proxy_le_bernoulli_cubic N k m (by omega) hm hmN hk hkhalf' hmk
    rw [if_pos hmk]
    linarith
  · have hcurv := hypergeomOptimalProxy_le_curvature N k m (by omega) hmN.le
    have hkm : k < m := by omega
    have hmin : (k : ℝ) * ((N : ℝ) - k) ≤
        (m : ℝ) * ((N : ℝ) - m) := by
      have hkR : (k : ℝ) < m := by exact_mod_cast hkm
      have hsum : k + m ≤ N := by omega
      have hsumR : (k : ℝ) + (m : ℝ) ≤ N := by exact_mod_cast hsum
      nlinarith
    unfold sharpCurvatureConstant at hcurv
    rw [min_eq_left hmin] at hcurv
    rw [if_neg hmk]
    simpa [fixedSampleCentralVariance] using hcurv

end
end ExactHoeffding
