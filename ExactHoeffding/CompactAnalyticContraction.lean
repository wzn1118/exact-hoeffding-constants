import ExactHoeffding.FinitePopulationBernoulliEnvelope
import ExactHoeffding.NormalizedProxy
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Compact success-proportion contraction for the actual optimal proxy

For every fixed sample size and compact subinterval of the success-proportion
interval, the finite-population Bernoulli comparison holds beyond an explicit
population threshold.  The proof uses the stronger finite-parameter envelope,
so its conclusion includes both population parities and the complete equality
set.  All optimal coefficients here are suprema of the actual log-MGF
quotients.
-/

namespace ExactHoeffding

noncomputable section

/-- An explicit population threshold for the compact success-proportion
comparison. -/
def compactContractionPopulationThreshold (m : ℕ) (η : ℝ) : ℕ :=
  max 2 (⌈(m : ℝ) / η⌉₊ + 1)

/-- The compact success-proportion constraints force both marked and unmarked
populations to exceed the fixed sample size. -/
theorem compactContraction_admissible_margins (m N k : ℕ)
    (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η)
    (hN : compactContractionPopulationThreshold m η ≤ N)
    (hlo : η ≤ (k : ℝ) / N) (hhi : (k : ℝ) / N ≤ 1 - η) :
    2 ≤ N ∧ m ≤ k ∧ m ≤ N - k ∧ k < N ∧ m < N ∧ 0 < k := by
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hceil : ⌈(m : ℝ) / η⌉₊ + 1 ≤ N :=
    (le_max_right _ _).trans hN
  have hceilR : ((⌈(m : ℝ) / η⌉₊ : ℕ) : ℝ) < N := by
    exact_mod_cast (show ⌈(m : ℝ) / η⌉₊ < N by omega)
  have hlarge : (m : ℝ) < η * N := by
    have hratio := (Nat.le_ceil ((m : ℝ) / η)).trans_lt hceilR
    have hmN := (div_lt_iff₀ hη).mp hratio
    nlinarith only [hmN]
  have hlow := (le_div_iff₀ hNR).mp hlo
  have hhigh := (div_le_iff₀ hNR).mp hhi
  have hmk : m ≤ k := by
    exact_mod_cast (show (m : ℝ) ≤ k by linarith)
  have hkN : k < N := by
    have hηN : 0 < η * N := mul_pos hη hNR
    exact_mod_cast (show (k : ℝ) < N by nlinarith only [hhigh, hηN])
  have hmNk : m ≤ N - k := by
    rw [← Nat.cast_le (α := ℝ), Nat.cast_sub hkN.le]
    nlinarith only [hhigh, hlarge]
  exact ⟨hN2, hmk, hmNk, hkN, by omega, by omega⟩

/-- The closed Bernoulli coefficient is the actual optimal quadratic proxy,
including the balanced parameter and both deterministic endpoints. -/
theorem bernoulliSharpBeta_eq_actual_optimalProxy (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    bernoulliSharpBeta p = optimalProxy (bernoulliCenteredLogMGF p) := by
  symm
  exact optimalProxy_eq_of_optimal _
    (by simp [bernoulliCenteredLogMGF, bernoulliMGF]) _
    (bernoulli_sharp_quadratic_optimal p hp0 hp1)

/-- The exact compact-interval comparison in the supplement, with an explicit
threshold and all equality cases. -/
theorem hypergeom_compact_contraction_explicit (m : ℕ) (hm : 2 ≤ m)
    (η : ℝ) (hη : 0 < η) (_hηhalf : η < 1 / 2)
    (N k : ℕ) (hN : compactContractionPopulationThreshold m η ≤ N)
    (hlo : η ≤ (k : ℝ) / N) (hhi : (k : ℝ) / N ≤ 1 - η) :
    hypergeomOptimalProxy N k m ≤
      ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) *
        optimalProxy (bernoulliCenteredLogMGF ((k : ℝ) / N)) ∧
    (hypergeomOptimalProxy N k m =
      ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) *
        optimalProxy (bernoulliCenteredLogMGF ((k : ℝ) / N)) ↔ 2 * k = N) ∧
    (2 * k ≠ N → hypergeomOptimalProxy N k m <
      ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) *
        optimalProxy (bernoulliCenteredLogMGF ((k : ℝ) / N))) := by
  obtain ⟨hN2, hmk, hmNk, hkN, _hmN, _hk⟩ :=
    compactContraction_admissible_margins m N k hm η hη hN hlo hhi
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp0 : 0 ≤ (k : ℝ) / N := div_nonneg (Nat.cast_nonneg _) hNR.le
  have hp1 : (k : ℝ) / N ≤ 1 :=
    (div_le_one hNR).mpr (by exact_mod_cast hkN.le)
  rw [← bernoulliSharpBeta_eq_actual_optimalProxy _ hp0 hp1]
  exact ⟨hypergeom_proxy_le_scaled_bernoulli N k m hm hmk hmNk,
    hypergeom_proxy_scaled_bernoulli_equality_iff N k m hm hmk hmNk,
    hypergeom_proxy_lt_scaled_bernoulli N k m hm hmk hmNk⟩

/-- The same compact comparison in the manuscript's normalized proxy
coordinates, with the same equality set and strict nonbalanced cases. -/
theorem normalized_hypergeom_compact_contraction_explicit
    (m : ℕ) (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η) (hηhalf : η < 1 / 2)
    (N k : ℕ) (hN : compactContractionPopulationThreshold m η ≤ N)
    (hlo : η ≤ (k : ℝ) / N) (hhi : (k : ℝ) / N ≤ 1 - η) :
    normalizedHypergeomProxy N k m ≤
      (4 * (N : ℝ) / ((N : ℝ) - 1)) *
        optimalProxy (bernoulliCenteredLogMGF ((k : ℝ) / N)) ∧
    (normalizedHypergeomProxy N k m =
      (4 * (N : ℝ) / ((N : ℝ) - 1)) *
        optimalProxy (bernoulliCenteredLogMGF ((k : ℝ) / N)) ↔ 2 * k = N) ∧
    (2 * k ≠ N → normalizedHypergeomProxy N k m <
      (4 * (N : ℝ) / ((N : ℝ) - 1)) *
        optimalProxy (bernoulliCenteredLogMGF ((k : ℝ) / N))) := by
  obtain ⟨hN2, _hmk, _hmNk, _hkN, hmN, _hk⟩ :=
    compactContraction_admissible_margins m N k hm η hη hN hlo hhi
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNm : 0 < (N : ℝ) - m := by
    exact sub_pos.mpr (by exact_mod_cast hmN)
  have hN1 : 0 < (N : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  let S : ℝ := 4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))
  have hS : 0 < S := by dsimp [S]; positivity
  let B : ℝ := optimalProxy (bernoulliCenteredLogMGF ((k : ℝ) / N))
  have hcancel : S * (((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) * B) =
      (4 * (N : ℝ) / ((N : ℝ) - 1)) * B := by
    dsimp [S]
    field_simp [hmR.ne', hNm.ne', hN1.ne']
  have hnorm : normalizedHypergeomProxy N k m = S * hypergeomOptimalProxy N k m := rfl
  obtain ⟨hle, heq, hlt⟩ :=
    hypergeom_compact_contraction_explicit m hm η hη hηhalf N k hN hlo hhi
  change hypergeomOptimalProxy N k m ≤ _ * B at hle
  change (hypergeomOptimalProxy N k m = _ * B ↔ _) at heq
  change (2 * k ≠ N → hypergeomOptimalProxy N k m < _ * B) at hlt
  rw [hnorm, ← hcancel]
  refine ⟨mul_le_mul_of_nonneg_left hle hS.le, ?_, ?_⟩
  · constructor
    · intro hh
      exact heq.mp (mul_left_cancel₀ hS.ne' hh)
    · intro hh
      rw [heq.mpr hh]
  · intro hb
    exact mul_lt_mul_of_pos_left (hlt hb) hS

/-- Eventual compact contraction for all actual finite populations and both
parities.  Equality holds precisely at the balanced marked margin. -/
theorem hypergeom_uniform_bernoulli_envelope_fixed_sample
    (m : ℕ) (hm : 2 ≤ m) (η : ℝ) (hη : 0 < η) (hηhalf : η < 1 / 2) :
    ∃ N₁ : ℕ, ∀ N k : ℕ, N₁ ≤ N →
      η ≤ (k : ℝ) / N → (k : ℝ) / N ≤ 1 - η →
      hypergeomOptimalProxy N k m ≤
        ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) *
          optimalProxy (bernoulliCenteredLogMGF ((k : ℝ) / N)) ∧
      (hypergeomOptimalProxy N k m =
        ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) *
          optimalProxy (bernoulliCenteredLogMGF ((k : ℝ) / N)) ↔ 2 * k = N) ∧
      (2 * k ≠ N → hypergeomOptimalProxy N k m <
        ((m : ℝ) * ((N : ℝ) - m) / ((N : ℝ) - 1)) *
          optimalProxy (bernoulliCenteredLogMGF ((k : ℝ) / N))) := by
  refine ⟨compactContractionPopulationThreshold m η, ?_⟩
  exact fun N k hN hlo hhi =>
    hypergeom_compact_contraction_explicit m hm η hη hηhalf N k hN hlo hhi

end

end ExactHoeffding
