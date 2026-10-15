import ExactHoeffding.ExactParityConstants
import Mathlib.Analysis.SpecificLimits.Basic

open Filter Set
open scoped Topology

namespace ExactHoeffding

/-- A convex secant bound gives a quadratic lower bound for the normalized
logarithmic odds. -/
theorem imbalanceFactor_quadratic_lower (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    1 - d ^ 2 ≤ imbalanceFactor d := by
  have hs := logOdds_strictConvex.convexOn.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Ico 0 1 by simp)
    (show d ∈ Ico 0 1 from ⟨hd.le, hd1⟩) hd
    (logOdds_hasDerivAt d ⟨by linarith, hd1⟩)
  have hz : logOdds 0 = 0 := by simp [logOdds]
  simp only [slope_def_field, hz, sub_zero] at hs
  have hp : 0 < 1 - d ^ 2 := by nlinarith
  have hcross := (div_le_div_iff₀ hd hp).mp hs
  unfold imbalanceFactor
  apply (le_div_iff₀ (logOdds_pos d hd hd1)).2
  nlinarith only [hcross]

/-- The odd closed form has the lower bound needed to retain its first-order
inflation, uniformly in every population size. -/
theorem oddHypergeomConstant_first_order_lower (N : ℕ) (hN : 2 ≤ N) :
    ((N : ℝ) + 1) / N ≤ oddHypergeomConstant N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : 0 < (N : ℝ) - 1 := by linarith
  have hd : 0 < 1 / (N : ℝ) := by positivity
  have hd1 : 1 / (N : ℝ) < 1 := (div_lt_one hN0).2 (by linarith)
  have h := mul_le_mul_of_nonneg_left
    (imbalanceFactor_quadratic_lower (1 / (N : ℝ)) hd hd1)
    (show 0 ≤ (N : ℝ) / ((N : ℝ) - 1) by positivity)
  rw [oddHypergeomConstant_eq_factor N (by omega)] at h
  have heq : (N : ℝ) / ((N : ℝ) - 1) * (1 - (1 / (N : ℝ)) ^ 2) =
      ((N : ℝ) + 1) / N := by
    field_simp [hN0.ne', hN1.ne'] <;> ring
  rwa [heq] at h

/-- A finite-population sandwich for the exact parity coefficient. -/
theorem paritySharpConstant_first_order_bounds (N : ℕ) (hN : 2 ≤ N) :
    1 ≤ (N : ℝ) * (paritySharpConstant N - 1) ∧
      (N : ℝ) * (paritySharpConstant N - 1) ≤ (N : ℝ) / ((N : ℝ) - 1) := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : 0 < (N : ℝ) - 1 := by linarith
  have hlo : ((N : ℝ) + 1) / N ≤ paritySharpConstant N := by
    unfold paritySharpConstant
    split_ifs with he
    · apply (div_le_div_iff₀ hN0 hN1).2
      nlinarith
    · exact oddHypergeomConstant_first_order_lower N hN
  have hhi : paritySharpConstant N ≤ (N : ℝ) / ((N : ℝ) - 1) := by
    unfold paritySharpConstant
    split_ifs with he
    · exact le_rfl
    · exact (oddHypergeomConstant_lt_even_bound N (by omega)).le
  constructor
  · have h := mul_le_mul_of_nonneg_left hlo hN0.le
    have heq : (N : ℝ) * (((N : ℝ) + 1) / N) = (N : ℝ) + 1 := by
      field_simp [hN0.ne'] <;> ring
    rw [heq] at h
    nlinarith only [h]
  · have h := mul_le_mul_of_nonneg_left hhi hN0.le
    have heq : (N : ℝ) * ((N : ℝ) / ((N : ℝ) - 1) - 1) =
        (N : ℝ) / ((N : ℝ) - 1) := by
      field_simp [hN1.ne'] <;> ring
    calc
      (N : ℝ) * (paritySharpConstant N - 1) ≤
          (N : ℝ) * ((N : ℝ) / ((N : ℝ) - 1) - 1) := by
            nlinarith only [h]
      _ = _ := heq

/-- The manuscript's first-order asymptotic holds along the complete natural
population sequence, simultaneously for both parities. -/
theorem paritySharpConstant_first_order_limit :
    Tendsto (fun N : ℕ => (N : ℝ) * (paritySharpConstant N - 1))
      atTop (𝓝 1) := by
  have hu : Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) - 1)) atTop (𝓝 1) := by
    simpa only [sub_eq_add_neg] using (tendsto_natCast_div_add_atTop (-1 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact (paritySharpConstant_first_order_bounds N hN).1
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact (paritySharpConstant_first_order_bounds N hN).2

/-- The explicit odd coefficient itself has first-order inflation one,
even when evaluated along every natural population size. -/
theorem oddHypergeomConstant_first_order_limit :
    Tendsto (fun N : ℕ => (N : ℝ) * (oddHypergeomConstant N - 1))
      atTop (𝓝 1) := by
  have hu : Tendsto (fun N : ℕ => (N : ℝ) / ((N : ℝ) - 1)) atTop (𝓝 1) := by
    simpa only [sub_eq_add_neg] using (tendsto_natCast_div_add_atTop (-1 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    have h := mul_le_mul_of_nonneg_left
      (oddHypergeomConstant_first_order_lower N hN) hN0.le
    have heq : (N : ℝ) * (((N : ℝ) + 1) / N) = (N : ℝ) + 1 := by
      field_simp [hN0.ne'] <;> ring
    rw [heq] at h
    nlinarith only [h]
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hN0 : (0 : ℝ) < N := by linarith
    have hN1 : 0 < (N : ℝ) - 1 := by linarith
    have h := mul_le_mul_of_nonneg_left
      (oddHypergeomConstant_lt_even_bound N (by omega)).le hN0.le
    have heq : (N : ℝ) * ((N : ℝ) / ((N : ℝ) - 1) - 1) =
        (N : ℝ) / ((N : ℝ) - 1) := by
      field_simp [hN1.ne'] <;> ring
    calc
      (N : ℝ) * (oddHypergeomConstant N - 1) ≤
          (N : ℝ) * ((N : ℝ) / ((N : ℝ) - 1) - 1) := by
            nlinarith only [h]
      _ = _ := heq

/-- The least coefficient over all actual exchangeable cube laws has
first-order inflation exactly one. -/
theorem exactExchangeableConstant_first_order_limit :
    Tendsto (fun N : ℕ => (N : ℝ) * (exactExchangeableConstant N - 1))
      atTop (𝓝 1) := by
  apply paritySharpConstant_first_order_limit.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [exact_finite_exchangeability_constants N hN]

end ExactHoeffding
