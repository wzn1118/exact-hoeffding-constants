import ExactHoeffding.HypergeomBennettBernstein
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set
open scoped Topology

namespace ExactHoeffding
noncomputable section

/-- The Bennett kernel dominates the Bernstein rational kernel on the nonnegative half-line. -/
theorem bennettKernel_ge_bernsteinKernel {z : ℝ} (hz : 0 ≤ z) :
    bernsteinKernel z ≤ bennettKernel z := by
  let x : ℝ := z / (z + 2)
  have hz2 : 0 < z + 2 := by linarith
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hx1 : x < 1 := by
    dsimp [x]
    apply (div_lt_one hz2).2
    linarith
  have hlog := Real.sum_range_le_log_div hx0 hx1 2
  have hsum : (∑ i ∈ Finset.range 2,
      x ^ (2 * i + 1) / (2 * i + 1)) = x + x^3 / 3 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at hlog
  have hratio : (1 + x) / (1 - x) = 1 + z := by
    dsimp [x]
    field_simp [ne_of_gt hz2]
    ring
  rw [hratio] at hlog
  have hlog2 : 2 * (x + x^3 / 3) ≤ Real.log (1 + z) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog2 (by positivity : 0 ≤ 1 + z)
  have hbound : bernsteinKernel z ≤
      (1 + z) * (2 * (x + x^3 / 3)) - z := by
    dsimp [bernsteinKernel, x]
    have hz3 : 0 < z + 3 := by linarith
    have hz23 : 0 < z + 2 := by linarith
    have hden : 0 < 6 * (z + 2)^3 * (z + 3) := by positivity
    have hz4 : 0 ≤ z^4 := by positivity
    have hzplus : 0 ≤ z + 4 := by linarith
    have hnonneg : 0 ≤ z^4 * (z + 4) := mul_nonneg hz4 hzplus
    field_simp [ne_of_gt hz2, ne_of_gt hz3]
    nlinarith
  unfold bennettKernel
  linarith


/-- The Bernstein rate is bounded above by the Bennett rate for nonnegative
arguments and a positive variance scale. -/
theorem bernsteinRate_le_bennettRate_kernel {v₀ x : ℝ} (hv₀ : 0 < v₀) (hx : 0 ≤ x) :
    bernsteinRate v₀ x ≤ bennettRate v₀ x := by
  have hz : 0 ≤ x / v₀ := div_nonneg hx hv₀.le
  have hkernel := bennettKernel_ge_bernsteinKernel hz
  calc
    bernsteinRate v₀ x = v₀ * bernsteinKernel (x / v₀) := by
      dsimp [bernsteinRate, bernsteinKernel]
      field_simp [ne_of_gt hv₀]
      ring
    _ ≤ v₀ * bennettKernel (x / v₀) :=
      mul_le_mul_of_nonneg_left hkernel hv₀.le
    _ = bennettRate v₀ x := rfl

/-- The exact finite-population Bernstein exponent is strictly below the
piecewise KL rate on the upper supported tail. -/
theorem hypergeomBernsteinRate_lt_canonicalPiecewiseRate_upper (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hvμ : (m:ℝ)*k/N < v) (hvm : v ≤ m) :
    hypergeomBernsteinRate N k m v < canonicalPiecewiseRate N k m v := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hM : 0 < envelopeM (N:ℝ) (m:ℝ) := envelopeM_positive _ _ hmR hhR
  have hp : 0 < (k:ℝ)/N := by
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have hp1 : (k:ℝ)/N < 1 := by
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    apply (div_lt_one hN).2
    have hkN : k < N := by omega
    exact_mod_cast hkN
  have hv₀ : 0 < envelopeM (N:ℝ) (m:ℝ) * ((k:ℝ)/N) *
      (1 - (k:ℝ)/N) := by positivity
  have hle : hypergeomBernsteinRate N k m v ≤ hypergeomBennettRate N k m v := by
    unfold hypergeomBernsteinRate hypergeomBennettRate
    exact bernsteinRate_le_bennettRate_kernel hv₀ (abs_nonneg _)
  exact hle.trans_lt (hypergeomBennettRate_lt_canonicalPiecewiseRate_upper
    N k m hm hmk hk hhalf v hvμ hvm)

/-- The exact finite-population Bernstein exponent is strictly below the
piecewise KL rate on the lower supported tail. -/
theorem hypergeomBernsteinRate_lt_canonicalPiecewiseRate_lower (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvμ : v < (m:ℝ)*k/N) :
    hypergeomBernsteinRate N k m v < canonicalPiecewiseRate N k m v := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hM : 0 < envelopeM (N:ℝ) (m:ℝ) := envelopeM_positive _ _ hmR hhR
  have hp : 0 < (k:ℝ)/N := by
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have hp1 : (k:ℝ)/N < 1 := by
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    apply (div_lt_one hN).2
    have hkN : k < N := by omega
    exact_mod_cast hkN
  have hv₀ : 0 < envelopeM (N:ℝ) (m:ℝ) * ((k:ℝ)/N) *
      (1 - (k:ℝ)/N) := by positivity
  have hle : hypergeomBernsteinRate N k m v ≤ hypergeomBennettRate N k m v := by
    unfold hypergeomBernsteinRate hypergeomBennettRate
    exact bernsteinRate_le_bennettRate_kernel hv₀ (abs_nonneg _)
  exact hle.trans_lt (hypergeomBennettRate_lt_canonicalPiecewiseRate_lower
    N k m hm hmk hk hhalf v hv0 hvμ)

end
end ExactHoeffding
