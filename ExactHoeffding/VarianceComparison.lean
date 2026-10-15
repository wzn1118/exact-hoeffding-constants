import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace ExactHoeffding

/-- Reciprocal variance bounds combine by the minimum upper envelope. -/
theorem reciprocal_variance_minimum (V P B : ℝ)
    (hV : 0 < V) (hP : V ≤ P) (hB : V ≤ B) :
    1 / min P B ≤ 1 / V := by
  exact one_div_le_one_div_of_le hV (le_min hP hB)

/-- Exact difference of trial-count Bernoulli variance envelopes. -/
theorem bernoulli_envelope_gap (m k u : ℝ) (hm : m ≠ 0) (hk : k ≠ 0) :
    u * (k-u) / k - u * (m-u) / m = (k-m)*u^2/(m*k) := by
  field_simp
  ring

/-- The smaller number of trials gives the smaller mean-dependent envelope. -/
theorem bernoulli_envelope_order (m k u : ℝ) (hm : 0 < m) (hkm : m ≤ k) :
    u * (m-u) / m ≤ u * (k-u) / k := by
  have hk : 0 < k := lt_of_lt_of_le hm hkm
  have hgap := bernoulli_envelope_gap m k u (ne_of_gt hm) (ne_of_gt hk)
  have hnonneg : 0 ≤ (k-m)*u^2/(m*k) :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hkm) (sq_nonneg u))
      (le_of_lt (mul_pos hm hk))
  linarith

/-- Complemented-sample variance envelope in the original mean coordinate. -/
theorem complement_envelope_gap (m L R u : ℝ)
    (hm : m ≠ 0) (hden : m+L+R ≠ 0) :
    (m+L-u)*(R+u)/(m+L+R) - u*(m-u)/m =
      (L*u^2+R*(m-u)^2+m*L*R)/(m*(m+L+R)) := by
  field_simp
  ring

theorem complement_envelope_order (m L R u : ℝ)
    (hm : 0 < m) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    u*(m-u)/m ≤ (m+L-u)*(R+u)/(m+L+R) := by
  have hd : 0 < m+L+R := by linarith
  have hgap := complement_envelope_gap m L R u (ne_of_gt hm) (ne_of_gt hd)
  have hnum : 0 ≤ L*u^2+R*(m-u)^2+m*L*R := by positivity
  have hnonneg : 0 ≤ (L*u^2+R*(m-u)^2+m*L*R)/(m*(m+L+R)) :=
    div_nonneg hnum (le_of_lt (mul_pos hm hd))
  linarith

end ExactHoeffding
