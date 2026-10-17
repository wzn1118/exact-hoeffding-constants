import ExactHoeffding.StationaryCertificates
import Mathlib.Analysis.Real.Sqrt

/-! # The explicit radical auxiliary used by the stationary comparison -/
namespace ExactHoeffding
noncomputable section

def stationaryQZero (j L : ℝ) : ℝ :=
  j * Real.sqrt (((j-1)*L-1)/(L*(L+j)))

private theorem qZero_square (j L : ℝ) (hj : 3 ≤ j) (hL : j-1 ≤ L) :
    (stationaryQZero j L)^2 = j^2 * (((j-1)*L-1)/(L*(L+j))) := by
  have hL0 : 0 < L := by linarith
  have hnum : 0 ≤ (j-1)*L-1 := by nlinarith
  unfold stationaryQZero
  rw [mul_pow, Real.sq_sqrt (div_nonneg hnum (by positivity))]

/-- The Case II relation forces q strictly above the printed radical. -/
theorem stationary_q_gt_qZero (j L A q : ℝ)
    (hj : 3 ≤ j) (hL : j-1 ≤ L) (hq : 0 ≤ q)
    (hrel : A = j^2*(j-1)-(L+j)*q^2) (hsmall : A*L < j^2) :
    stationaryQZero j L < q := by
  have hL0 : 0 < L := by linarith
  have hT : 0 < L*(L+j) := by positivity
  have hs := qZero_square j L hj hL
  have hs' : (stationaryQZero j L)^2 * (L*(L+j)) = j^2*((j-1)*L-1) := by
    rw [hs]
    field_simp [hT.ne']
  have hqprod : q^2 * (L*(L+j)) = L*(j^2*(j-1)-A) := by
    rw [hrel]
    ring
  have hprod : (stationaryQZero j L)^2 * (L*(L+j)) <
      q^2 * (L*(L+j)) := by
    rw [hs', hqprod]
    nlinarith [hsmall]
  have hsq : (stationaryQZero j L)^2 < q^2 := by
    by_contra hn
    have hle : q^2 ≤ (stationaryQZero j L)^2 := le_of_not_gt hn
    have hbad := mul_le_mul_of_nonneg_right hle hT.le
    linarith
  have hq0 : 0 ≤ stationaryQZero j L := by
    unfold stationaryQZero
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  nlinarith

/-- The radical itself dominates the lower comparison j/L. -/
theorem stationary_qZero_ge_div (j L : ℝ) (hj : 3 ≤ j) (hL : j-1 ≤ L) :
    j/L ≤ stationaryQZero j L := by
  have hL0 : 0 < L := by linarith
  have hT : 0 < L*(L+j) := by positivity
  have hs := qZero_square j L hj hL
  have haux := stationary_small_A_auxiliary_positive j L hj hL
  have hq0 : 0 ≤ stationaryQZero j L := by
    unfold stationaryQZero
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hsq : (j/L)^2 ≤ (stationaryQZero j L)^2 := by
    rw [hs]
    field_simp [hL0.ne', hT.ne']
    nlinarith [haux]
  have hjdiv : 0 ≤ j/L := div_nonneg (by linarith) hL0.le
  nlinarith [sq_nonneg (j/L - stationaryQZero j L)]

/-- The last Case II comparison holds at q₀ itself. -/
theorem stationary_E_mul_qZero_ge (j L : ℝ) (hj : 3 ≤ j) (hL : j-1 ≤ L) :
    2*j*(L-j+1) ≤ (L*(L+1)-2*j)*stationaryQZero j L := by
  have hL0 : 0 < L := by linarith
  have hT : 0 < L*(L+j) := by positivity
  have hs := qZero_square j L hj hL
  have hs' : (stationaryQZero j L)^2 * (L*(L+j)) = j^2*((j-1)*L-1) := by
    rw [hs]
    field_simp [hT.ne']
  have hS : 0 ≤ L-j+1 := by linarith
  have hE : 0 ≤ L*(L+1)-2*j := by nlinarith
  have hq0 : 0 ≤ stationaryQZero j L := by
    unfold stationaryQZero
    exact mul_nonneg (by linarith) (Real.sqrt_nonneg _)
  have hK := stationary_K_nonnegative j (L-j+1) hj hS
  rw [show j-1+(L-j+1)=L by ring] at hK
  unfold stationaryK at hK
  have hmul := mul_nonneg (sq_nonneg j) hK
  have heq := congrArg (fun x : ℝ => (L*(L+1)-2*j)^2*x) hs'
  have hsq : (2*j*(L-j+1))^2 ≤ ((L*(L+1)-2*j)*stationaryQZero j L)^2 := by
    nlinarith
  have hr : 0 ≤ (L*(L+1)-2*j)*stationaryQZero j L := mul_nonneg hE hq0
  have hl : 0 ≤ 2*j*(L-j+1) := by positivity
  nlinarith

end
end ExactHoeffding
