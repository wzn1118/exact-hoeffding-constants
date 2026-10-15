import ExactHoeffding.RealMarginProbabilityBridge

/-! # Sharp one- and two-draw curvature with real success margins -/

namespace ExactHoeffding

noncomputable section

open Finset

/-- Sharp two-draw finite-population upper bound for real marks. -/
theorem realMargin_two_curvature_le (N k t : ℝ) (hN : 2 < N)
    (hk : 2 ≤ k) (hq : k+2 ≤ N) :
    deriv (deriv (fun u => Real.log (finiteMGF (range 3)
      (realMarginMass 2 (1/N) (k/N)) (fun i => (i:ℝ)) u))) t ≤
      (N-2)/(2*(N-1)) := by
  have ha : 0<(N-k)*(N-k-1) := by
    apply mul_pos <;> linarith
  have hb : 0<k*(N-k) := by
    apply mul_pos <;> linarith
  have hc : 0<k*(k-1) := by
    apply mul_pos <;> linarith
  have hlow : 0≤4*(k-1)*(N-k-1)-k*(N-k) := by
    have hprod : 0≤(k-2)*(N-k-2) := by
      apply mul_nonneg <;> linarith
    nlinarith
  have hshape : (k*(N-k))^2≤
      4*((N-k)*(N-k-1)*(k*(k-1))) := by
    have hmul := mul_nonneg (le_of_lt hb) hlow
    nlinarith only [hmul]
  have hbalance : N^2*
      ((N-k)*(N-k-1)*(k*(k-1)))≤
      (k*(N-k))^2*(N-2)^2 := by
    have hp : 0≤k*(N-k)*(N-1)*(N-2*k)^2 := by
      apply mul_nonneg
      · apply mul_nonneg (le_of_lt hb); linarith
      · positivity
    nlinarith only [hp]
  rw [realMargin_two_curvature_formula N k t hN hk hq]
  exact threePointVariance_finite_population_bound N _ _ _ _
    hN ha hb hc (Real.exp_pos t) hshape hbalance


/-- Equality in the real-margin two-draw curvature bound forces a balanced
success margin and zero tilt. -/
theorem realMargin_two_curvature_equality_necessary (N k t : ℝ) (hN : 2 < N)
    (hk : 2 ≤ k) (hq : k+2 ≤ N)
    (heq : deriv (deriv (fun u => Real.log (finiteMGF (range 3)
      (realMarginMass 2 (1/N) (k/N)) (fun i => (i:ℝ)) u))) t =
      (N-2)/(2*(N-1))) : N=2*k ∧ t=0 := by
  have ha : 0<(N-k)*(N-k-1) := by apply mul_pos <;> linarith
  have hb : 0<k*(N-k) := by apply mul_pos <;> linarith
  have hc : 0<k*(k-1) := by apply mul_pos <;> linarith
  have hlow : 0≤4*(k-1)*(N-k-1)-k*(N-k) := by
    have hprod : 0≤(k-2)*(N-k-2) := by apply mul_nonneg <;> linarith
    nlinarith
  have hshape : (k*(N-k))^2≤
      4*((N-k)*(N-k-1)*(k*(k-1))) := by
    have hmul := mul_nonneg hb.le hlow
    nlinarith only [hmul]
  have hbalance : N^2*
      ((N-k)*(N-k-1)*(k*(k-1)))≤
      (k*(N-k))^2*(N-2)^2 := by
    have hp : 0≤k*(N-k)*(N-1)*(N-2*k)^2 := by
      apply mul_nonneg
      · apply mul_nonneg hb.le; linarith
      · positivity
    nlinarith only [hp]
  rw [realMargin_two_curvature_formula N k t hN hk hq] at heq
  have hnec := threePointVariance_finite_population_equality_necessary N _ _ _ _
    (by linarith) ha hb hc (Real.exp_pos t) hshape hbalance heq
  have hprod : k*(N-k)*(N-1)*(N-2*k)^2=0 := by
    nlinarith only [hnec.1]
  have hfactor : k*(N-k)*(N-1)≠0 :=
    (mul_pos hb (by linarith : 0<N-1)).ne'
  have hN2k : N=2*k := by
    have := (mul_eq_zero.mp hprod).resolve_left hfactor
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)
  have htEq : (Real.exp t)^2=1 := by
    have hz := hnec.2
    rw [hN2k] at hz
    have haEq : (2*k-k)*(2*k-k-1)=k*(k-1) := by ring
    rw [haEq] at hz
    nlinarith
  have hzt : Real.exp t=1 := by nlinarith [Real.exp_pos t]
  exact ⟨hN2k, Real.exp_injective (by simpa using hzt)⟩


end
end ExactHoeffding
