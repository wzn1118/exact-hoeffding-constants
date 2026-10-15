import ExactHoeffding.ThreePointHermitePositive
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ExactHoeffding

noncomputable def pairedExponential (A B x : ℝ) : ℝ := A * Real.exp x + B * Real.exp (-x)
noncomputable def pairedExponentialFirst (A B x : ℝ) : ℝ := A * Real.exp x - B * Real.exp (-x)

theorem pairedExponential_hasDerivAt (A B x : ℝ) :
    HasDerivAt (pairedExponential A B) (pairedExponentialFirst A B x) x := by
  have hneg := ((hasDerivAt_id x).neg.exp).const_mul B
  have h := ((Real.hasDerivAt_exp x).const_mul A).add hneg
  apply h.congr_deriv
  simp only [pairedExponentialFirst, Pi.neg_apply, id_eq, mul_neg]
  ring

theorem pairedExponentialFirst_hasDerivAt (A B x : ℝ) :
    HasDerivAt (pairedExponentialFirst A B) (pairedExponential A B x) x := by
  have hneg := ((hasDerivAt_id x).neg.exp).const_mul B
  have h := ((Real.hasDerivAt_exp x).const_mul A).sub hneg
  apply h.congr_deriv
  simp only [pairedExponential, Pi.neg_apply, id_eq, mul_neg]
  ring

theorem pairedExponential_pos (A B x : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B) :
    0 < pairedExponential A B x := by
  unfold pairedExponential
  have ha := mul_nonneg hA (le_of_lt (Real.exp_pos x))
  have hb := mul_nonneg hB (le_of_lt (Real.exp_pos (-x)))
  by_cases ha0 : A = 0
  · subst A
    have hB' : 0 < B := by linarith
    simpa using mul_pos hB' (Real.exp_pos (-x))
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hA (Ne.symm ha0)) (Real.exp_pos x)) hb

/-- The Hermite contradiction term is positive for every nontrivial
nonnegative pair of exponential coefficients and three stationary nodes. -/
theorem pairedExponential_hermite_positive (A B α β x y z : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B) (hxy : x < y) (hyz : y < z)
    (hx : pairedExponentialFirst A B x = α + β * x)
    (hy : pairedExponentialFirst A B y = α + β * y)
    (hz : pairedExponentialFirst A B z = α + β * z) :
    0 < (pairedExponential A B x - β) * (threePointWeight x y z) ^ 2 +
      (pairedExponential A B y - β) * (threePointWeight y x z) ^ 2 +
      (pairedExponential A B z - β) * (threePointWeight z x y) ^ 2 := by
  apply threePoint_hermite_weighted_derivative_pos
    (fun s => pairedExponentialFirst A B s - α - β * s)
    (fun s => pairedExponential A B s - β)
    (pairedExponentialFirst A B) (pairedExponential A B)
    (pairedExponentialFirst A B) (pairedExponential A B)
  · intro s
    exact (((pairedExponentialFirst_hasDerivAt A B s).sub_const α).sub
      ((hasDerivAt_id s).const_mul β)).congr_deriv (by ring)
  · intro s
    exact (pairedExponential_hasDerivAt A B s).sub_const β
  · exact pairedExponentialFirst_hasDerivAt A B
  · exact pairedExponential_hasDerivAt A B
  · exact pairedExponentialFirst_hasDerivAt A B
  · exact hxy
  · exact hyz
  · rw [hx]; ring
  · rw [hy]; ring
  · rw [hz]; ring
  · intro s hsx hsz
    exact pairedExponential_pos A B s hA hB hAB

/-- An affine stationary triple for the paired exponential has a strictly
positive constrained quadratic form. -/
theorem pairedExponential_stationary_quadratic_positive (A B x y z : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B) (hxy : x < y) (hyz : y < z)
    (hstationary : pairedExponentialFirst A B x * threePointWeight x y z +
      pairedExponentialFirst A B y * threePointWeight y x z +
      pairedExponentialFirst A B z * threePointWeight z x y = 0) :
    ∃ α β : ℝ,
      pairedExponentialFirst A B x = α + β * x ∧
      pairedExponentialFirst A B y = α + β * y ∧
      pairedExponentialFirst A B z = α + β * z ∧
      0 < (pairedExponential A B x - β) * (threePointWeight x y z) ^ 2 +
        (pairedExponential A B y - β) * (threePointWeight y x z) ^ 2 +
        (pairedExponential A B z - β) * (threePointWeight z x y) ^ 2 := by
  obtain ⟨α, β, hx, hy, hz⟩ := threePoint_tangent_stationary_affine x y z
    (pairedExponentialFirst A B x) (pairedExponentialFirst A B y)
    (pairedExponentialFirst A B z) hxy.ne (hxy.trans hyz).ne hyz.ne hstationary
  exact ⟨α, β, hx, hy, hz,
    pairedExponential_hermite_positive A B α β x y z hA hB hAB hxy hyz hx hy hz⟩

end ExactHoeffding
