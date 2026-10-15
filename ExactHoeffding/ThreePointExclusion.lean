import ExactHoeffding.ThreePointExponential
import ExactHoeffding.ThreePointCircleObjective
import Mathlib.Analysis.Real.Sqrt

/-!
# Excluding three distinct coordinates at a constrained exponential maximum

The constraint curve is constructed explicitly from the nodes. Both first-
and second-order necessary conditions are derived from the actual maximum.
-/

namespace ExactHoeffding
open Filter Topology

theorem pairedExponential_no_three_distinct_max (A B x y z : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B) (hxy : x < y) (hyz : y < z)
    (hmax : ∀ x' y' z' : ℝ, x' + y' + z' = x + y + z →
      x' ^ 2 + y' ^ 2 + z' ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 →
      pairedExponential A B x' + pairedExponential A B y' + pairedExponential A B z' ≤
        pairedExponential A B x + pairedExponential A B y + pairedExponential A B z) : False := by
  let c := (x + y + z) / 3
  let v₁ := x - c
  let v₂ := y - c
  let v₃ := z - c
  let η₁ := threePointWeight x y z
  let η₂ := threePointWeight y x z
  let η₃ := threePointWeight z x y
  let R := v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2
  let E := η₁ ^ 2 + η₂ ^ 2 + η₃ ^ 2
  have hv : v₁ + v₂ + v₃ = 0 := by dsimp [v₁, v₂, v₃, c]; ring
  have hη : η₁ + η₂ + η₃ = 0 := threePointWeight_sum x y z hxy.ne (hxy.trans hyz).ne hyz.ne
  have hfirst : x * η₁ + y * η₂ + z * η₃ = 0 :=
    threePointWeight_first_moment x y z hxy.ne (hxy.trans hyz).ne hyz.ne
  have horth : v₁ * η₁ + v₂ * η₂ + v₃ * η₃ = 0 := by
    dsimp [v₁, v₂, v₃]
    linear_combination hfirst - c * hη
  have hE : 0 < E := threePointWeight_sq_sum_pos x y z hxy.ne (hxy.trans hyz).ne
  have hR : 0 < R := by
    have hd : v₁ - v₂ ≠ 0 := by
      dsimp [v₁, v₂]
      intro h
      linarith
    have hp := sq_pos_of_ne_zero hd
    dsimp [R]
    nlinarith [sq_nonneg (v₁ + v₂), sq_nonneg v₃]
  let ω := Real.sqrt (E / R)
  have hωpos : 0 < ω := Real.sqrt_pos.mpr (div_pos hE hR)
  have hω : ω ≠ 0 := ne_of_gt hωpos
  have hnorm : E = ω ^ 2 * R := by
    dsimp [ω]
    rw [Real.sq_sqrt (le_of_lt (div_pos hE hR))]
    field_simp [ne_of_gt hR]
  have hx0 : c + v₁ = x := by dsimp [v₁]; ring
  have hy0 : c + v₂ = y := by dsimp [v₂]; ring
  have hz0 : c + v₃ = z := by dsimp [v₃]; ring
  let F := threeCircleObjective (pairedExponential A B) c v₁ v₂ v₃ η₁ η₂ η₃ ω
  have hFmax : IsLocalMax F 0 := by
    apply Filter.Eventually.of_forall
    intro s
    have hsum : circleCoordinate c v₁ η₁ ω s + circleCoordinate c v₂ η₂ ω s +
        circleCoordinate c v₃ η₃ ω s = x + y + z := by
      rw [threeCircle_sum c v₁ v₂ v₃ η₁ η₂ η₃ ω s hv hη]
      dsimp [c]
      ring
    have hsq : (circleCoordinate c v₁ η₁ ω s) ^ 2 + (circleCoordinate c v₂ η₂ ω s) ^ 2 +
        (circleCoordinate c v₃ η₃ ω s) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
      rw [threeCircle_sq_sum c v₁ v₂ v₃ η₁ η₂ η₃ ω s hω hv hη horth hnorm]
      dsimp [v₁, v₂, v₃, c]
      ring
    simpa only [F, threeCircleObjective, circleCoordinate_zero, hx0, hy0, hz0] using
      hmax (circleCoordinate c v₁ η₁ ω s) (circleCoordinate c v₂ η₂ ω s)
        (circleCoordinate c v₃ η₃ ω s) hsum hsq
  have hFderiv := threeCircleObjective_deriv_zero (pairedExponential A B)
    (pairedExponentialFirst A B) (pairedExponential_hasDerivAt A B)
    c v₁ v₂ v₃ η₁ η₂ η₃ ω hω
  rw [hx0, hy0, hz0] at hFderiv
  have hstationary : pairedExponentialFirst A B x * η₁ +
      pairedExponentialFirst A B y * η₂ + pairedExponentialFirst A B z * η₃ = 0 := by
    exact hFderiv.symm.trans hFmax.deriv_eq_zero
  obtain ⟨α, β, hxaff, hyaff, hzaff, hpositive⟩ :=
    pairedExponential_stationary_quadratic_positive A B x y z hA hB hAB hxy hyz hstationary
  have hFc : ContinuousAt F 0 :=
    (threeCircleObjective_hasDerivAt (pairedExponential A B) (pairedExponentialFirst A B)
      (pairedExponential_hasDerivAt A B) c v₁ v₂ v₃ η₁ η₂ η₃ ω 0 hω).continuousAt
  have hnonpos := ExactHoeffding.IsLocalMax.second_deriv_nonpos hFmax hFc
  have hFsecond := threeCircleObjective_second_deriv_zero
    (pairedExponential A B) (pairedExponentialFirst A B) (pairedExponential A B)
    (pairedExponential_hasDerivAt A B) (pairedExponentialFirst_hasDerivAt A B)
    c v₁ v₂ v₃ η₁ η₂ η₃ ω hω
  rw [hx0, hy0, hz0] at hFsecond
  change deriv (deriv F) 0 = _ at hFsecond
  have haffsum : pairedExponentialFirst A B x * v₁ +
      pairedExponentialFirst A B y * v₂ + pairedExponentialFirst A B z * v₃ = β * R := by
    rw [hxaff, hyaff, hzaff]
    dsimp [R]
    rw [← hx0, ← hy0, ← hz0]
    linear_combination (α + β * c) * hv
  rw [haffsum] at hFsecond
  have hcurv : deriv (deriv F) 0 =
      (pairedExponential A B x - β) * η₁ ^ 2 +
      (pairedExponential A B y - β) * η₂ ^ 2 +
      (pairedExponential A B z - β) * η₃ ^ 2 := by
    linear_combination hFsecond + β * hnorm
  rw [hcurv] at hnonpos
  exact (not_lt_of_ge hnonpos) hpositive

end ExactHoeffding
