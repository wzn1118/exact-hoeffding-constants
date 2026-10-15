import ExactHoeffding.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Three-point tangent algebra for the two-level optimization argument

These are exact rational identities at three distinct real coordinates.
They do not assume any conclusion about a constrained maximizer.
-/

namespace ExactHoeffding

noncomputable def threePointWeight (x y z : ℝ) : ℝ := 1 / ((x - y) * (x - z))

theorem threePointWeight_sum (x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    threePointWeight x y z + threePointWeight y x z + threePointWeight z x y = 0 := by
  unfold threePointWeight
  field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxz, sub_ne_zero.mpr hyz,
    sub_ne_zero.mpr hxy.symm, sub_ne_zero.mpr hxz.symm, sub_ne_zero.mpr hyz.symm]
  ring

theorem threePointWeight_first_moment (x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    x * threePointWeight x y z + y * threePointWeight y x z +
      z * threePointWeight z x y = 0 := by
  unfold threePointWeight
  field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxz, sub_ne_zero.mpr hyz,
    sub_ne_zero.mpr hxy.symm, sub_ne_zero.mpr hxz.symm, sub_ne_zero.mpr hyz.symm]
  ring

theorem threePointWeight_second_moment (x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    x ^ 2 * threePointWeight x y z + y ^ 2 * threePointWeight y x z +
      z ^ 2 * threePointWeight z x y = 1 := by
  unfold threePointWeight
  field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxz, sub_ne_zero.mpr hyz,
    sub_ne_zero.mpr hxy.symm, sub_ne_zero.mpr hxz.symm, sub_ne_zero.mpr hyz.symm]
  ring

theorem threePointWeight_sq_sum_pos (x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) :
    0 < (threePointWeight x y z) ^ 2 + (threePointWeight y x z) ^ 2 +
      (threePointWeight z x y) ^ 2 := by
  have hw : threePointWeight x y z ≠ 0 := by
    unfold threePointWeight
    exact one_div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hxz))
  nlinarith [sq_pos_of_ne_zero hw, sq_nonneg (threePointWeight y x z),
    sq_nonneg (threePointWeight z x y)]

/-- Vanishing first derivative in the tangent direction makes the three
coordinate derivatives affine in their coordinate values. -/
theorem threePoint_tangent_stationary_affine (x y z g₁ g₂ g₃ : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : g₁ * threePointWeight x y z + g₂ * threePointWeight y x z +
      g₃ * threePointWeight z x y = 0) :
    ∃ α β : ℝ, g₁ = α + β * x ∧ g₂ = α + β * y ∧ g₃ = α + β * z := by
  let β := (g₂ - g₁) / (y - x)
  let α := g₁ - β * x
  have h₁ : g₁ = α + β * x := by dsimp [α]; ring
  have h₂ : g₂ = α + β * y := by
    dsimp [α, β]
    field_simp [sub_ne_zero.mpr hxy.symm]
    ring
  refine ⟨α, β, h₁, h₂, ?_⟩
  have hs := threePointWeight_sum x y z hxy hxz hyz
  have hx := threePointWeight_first_moment x y z hxy hxz hyz
  have hw : threePointWeight z x y ≠ 0 := by
    unfold threePointWeight
    exact one_div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hxz.symm) (sub_ne_zero.mpr hyz.symm))
  have hz : (g₃ - (α + β * z)) * threePointWeight z x y = 0 := by
    rw [h₁, h₂] at h
    linear_combination h - α * hs - β * hx
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hw)

end ExactHoeffding
