import ExactHoeffding.ThreePointTangent
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Explicit three-node Hermite basis

Each degree-five basis polynomial has zero values at the three nodes and
prescribed first derivatives. These are algebraic interpolation statements.
-/

namespace ExactHoeffding
open Polynomial

noncomputable def threeHermiteBasis (x y z : ℝ) : Polynomial ℝ :=
  C ((threePointWeight x y z) ^ 2) * (X - C x) * (X - C y) ^ 2 * (X - C z) ^ 2

noncomputable def threeHermitePolynomial (x y z b₁ b₂ b₃ : ℝ) : Polynomial ℝ :=
  C b₁ * threeHermiteBasis x y z + C b₂ * threeHermiteBasis y x z +
    C b₃ * threeHermiteBasis z x y

theorem threeHermiteBasis_values (x y z : ℝ) :
    (threeHermiteBasis x y z).eval x = 0 ∧
      (threeHermiteBasis x y z).eval y = 0 ∧ (threeHermiteBasis x y z).eval z = 0 := by
  simp [threeHermiteBasis]

theorem threeHermiteBasis_derivative_self (x y z : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) :
    (threeHermiteBasis x y z).derivative.eval x = 1 := by
  simp only [threeHermiteBasis, derivative_mul, derivative_C, derivative_X_sub_C,
    derivative_pow, eval_add, eval_mul, eval_C, eval_X, eval_sub, eval_pow, eval_one]
  simp only [sub_self, mul_zero, zero_mul, zero_add, add_zero, mul_one]
  unfold threePointWeight
  field_simp [sub_ne_zero.mpr hxy, sub_ne_zero.mpr hxz]

theorem threeHermiteBasis_derivative_other (x y z : ℝ) :
    (threeHermiteBasis x y z).derivative.eval y = 0 ∧
      (threeHermiteBasis x y z).derivative.eval z = 0 := by
  simp [threeHermiteBasis, derivative_mul, derivative_pow]

/-- A direct polynomial normal form makes the degree-five coefficient explicit. -/
theorem threeHermiteBasis_expansion (x y z : ℝ) :
    threeHermiteBasis x y z =
      C ((threePointWeight x y z) ^ 2) *
        (X ^ 5 - C (x + 2 * y + 2 * z) * X ^ 4 +
          C (2 * x * y + 2 * x * z + y ^ 2 + 4 * y * z + z ^ 2) * X ^ 3 -
          C (x * y ^ 2 + 4 * x * y * z + x * z ^ 2 + 2 * y ^ 2 * z + 2 * y * z ^ 2) * X ^ 2 +
          C (2 * x * y ^ 2 * z + 2 * x * y * z ^ 2 + y ^ 2 * z ^ 2) * X -
          C (x * y ^ 2 * z ^ 2)) := by
  unfold threeHermiteBasis
  simp only [map_add, map_mul, map_pow, map_ofNat]
  ring

theorem threeHermiteBasis_fifth_derivative (x y z : ℝ) :
    (Polynomial.derivative^[5]) (threeHermiteBasis x y z) =
      C (120 * (threePointWeight x y z) ^ 2) := by
  rw [threeHermiteBasis_expansion]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    derivative_add, derivative_sub, derivative_X_pow,
    derivative_C, derivative_X, derivative_mul]
  norm_num
  simp only [map_ofNat]
  ring

theorem threeHermitePolynomial_values (x y z b₁ b₂ b₃ : ℝ) :
    (threeHermitePolynomial x y z b₁ b₂ b₃).eval x = 0 ∧
      (threeHermitePolynomial x y z b₁ b₂ b₃).eval y = 0 ∧
      (threeHermitePolynomial x y z b₁ b₂ b₃).eval z = 0 := by
  simp [threeHermitePolynomial, threeHermiteBasis]

theorem threeHermitePolynomial_derivatives (x y z b₁ b₂ b₃ : ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (threeHermitePolynomial x y z b₁ b₂ b₃).derivative.eval x = b₁ ∧
      (threeHermitePolynomial x y z b₁ b₂ b₃).derivative.eval y = b₂ ∧
      (threeHermitePolynomial x y z b₁ b₂ b₃).derivative.eval z = b₃ := by
  simp only [threeHermitePolynomial, derivative_add, derivative_C_mul, eval_add, eval_mul, eval_C]
  rw [threeHermiteBasis_derivative_self x y z hxy hxz,
    (threeHermiteBasis_derivative_other y x z).1,
    (threeHermiteBasis_derivative_other z x y).1,
    (threeHermiteBasis_derivative_other x y z).1,
    threeHermiteBasis_derivative_self y x z hxy.symm hyz,
    (threeHermiteBasis_derivative_other z x y).2,
    (threeHermiteBasis_derivative_other x y z).2,
    (threeHermiteBasis_derivative_other y x z).2,
    threeHermiteBasis_derivative_self z x y hxz.symm hyz.symm]
  simp

theorem threeHermitePolynomial_fifth_derivative (x y z b₁ b₂ b₃ : ℝ) :
    (Polynomial.derivative^[5]) (threeHermitePolynomial x y z b₁ b₂ b₃) =
      C (120 * (b₁ * (threePointWeight x y z) ^ 2 +
        b₂ * (threePointWeight y x z) ^ 2 + b₃ * (threePointWeight z x y) ^ 2)) := by
  have hadd (n : ℕ) (P Q : Polynomial ℝ) :
      (Polynomial.derivative^[n]) (P + Q) =
        (Polynomial.derivative^[n]) P + (Polynomial.derivative^[n]) Q := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply', ih, derivative_add]
  simp only [threeHermitePolynomial, hadd, iterate_derivative_C_mul,
    threeHermiteBasis_fifth_derivative]
  simp only [← map_mul, ← map_add]
  congr 1
  ring

/-- The sixth polynomial derivative vanishes identically. -/
theorem threeHermitePolynomial_sixth_derivative (x y z b₁ b₂ b₃ : ℝ) :
    (Polynomial.derivative^[6]) (threeHermitePolynomial x y z b₁ b₂ b₃) = 0 := by
  rw [show 6 = 5 + 1 by rfl, Function.iterate_succ_apply',
    threeHermitePolynomial_fifth_derivative, derivative_C]

end ExactHoeffding
