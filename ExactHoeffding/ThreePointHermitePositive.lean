import ExactHoeffding.ThreePointHermite
import ExactHoeffding.ThreePointRolle

/-!
# Positive Hermite coefficient from a positive fifth derivative

The conclusion follows by applying the proved three-double-zero Rolle chain
to a function minus its explicit Hermite polynomial.
-/

namespace ExactHoeffding

theorem threePoint_hermite_weighted_derivative_pos
    (f₀ f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ)
    (hd₀ : ∀ s, HasDerivAt f₀ (f₁ s) s)
    (hd₁ : ∀ s, HasDerivAt f₁ (f₂ s) s)
    (hd₂ : ∀ s, HasDerivAt f₂ (f₃ s) s)
    (hd₃ : ∀ s, HasDerivAt f₃ (f₄ s) s)
    (hd₄ : ∀ s, HasDerivAt f₄ (f₅ s) s)
    (x y z : ℝ) (hxy : x < y) (hyz : y < z)
    (h₀x : f₀ x = 0) (h₀y : f₀ y = 0) (h₀z : f₀ z = 0)
    (h₅ : ∀ s, x < s → s < z → 0 < f₅ s) :
    0 < f₁ x * (threePointWeight x y z) ^ 2 +
      f₁ y * (threePointWeight y x z) ^ 2 + f₁ z * (threePointWeight z x y) ^ 2 := by
  let P := threeHermitePolynomial x y z (f₁ x) (f₁ y) (f₁ z)
  let Q (n : ℕ) := (Polynomial.derivative^[n]) P
  have hQ (n : ℕ) (s : ℝ) :
      HasDerivAt (fun u => (Q n).eval u) ((Q (n + 1)).eval s) s := by
    simpa only [Q, Function.iterate_succ_apply'] using (Q n).hasDerivAt s
  have hvalues := threeHermitePolynomial_values x y z (f₁ x) (f₁ y) (f₁ z)
  have hderivs := threeHermitePolynomial_derivatives x y z (f₁ x) (f₁ y) (f₁ z)
    hxy.ne (hxy.trans hyz).ne hyz.ne
  obtain ⟨c, hxc, hcz, hc⟩ := three_double_zeros_fifth_zero
    (fun s => f₀ s - (Q 0).eval s) (fun s => f₁ s - (Q 1).eval s)
    (fun s => f₂ s - (Q 2).eval s) (fun s => f₃ s - (Q 3).eval s)
    (fun s => f₄ s - (Q 4).eval s) (fun s => f₅ s - (Q 5).eval s)
    (fun s => (hd₀ s).sub (hQ 0 s)) (fun s => (hd₁ s).sub (hQ 1 s))
    (fun s => (hd₂ s).sub (hQ 2 s)) (fun s => (hd₃ s).sub (hQ 3 s))
    (fun s => (hd₄ s).sub (hQ 4 s)) x y z hxy hyz
    (by simp only [Q, Function.iterate_zero_apply, P, hvalues.1, h₀x, sub_self])
    (by simp only [Q, Function.iterate_zero_apply, P, hvalues.2.1, h₀y, sub_self])
    (by simp only [Q, Function.iterate_zero_apply, P, hvalues.2.2, h₀z, sub_self])
    (by simp only [Q, Function.iterate_one, P, hderivs.1, sub_self])
    (by simp only [Q, Function.iterate_one, P, hderivs.2.1, sub_self])
    (by simp only [Q, Function.iterate_one, P, hderivs.2.2, sub_self])
  have hp := h₅ c hxc hcz
  dsimp only [Q, P] at hc
  rw [threeHermitePolynomial_fifth_derivative, Polynomial.eval_C] at hc
  linarith

end ExactHoeffding
