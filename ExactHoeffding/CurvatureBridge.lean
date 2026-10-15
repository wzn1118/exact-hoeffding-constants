import ExactHoeffding.Laplace
import Mathlib.Analysis.Convex.Deriv

/-!
# From a curvature certificate to a quadratic Laplace envelope

This module isolates an analytical implication used in the manuscript.
If the gap between a candidate quadratic bound and a centered log-Laplace
transform has nonnegative second derivative everywhere, its zero value and
zero first derivative at the origin imply a global Laplace bound.

The hypergeometric curvature certificate itself remains a separate proof
obligation; this module does not assume it as an axiom.
-/

namespace ExactHoeffding

/-- Every point lies above a stationary point of a differentiable
convex real-valued function. -/
theorem convex_stationary_global_minimum (f : ℝ → ℝ)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hstationary : HasDerivAt f 0 0) (x : ℝ) :
    f 0 ≤ f x := by
  rcases lt_trichotomy x 0 with hlt | heq | hgt
  · have hs : slope f x 0 ≤ 0 :=
      hconvex.slope_le_of_hasDerivAt (by simp) (by simp) hlt hstationary
    exact (slope_nonpos_iff_of_le (le_of_lt hlt)).mp hs
  · simpa [heq]
  · have hs : 0 ≤ slope f 0 x :=
      hconvex.le_slope_of_hasDerivAt (by simp) (by simp) hgt hstationary
    exact (slope_nonneg_iff_of_le (le_of_lt hgt)).mp hs

/-- A globally convex and stationary quadratic gap gives a global
two-sided quadratic Laplace envelope. -/
theorem quadratic_envelope_of_convex_gap (ψ : ℝ → ℝ) (C : ℝ)
    (hconvex : ConvexOn ℝ Set.univ (fun t => C * t ^ 2 / 2 - ψ t))
    (hstationary :
      HasDerivAt (fun t => C * t ^ 2 / 2 - ψ t) 0 0)
    (hzero : ψ 0 = 0) (t : ℝ) :
    ψ t ≤ C * t ^ 2 / 2 := by
  have hm := convex_stationary_global_minimum
    (fun x => C * x ^ 2 / 2 - ψ x) hconvex hstationary t
  have hnonneg : 0 ≤ C * t ^ 2 / 2 - ψ t := by
    simpa [hzero] using hm
  linarith

/-- A nonnegative second derivative of the quadratic gap is a
kernel-checkable sufficient condition for the Laplace inequality. -/
theorem quadratic_envelope_of_gap_second_derivative
    (ψ : ℝ → ℝ) (C : ℝ)
    (hdiff : Differentiable ℝ (fun t => C * t ^ 2 / 2 - ψ t))
    (hdiff' : Differentiable ℝ
      (deriv (fun t => C * t ^ 2 / 2 - ψ t)))
    (hcurv : ∀ t : ℝ,
      0 ≤ deriv^[2] (fun x => C * x ^ 2 / 2 - ψ x) t)
    (hstationary :
      HasDerivAt (fun t => C * t ^ 2 / 2 - ψ t) 0 0)
    (hzero : ψ 0 = 0) (t : ℝ) :
    ψ t ≤ C * t ^ 2 / 2 := by
  exact quadratic_envelope_of_convex_gap ψ C
    (convexOn_univ_of_deriv2_nonneg hdiff hdiff' hcurv)
    hstationary hzero t

end ExactHoeffding
