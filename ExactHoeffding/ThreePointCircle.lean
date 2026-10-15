import ExactHoeffding.ThreePointTangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Constraint-preserving circle coordinates and the second derivative condition

The one-dimensional maximum condition is proved from local extremality,
not assumed as a constrained Hessian inequality.
-/

namespace ExactHoeffding
open Filter Topology

/-- A twice-differentiable real function cannot have positive second derivative
at a genuine local maximum. -/
theorem IsLocalMax.second_deriv_nonpos {f : ℝ → ℝ} {x : ℝ}
    (hmax : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin : IsLocalMin f x := isLocalMin_of_deriv_deriv_pos hp hmax.deriv_eq_zero hc
  have heq : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hmax, hmin] with y hymax hymin
    exact le_antisymm hymax hymin
  have hd := heq.deriv.deriv_eq
  have hz : deriv (deriv f) x = 0 := by simpa using hd
  linarith

noncomputable def circleCoordinate (c v η ω s : ℝ) : ℝ :=
  c + v * Real.cos (ω * s) + η / ω * Real.sin (ω * s)

noncomputable def circleCoordinateFirst (v η ω s : ℝ) : ℝ :=
  -v * ω * Real.sin (ω * s) + η * Real.cos (ω * s)

theorem circleCoordinate_zero (c v η ω : ℝ) : circleCoordinate c v η ω 0 = c + v := by
  simp [circleCoordinate]

theorem circleCoordinate_hasDerivAt (c v η ω s : ℝ) (hω : ω ≠ 0) :
    HasDerivAt (circleCoordinate c v η ω) (circleCoordinateFirst v η ω s) s := by
  have hωs : HasDerivAt (fun r : ℝ => ω * r) ω s := by
    simpa using (hasDerivAt_id s).const_mul ω
  have hcalc := (((hωs.cos).const_mul v).const_add c).add ((hωs.sin).const_mul (η / ω))
  apply hcalc.congr_deriv
  unfold circleCoordinateFirst
  field_simp [hω]

theorem circleCoordinateFirst_hasDerivAt (v η ω s : ℝ) :
    HasDerivAt (circleCoordinateFirst v η ω)
      (-v * ω ^ 2 * Real.cos (ω * s) - η * ω * Real.sin (ω * s)) s := by
  have hωs : HasDerivAt (fun r : ℝ => ω * r) ω s := by
    simpa using (hasDerivAt_id s).const_mul ω
  have hcalc := ((hωs.sin).const_mul (-v * ω)).add ((hωs.cos).const_mul η)
  apply hcalc.congr_deriv
  ring

theorem circleCoordinate_deriv_zero (c v η ω : ℝ) (hω : ω ≠ 0) :
    deriv (circleCoordinate c v η ω) 0 = η := by
  rw [(circleCoordinate_hasDerivAt c v η ω 0 hω).deriv]
  simp [circleCoordinateFirst]

theorem circleCoordinate_second_deriv_zero (c v η ω : ℝ) (hω : ω ≠ 0) :
    deriv (deriv (circleCoordinate c v η ω)) 0 = -v * ω ^ 2 := by
  have hd : deriv (circleCoordinate c v η ω) = circleCoordinateFirst v η ω := by
    funext s
    exact (circleCoordinate_hasDerivAt c v η ω s hω).deriv
  rw [hd, (circleCoordinateFirst_hasDerivAt v η ω 0).deriv]
  simp

/-- Three circle coordinates preserve their sum when the centered and tangent
vectors each have zero sum. -/
theorem threeCircle_sum (c v₁ v₂ v₃ η₁ η₂ η₃ ω s : ℝ)
    (hv : v₁ + v₂ + v₃ = 0) (hη : η₁ + η₂ + η₃ = 0) :
    circleCoordinate c v₁ η₁ ω s + circleCoordinate c v₂ η₂ ω s +
      circleCoordinate c v₃ η₃ ω s = 3 * c := by
  unfold circleCoordinate
  linear_combination Real.cos (ω * s) * hv + Real.sin (ω * s) / ω * hη

/-- Orthogonal centered and tangent directions give a constant squared norm
on the constraint circle when their speeds are matched. -/
theorem threeCircle_sq_sum (c v₁ v₂ v₃ η₁ η₂ η₃ ω s : ℝ)
    (hω : ω ≠ 0) (hv : v₁ + v₂ + v₃ = 0) (hη : η₁ + η₂ + η₃ = 0)
    (horth : v₁ * η₁ + v₂ * η₂ + v₃ * η₃ = 0)
    (hnorm : η₁ ^ 2 + η₂ ^ 2 + η₃ ^ 2 = ω ^ 2 * (v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2)) :
    (circleCoordinate c v₁ η₁ ω s) ^ 2 + (circleCoordinate c v₂ η₂ ω s) ^ 2 +
      (circleCoordinate c v₃ η₃ ω s) ^ 2 = 3 * c ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 := by
  have htrig := Real.sin_sq_add_cos_sq (ω * s)
  unfold circleCoordinate
  field_simp [hω]
  linear_combination
    2 * c * ω ^ 2 * Real.cos (ω * s) * hv +
    2 * c * ω * Real.sin (ω * s) * hη +
    2 * ω * Real.cos (ω * s) * Real.sin (ω * s) * horth +
    (Real.sin (ω * s)) ^ 2 * hnorm +
    ω ^ 2 * (v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) * htrig

end ExactHoeffding
