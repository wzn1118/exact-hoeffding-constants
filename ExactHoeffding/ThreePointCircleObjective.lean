import ExactHoeffding.ThreePointCircle

namespace ExactHoeffding

noncomputable def threeCircleObjective (φ : ℝ → ℝ)
    (c v₁ v₂ v₃ η₁ η₂ η₃ ω s : ℝ) : ℝ :=
  φ (circleCoordinate c v₁ η₁ ω s) + φ (circleCoordinate c v₂ η₂ ω s) +
    φ (circleCoordinate c v₃ η₃ ω s)

noncomputable def threeCircleObjectiveFirst (φ' : ℝ → ℝ)
    (c v₁ v₂ v₃ η₁ η₂ η₃ ω s : ℝ) : ℝ :=
  φ' (circleCoordinate c v₁ η₁ ω s) * circleCoordinateFirst v₁ η₁ ω s +
    φ' (circleCoordinate c v₂ η₂ ω s) * circleCoordinateFirst v₂ η₂ ω s +
    φ' (circleCoordinate c v₃ η₃ ω s) * circleCoordinateFirst v₃ η₃ ω s

theorem threeCircleObjective_hasDerivAt (φ φ' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (c v₁ v₂ v₃ η₁ η₂ η₃ ω s : ℝ) (hω : ω ≠ 0) :
    HasDerivAt (threeCircleObjective φ c v₁ v₂ v₃ η₁ η₂ η₃ ω)
      (threeCircleObjectiveFirst φ' c v₁ v₂ v₃ η₁ η₂ η₃ ω s) s := by
  exact (((hd _).comp s (circleCoordinate_hasDerivAt c v₁ η₁ ω s hω)).add
    ((hd _).comp s (circleCoordinate_hasDerivAt c v₂ η₂ ω s hω))).add
    ((hd _).comp s (circleCoordinate_hasDerivAt c v₃ η₃ ω s hω))

theorem threeCircleObjective_deriv_zero (φ φ' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt φ (φ' x) x)
    (c v₁ v₂ v₃ η₁ η₂ η₃ ω : ℝ) (hω : ω ≠ 0) :
    deriv (threeCircleObjective φ c v₁ v₂ v₃ η₁ η₂ η₃ ω) 0 =
      φ' (c + v₁) * η₁ + φ' (c + v₂) * η₂ + φ' (c + v₃) * η₃ := by
  rw [(threeCircleObjective_hasDerivAt φ φ' hd c v₁ v₂ v₃ η₁ η₂ η₃ ω 0 hω).deriv]
  simp [threeCircleObjectiveFirst, circleCoordinate_zero, circleCoordinateFirst]

theorem threeCircleObjectiveFirst_hasDerivAt_zero (φ' φ'' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt φ' (φ'' x) x)
    (c v₁ v₂ v₃ η₁ η₂ η₃ ω : ℝ) (hω : ω ≠ 0) :
    HasDerivAt (threeCircleObjectiveFirst φ' c v₁ v₂ v₃ η₁ η₂ η₃ ω)
      (φ'' (c + v₁) * η₁ ^ 2 + φ'' (c + v₂) * η₂ ^ 2 + φ'' (c + v₃) * η₃ ^ 2 -
        ω ^ 2 * (φ' (c + v₁) * v₁ + φ' (c + v₂) * v₂ + φ' (c + v₃) * v₃)) 0 := by
  have hterm (v η : ℝ) : HasDerivAt
      (fun s => φ' (circleCoordinate c v η ω s) * circleCoordinateFirst v η ω s)
      (φ'' (c + v) * η ^ 2 - ω ^ 2 * φ' (c + v) * v) 0 := by
    have h := ((hd _).comp 0 (circleCoordinate_hasDerivAt c v η ω 0 hω)).mul
      (circleCoordinateFirst_hasDerivAt v η ω 0)
    apply h.congr_deriv
    simp only [Function.comp_apply, circleCoordinate_zero, circleCoordinateFirst, mul_zero,
      Real.sin_zero, Real.cos_zero, mul_one, zero_add, sub_zero]
    ring
  exact (((hterm v₁ η₁).add (hterm v₂ η₂)).add (hterm v₃ η₃)).congr_deriv (by ring)

theorem threeCircleObjective_second_deriv_zero (φ φ' φ'' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt φ (φ' x) x) (hd' : ∀ x, HasDerivAt φ' (φ'' x) x)
    (c v₁ v₂ v₃ η₁ η₂ η₃ ω : ℝ) (hω : ω ≠ 0) :
    deriv (deriv (threeCircleObjective φ c v₁ v₂ v₃ η₁ η₂ η₃ ω)) 0 =
      φ'' (c + v₁) * η₁ ^ 2 + φ'' (c + v₂) * η₂ ^ 2 + φ'' (c + v₃) * η₃ ^ 2 -
        ω ^ 2 * (φ' (c + v₁) * v₁ + φ' (c + v₂) * v₂ + φ' (c + v₃) * v₃) := by
  have hfirst : deriv (threeCircleObjective φ c v₁ v₂ v₃ η₁ η₂ η₃ ω) =
      threeCircleObjectiveFirst φ' c v₁ v₂ v₃ η₁ η₂ η₃ ω := by
    funext s
    exact (threeCircleObjective_hasDerivAt φ φ' hd c v₁ v₂ v₃ η₁ η₂ η₃ ω s hω).deriv
  rw [hfirst]
  exact (threeCircleObjectiveFirst_hasDerivAt_zero φ' φ'' hd' c v₁ v₂ v₃ η₁ η₂ η₃ ω hω).deriv

end ExactHoeffding
