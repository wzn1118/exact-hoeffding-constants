import ExactHoeffding.AllParameterCurvatureEquality

namespace ExactHoeffding

/--
The theorem contract for the frozen manuscript result
`Universal hypergeometric curvature` (Theorem `thm:curvature`, equation
`eq:curvature`).  The manuscript's `v_{N,k,m}(t)` is the variance of the
actual exponentially tilted hypergeometric law, represented by
`hypergeomTiltVariance`.
-/
theorem manuscript_thm_curvature_bound
    (N k m : ℕ) (_hN : 2 ≤ N)
    (_hk0 : 1 ≤ k) (hkN : k < N)
    (_hm0 : 1 ≤ m) (hmN : m < N) (t : ℝ) :
    hypergeomTiltVariance N k m t ≤
      min ((k : ℝ) * ((N : ℝ) - k)) ((m : ℝ) * ((N : ℝ) - m)) /
        (4 * ((N : ℝ) - 1)) := by
  have hk : k ≤ N := Nat.le_of_lt hkN
  have hm : m ≤ N := Nat.le_of_lt hmN
  exact hypergeomTiltVariance_sharp N k m hk hm t

/-- The singleton-mark equality case stated in the curvature theorem: when
`k=1`, a suitable exponential tilt attains the displayed sharp envelope. -/
theorem manuscript_thm_curvature_singleton_mark_attainment
    (N m : ℕ) (_hN : 2 ≤ N) (hm0 : 1 ≤ m) (hmN : m < N) :
    ∃ t : ℝ,
      hypergeomTiltVariance N 1 m t =
        min ((1 : ℝ) * ((N : ℝ) - 1))
            ((m : ℝ) * ((N : ℝ) - m)) /
          (4 * ((N : ℝ) - 1)) := by
  have hmpos : 0 < m := by omega
  have hEq := hypergeomTiltVariance_one_mark_equality_iff N m hmpos hmN
    (Real.log (((N : ℝ) - m) / m))
  refine ⟨Real.log (((N : ℝ) - m) / m), ?_⟩
  have hconstant : sharpCurvatureConstant N 1 m =
      min ((1 : ℝ) * ((N : ℝ) - 1))
          ((m : ℝ) * ((N : ℝ) - m)) /
        (4 * ((N : ℝ) - 1)) := by
    simp [sharpCurvatureConstant]
  rw [← hconstant]
  exact hEq.mpr rfl

/-- When both margin products are maximal (the balanced even-population
case), zero tilt attains the curvature envelope. -/
theorem manuscript_thm_curvature_balanced_zero_attainment
    (n : ℕ) (hn : 0 < n) :
    hypergeomTiltVariance (2 * n) n n 0 =
      min ((n : ℝ) * ((2 * n : ℝ) - n))
          ((n : ℝ) * ((2 * n : ℝ) - n)) /
        (4 * ((2 * n : ℝ) - 1)) := by
  have hnle : n ≤ 2 * n := by omega
  rw [hypergeomTiltVariance_zero (2 * n) n n hnle hnle]
  have hsubR : (2 * (n : ℝ)) - (n : ℝ) = (n : ℝ) := by ring
  rw [hsubR]
  rw [show 2 * n - n = n by omega]
  simp only [min_self]
  push_cast
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hden : 0 < (2 * (n : ℝ) - 1) := by linarith
  field_simp [hnR.ne', hden.ne']
  ring

/-- Exact equality classification in the non-singleton interior.  This makes
the zero-tilt equality clause precise: at least one margin is balanced; no
nonzero tilt attains equality there. -/
theorem manuscript_thm_curvature_interior_equality_iff
    (N k m : ℕ) (hk2 : 2 ≤ k) (hkN2 : k + 2 ≤ N)
    (hm2 : 2 ≤ m) (hmN2 : m + 2 ≤ N) (t : ℝ) :
    hypergeomTiltVariance N k m t =
      min ((k : ℝ) * ((N : ℝ) - k)) ((m : ℝ) * ((N : ℝ) - m)) /
        (4 * ((N : ℝ) - 1)) ↔
      t = 0 ∧ (2 * k = N ∨ 2 * m = N) := by
  have hk : k ≤ N := by omega
  have hm : m ≤ N := by omega
  have hEq := hypergeomTiltVariance_interior_equality_iff N k m
    hk2 hkN2 hm2 hmN2 t
  have hconstant : sharpCurvatureConstant N k m =
      min ((k : ℝ) * ((N : ℝ) - k)) ((m : ℝ) * ((N : ℝ) - m)) /
        (4 * ((N : ℝ) - 1)) := by
    rfl
  rw [← hconstant]
  exact hEq

/-- Whole-result statement contract for Theorem `thm:curvature`: the sharp
bound over all legal parameters, an explicit nonzero-tilt singleton equality,
the balanced zero-tilt equality, and the interior equality classification. -/
theorem manuscript_thm_curvature_contract :
    (∀ N k m : ℕ, 2 ≤ N → 1 ≤ k → k < N → 1 ≤ m → m < N → ∀ t : ℝ,
      hypergeomTiltVariance N k m t ≤
        min ((k : ℝ) * ((N : ℝ) - k)) ((m : ℝ) * ((N : ℝ) - m)) /
          (4 * ((N : ℝ) - 1))) ∧
    (∀ N m : ℕ, 2 ≤ N → 1 ≤ m → m < N →
      ∃ t : ℝ, hypergeomTiltVariance N 1 m t =
        min ((1 : ℝ) * ((N : ℝ) - 1)) ((m : ℝ) * ((N : ℝ) - m)) /
          (4 * ((N : ℝ) - 1))) ∧
    (∀ n : ℕ, 0 < n →
      hypergeomTiltVariance (2*n) n n 0 =
        min ((n : ℝ) * ((2*n : ℝ) - n)) ((n : ℝ) * ((2*n : ℝ) - n)) /
          (4 * ((2*n : ℝ) - 1))) ∧
    (∀ N k m : ℕ, 2 ≤ k → k + 2 ≤ N → 2 ≤ m → m + 2 ≤ N → ∀ t : ℝ,
      (hypergeomTiltVariance N k m t =
        min ((k : ℝ) * ((N : ℝ) - k)) ((m : ℝ) * ((N : ℝ) - m)) /
          (4 * ((N : ℝ) - 1))) ↔
        t = 0 ∧ (2*k = N ∨ 2*m = N)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N k m hN hk0 hkN hm0 hmN t
    exact manuscript_thm_curvature_bound N k m hN hk0 hkN hm0 hmN t
  · intro N m hN hm0 hmN
    exact manuscript_thm_curvature_singleton_mark_attainment N m hN hm0 hmN
  · intro n hn
    exact manuscript_thm_curvature_balanced_zero_attainment n hn
  · intro N k m hk2 hkN2 hm2 hmN2 t
    exact manuscript_thm_curvature_interior_equality_iff N k m hk2 hkN2 hm2 hmN2 t

end ExactHoeffding
