import ExactHoeffding.ManuscriptIntegerTails

/-!
# Typed contract for the manuscript's integer and two-sided tail corollary

The contract states the ceiling and floor event identities, the disjoint
upper/lower decomposition, support cutoffs, and the capped two-sided bound for
the actual hypergeometric finite law under the parameter domain of
`A:piecewise`.
-/

namespace ExactHoeffding
noncomputable section

/-- Whole-result statement contract for the manuscript's unlabelled
`Integer and two-sided events` corollary. -/
theorem manuscript_integer_two_sided_contract (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2 * k ≤ N) (hhalf : 2 * m < N)
    (x : ℝ) (hx : 0 < x) :
    (hypergeomUpperDeviationMass N k m x =
      ∑ i ∈ Finset.range (m + 1),
        if (Int.ceil ((m : ℝ) * k / N + x) : ℝ) ≤ (i : ℝ)
        then hypergeomMass N k m i else 0) ∧
    (hypergeomLowerDeviationMass N k m x =
      ∑ i ∈ Finset.range (m + 1),
        if (i : ℝ) ≤ (Int.floor ((m : ℝ) * k / N - x) : ℝ)
        then hypergeomMass N k m i else 0) ∧
    hypergeomTwoSidedDeviationMass N k m x =
      hypergeomUpperDeviationMass N k m x + hypergeomLowerDeviationMass N k m x ∧
    hypergeomUpperDeviationMass N k m x ≤
      (if Int.ceil ((m : ℝ) * k / N + x) ≤ (m : ℤ) then
        Real.exp (-canonicalPiecewiseRate N k m
          (Int.ceil ((m : ℝ) * k / N + x) : ℝ)) else 0) ∧
    hypergeomLowerDeviationMass N k m x ≤
      (if (0 : ℤ) ≤ Int.floor ((m : ℝ) * k / N - x) then
        Real.exp (-canonicalPiecewiseRate N k m
          (Int.floor ((m : ℝ) * k / N - x) : ℝ)) else 0) ∧
    hypergeomTwoSidedDeviationMass N k m x ≤
      min 1 ((if Int.ceil ((m : ℝ) * k / N + x) ≤ (m : ℤ) then
          Real.exp (-canonicalPiecewiseRate N k m
            (Int.ceil ((m : ℝ) * k / N + x) : ℝ)) else 0) +
        (if (0 : ℤ) ≤ Int.floor ((m : ℝ) * k / N - x) then
          Real.exp (-canonicalPiecewiseRate N k m
            (Int.floor ((m : ℝ) * k / N - x) : ℝ)) else 0)) := by
  exact ⟨hypergeomUpperDeviationMass_eq_ceil_tail N k m x,
    hypergeomLowerDeviationMass_eq_floor_tail N k m x,
    hypergeomTwoSidedDeviationMass_eq_sum N k m x hx,
    hypergeom_integer_upper_deviation_piecewise_kl N k m hm hmk hk hhalf x hx,
    hypergeom_integer_lower_deviation_piecewise_kl N k m hm hmk hk hhalf x hx,
    hypergeom_integer_two_sided_deviation_piecewise_kl N k m hm hmk hk hhalf x hx⟩

end
end ExactHoeffding
