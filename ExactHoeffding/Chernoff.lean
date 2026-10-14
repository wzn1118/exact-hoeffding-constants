import ExactHoeffding.Laplace

/-!
# Finite-support Markov/Chernoff bridge

This module records the finite weighted exponential-Markov step used before
any Bernoulli or hypergeometric specialization.  It is deliberately stated
with explicit nonnegativity and event-threshold hypotheses.
-/

namespace ExactHoeffding

/-- Finite weighted exponential Markov inequality.

The left side is the total weight of an event on which `a ≤ values`.  The
right side is the exponential moment at a nonnegative tilt, multiplied by
`exp (-t * a)`.  No normalization or probabilistic interpretation is
assumed; normalization can be supplied by `finiteMGF_zero_of_normalized`.
-/
theorem finite_markov_exp_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ)
    (event : ι → Prop) [DecidablePred event]
    (hw : ∀ i ∈ s, 0 ≤ weights i)
    (t a : ℝ) (ht : 0 ≤ t)
    (hevent : ∀ i ∈ s, event i → a ≤ values i) :
    (∑ i ∈ s, if event i then weights i else 0) ≤
      Real.exp (-t * a) * finiteMGF s weights values t := by
  have hpoint : ∀ i ∈ s,
      (if event i then weights i else 0) ≤
        Real.exp (-t * a) * (weights i * Real.exp (t * values i)) := by
    intro i hi
    by_cases hev : event i
    · have hvalue : 0 ≤ t * (values i - a) := by
        exact mul_nonneg ht (sub_nonneg.mpr (hevent i hi hev))
      have hexp : 1 ≤ Real.exp (t * (values i - a)) :=
        Real.one_le_exp hvalue
      have hmul := mul_le_mul_of_nonneg_left hexp (hw i hi)
      rw [if_pos hev]
      calc
        weights i = weights i * 1 := by ring
        _ ≤ weights i * Real.exp (t * (values i - a)) := hmul
        _ = Real.exp (-t * a) * (weights i * Real.exp (t * values i)) := by
          calc
            weights i * Real.exp (t * (values i - a)) =
                weights i * (Real.exp (-t * a) * Real.exp (t * values i)) := by
                  rw [← Real.exp_add]
                  congr 2
                  ring
            _ = Real.exp (-t * a) * (weights i * Real.exp (t * values i)) := by
              ring
    · rw [if_neg hev]
      exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (mul_nonneg (hw i hi) (le_of_lt (Real.exp_pos _)))
  calc
    (∑ i ∈ s, if event i then weights i else 0) ≤
        ∑ i ∈ s, Real.exp (-t * a) *
          (weights i * Real.exp (t * values i)) := by
      exact Finset.sum_le_sum (fun i hi => hpoint i hi)
    _ = Real.exp (-t * a) * finiteMGF s weights values t := by
      simp only [finiteMGF, Finset.mul_sum]

end ExactHoeffding
