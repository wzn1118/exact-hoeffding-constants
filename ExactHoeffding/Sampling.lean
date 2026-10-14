import ExactHoeffding.Normalization

/-!
# Sampling and centering of the finite-population Laplace transform

This module connects the normalized combinatorial hypergeometric mass to its
finite exponential moment. In the one-draw case it proves an exact equality
with the Bernoulli MGF used in the manuscript's odd-population example.
-/

namespace ExactHoeffding

/-- For a valid population and a single draw, the hypergeometric MGF
is exactly the Bernoulli MGF with success probability k/N. -/
theorem hypergeomMGF_singleton (N k : ℕ) (hk : k ≤ N)
    (hN : 0 < N) (t : ℝ) :
    hypergeomMGF N k 1 t = bernoulliMGF ((k : ℝ) / N) t := by
  simp [hypergeomMGF, finiteMGF, bernoulliMGF,
    Finset.sum_range_succ, hypergeomMass_one_success,
    hypergeomMass_one_failure_complement N k hk hN]

/-- An explicitly centered hypergeometric exponential moment. -/
noncomputable def centeredHypergeomMGF (N k m : ℕ) (t : ℝ) : ℝ :=
  finiteMGF (Finset.range (m + 1)) (hypergeomMass N k m)
    (fun i => (i : ℝ) - (k : ℝ) * (m : ℝ) / (N : ℝ)) t

/-- Translation of the hypergeometric statistic gives the exact
multiplicative centering factor, for any finite parameters. -/
theorem centeredHypergeomMGF_factor (N k m : ℕ) (t : ℝ) :
    centeredHypergeomMGF N k m t =
      Real.exp (t * (-(k : ℝ) * (m : ℝ) / (N : ℝ))) *
        hypergeomMGF N k m t := by
  simpa only [centeredHypergeomMGF, hypergeomMGF, sub_eq_add_neg,
    neg_div, neg_mul] using
    (finiteMGF_shift (Finset.range (m + 1))
      (hypergeomMass N k m) (fun i => (i : ℝ)) t
      (-((k : ℝ) * (m : ℝ) / (N : ℝ))))

/-- The one-draw centered hypergeometric MGF is a centered Bernoulli
moment, an exact finite-N identity. -/
theorem centeredHypergeomMGF_singleton (N k : ℕ) (hk : k ≤ N)
    (hN : 0 < N) (t : ℝ) :
    centeredHypergeomMGF N k 1 t =
      Real.exp (t * (-((k : ℝ) / N))) * bernoulliMGF ((k : ℝ) / N) t := by
  rw [centeredHypergeomMGF_factor, hypergeomMGF_singleton N k hk hN]
  simp only [Nat.cast_one, mul_one, neg_div]

end ExactHoeffding
