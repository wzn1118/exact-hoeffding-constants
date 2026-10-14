import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite Poisson-binomial mean-variance algebra

This file isolates the finite-dimensional inequality used after a Jacobi
factorization.  The Jacobi factorization itself is deliberately not assumed
here: the theorem below only takes a finite list of Bernoulli parameters as
input.
-/

namespace ExactHoeffding

/-- A finite list of real parameters satisfies the mean-variance bound for a
sum of independent Bernoulli variables.  The proof is the finite Cauchy--
Schwarz inequality, so the algebraic estimate itself does not need the
parameter bounds `0 ≤ p i ≤ 1`. -/
theorem finite_mean_variance_bound {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) :
    (∑ i, p i * (1 - p i)) ≤
      (∑ i, p i) * ((n : ℝ) - ∑ i, p i) / (n : ℝ) := by
  let s : ℝ := ∑ i, p i
  let q : ℝ := ∑ i, p i ^ 2
  have hcs : s ^ 2 ≤ (n : ℝ) * q := by
    have h :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
        (Finset.univ : Finset (Fin n))
        (r := p) (f := fun i => p i ^ 2) (g := fun _ => (1 : ℝ))
        (by
          intro i hi
          exact sq_nonneg (p i))
        (by
          intro i hi
          norm_num)
        (by
          intro i hi
          simp)
    simpa [s, q, Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm] using h
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hsum : (∑ i, p i * (1 - p i)) = s - q := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    simp [s, q, pow_two]
  rw [hsum]
  apply (le_div_iff₀ hn0).2
  nlinarith [hcs]

/-- The same mean-variance bound with the usual Poisson-binomial parameter
hypotheses made explicit.  The factorization from a Jacobi polynomial, when
available, can instantiate this interface with its tilted Bernoulli
parameters. -/
theorem poissonBinomial_variance_bound {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℝ) (_hp0 : ∀ i, 0 ≤ p i) (_hp1 : ∀ i, p i ≤ 1) :
    (∑ i, p i * (1 - p i)) ≤
      (∑ i, p i) * ((n : ℝ) - ∑ i, p i) / (n : ℝ) := by
  exact finite_mean_variance_bound hn p

/-- Bernoulli parameter bounds make each summand in the Poisson-binomial
variance nonnegative. -/
theorem poissonBinomial_variance_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    0 ≤ ∑ i, p i * (1 - p i) := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hp0 i) (sub_nonneg.mpr (hp1 i))

end ExactHoeffding
