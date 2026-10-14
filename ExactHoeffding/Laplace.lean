import ExactHoeffding.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Finite Laplace transforms and two-point tilting

The simple finite-support definitions here are the starting point for a
Mathlib measure-theoretic proof of the manuscript's hypergeometric Laplace
comparison. All theorems below are unconditional identities.
-/

namespace ExactHoeffding

/-- A finite weighted exponential moment. -/
noncomputable def finiteMGF {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (weights values : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, weights i * Real.exp (t * values i)

/-- Exponential moment at zero is precisely the total mass. -/
theorem finiteMGF_zero {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (weights values : ι → ℝ) :
    finiteMGF s weights values 0 = ∑ i ∈ s, weights i := by
  simp [finiteMGF]

/-- A normalized finite mass function has unit exponential moment at zero. -/
theorem finiteMGF_zero_of_normalized {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ)
    (h : ∑ i ∈ s, weights i = 1) :
    finiteMGF s weights values 0 = 1 := by
  simpa [finiteMGF_zero] using h

/-- Nonnegative weights give a nonnegative exponential moment. -/
theorem finiteMGF_nonneg {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (weights values : ι → ℝ) (t : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weights i) :
    0 ≤ finiteMGF s weights values t := by
  unfold finiteMGF
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hw i hi) (le_of_lt (Real.exp_pos _))

/-- A weighted exponential moment transforms under a constant shift exactly. -/
theorem finiteMGF_shift {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (weights values : ι → ℝ) (t c : ℝ) :
    finiteMGF s weights (fun i => values i + c) t =
      Real.exp (t * c) * finiteMGF s weights values t := by
  simp only [finiteMGF, mul_add, Real.exp_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The Bernoulli exponential moment, with mass `p` at one. -/
noncomputable def bernoulliMGF (p t : ℝ) : ℝ :=
  1 - p + p * Real.exp t

/-- An exact Bernoulli balance identity at the log-odds tilt.
    This is the algebraic core of the odd-population sharp example. -/
theorem bernoulli_log_odds_balance (p : ℝ)
    (hp : 0 < p) (hq : p < 1) :
    bernoulliMGF p (2 * Real.log ((1 - p) / p)) = (1 - p) / p := by
  have hpos : 0 < (1 - p) / p := div_pos (by linarith) hp
  have hexp : Real.exp (Real.log ((1 - p) / p)) = (1 - p) / p :=
    Real.exp_log hpos
  unfold bernoulliMGF
  rw [show 2 * Real.log ((1 - p) / p) =
    Real.log ((1 - p) / p) + Real.log ((1 - p) / p) by ring,
    Real.exp_add, hexp]
  have hp0 : p ≠ 0 := ne_of_gt hp
  field_simp
  ring

end ExactHoeffding
