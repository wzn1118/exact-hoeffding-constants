import ExactHoeffding.TiltedVariance

/-!
# Nonnegative curvature of finite log-Laplace transforms

This is a full finite-dimensional Cauchy–Schwarz proof that exponential
tilting produces a nonnegative variance. The argument applies to every
nonnegative finite probability law, and in particular to every admissible
hypergeometric law from the paper. It is not the sharp *upper* curvature
bound required by the main theorem.
-/

namespace ExactHoeffding

/-- Cauchy–Schwarz for the exact first two tilted moments. -/
theorem finiteTilt_cauchy_schwarz {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weights i) (t : ℝ) :
    (finiteTiltFirst s weights values t) ^ 2 ≤
      finiteMGF s weights values t * finiteTiltSecond s weights values t := by
  let a : ι → ℝ := fun i => weights i * Real.exp (t * values i)
  have ha : ∀ i ∈ s, 0 ≤ a i := by
    intro i hi
    exact mul_nonneg (hw i hi) (le_of_lt (Real.exp_pos _))
  have hcs :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (r := fun i => a i * values i)
      (f := a)
      (g := fun i => a i * values i ^ 2)
      ha
      (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))
      (fun i hi => by
        dsimp only
        nlinarith [sq_nonneg (a i), sq_nonneg (values i)])
  have hA : (∑ i ∈ s, a i) = finiteMGF s weights values t := rfl
  have hB : (∑ i ∈ s, a i * values i) =
      finiteTiltFirst s weights values t := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [a, finiteTiltFirst]
    ring
  have hC : (∑ i ∈ s, a i * values i ^ 2) =
      finiteTiltSecond s weights values t := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [a, finiteTiltSecond]
    ring
  rw [hA, hB, hC] at hcs
  exact hcs

/-- Log-Laplace curvature is nonnegative at every real tilt, for every
normalized finite nonnegative law. -/
theorem finiteLogMGF_second_deriv_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weights i)
    (hs : ∑ i ∈ s, weights i = 1) (t : ℝ) :
    0 ≤ deriv (deriv (fun u => Real.log (finiteMGF s weights values u))) t := by
  rw [finiteLogMGF_second_deriv s weights values hw hs t]
  apply div_nonneg
  · nlinarith [finiteTilt_cauchy_schwarz s weights values hw t]
  · positivity

/-- The hypergeometric log-MGF is convex in tilt at the level of its
second derivative for all N,k,m with k,m ≤ N. -/
theorem hypergeomLogMGF_second_deriv_nonneg
    (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    0 ≤ deriv (deriv (fun u => Real.log (hypergeomMGF N k m u))) t := by
  exact finiteLogMGF_second_deriv_nonneg
    (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i)
    (hypergeomMass_total N k m hk hm) t

end ExactHoeffding
