import ExactHoeffding.RescaledHigherTiltInputs

/-! # All-order moment--cumulant recursion for actual finite laws -/

namespace ExactHoeffding
noncomputable section
open Finset
open scoped Topology

/-- A finite exponential sum is analytic at every real tilt. -/
theorem finiteMGF_analyticAt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) :
    AnalyticAt ℝ (finiteMGF s w x) t := by
  unfold finiteMGF
  fun_prop

/-- The moment--cumulant relation holds at every order for the actual
logarithm of a normalized finite MGF. -/
theorem finiteMGF_actual_moment_cumulant_recursion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (hs : ∑ i ∈ s, w i = 1) (n : ℕ) :
    finiteRawMoment s x w (n+1) =
      ∑ j ∈ Finset.range (n+1), (Nat.choose n j : ℝ) * finiteRawMoment s x w j *
        iteratedDeriv (n-j+1) (fun t => Real.log (finiteMGF s w x t)) 0 := by
  have h := analytic_log_derivative_recursion (finiteMGF s w x)
    (finiteMGF_analyticAt s w x 0) (finiteMGF_zero_of_normalized s w x hs) n
  simpa only [finiteMGF_iteratedDeriv_zero] using h

/-- The same all-order recurrence applies to every legal hypergeometric
population, including deterministic margins and populations of size zero. -/
theorem hypergeom_actual_moment_cumulant_recursion (N k m n : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomRawMoment N k m (n+1) =
      ∑ j ∈ Finset.range (n+1), (Nat.choose n j : ℝ) * hypergeomRawMoment N k m j *
        iteratedDeriv (n-j+1) (fun t => Real.log (hypergeomMGF N k m t)) 0 := by
  exact finiteMGF_actual_moment_cumulant_recursion (range (m+1))
    (hypergeomMass N k m) (fun i => (i : ℝ)) (hypergeomMass_total N k m hk hm) n

/-- Actual logarithmic derivatives at orders five and six agree with the
ordinary moment polynomials, without any auxiliary distribution. -/
theorem hypergeom_actual_log_derivatives_five_six (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    iteratedDeriv 5 (fun t => Real.log (hypergeomMGF N k m t)) 0 =
      cumulant5Polynomial (hypergeomRawMoment N k m 1) (hypergeomRawMoment N k m 2)
        (hypergeomRawMoment N k m 3) (hypergeomRawMoment N k m 4)
        (hypergeomRawMoment N k m 5) ∧
    iteratedDeriv 6 (fun t => Real.log (hypergeomMGF N k m t)) 0 =
      cumulant6Polynomial (hypergeomRawMoment N k m 1) (hypergeomRawMoment N k m 2)
        (hypergeomRawMoment N k m 3) (hypergeomRawMoment N k m 4)
        (hypergeomRawMoment N k m 5) (hypergeomRawMoment N k m 6) := by
  have ha := finiteMGF_analyticAt (range (m+1))
    (hypergeomMass N k m) (fun i => (i : ℝ)) 0
  have hz := hypergeomMGF_zero N k m hk hm
  constructor
  · simpa only [hypergeomMGF_iteratedDeriv_zero] using
      analytic_log_deriv5_polynomial (hypergeomMGF N k m) ha hz
  · simpa only [hypergeomMGF_iteratedDeriv_zero] using
      analytic_log_deriv6_polynomial (hypergeomMGF N k m) ha hz

end
end ExactHoeffding
