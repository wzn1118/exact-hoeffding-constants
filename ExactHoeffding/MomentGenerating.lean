import ExactHoeffding.Normalization
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiation of finite exponential moments

We formalize first and second raw tilted moments as derivatives of a finite
Laplace transform. In particular these statements apply to the exact
hypergeometric probability mass function, without numerical approximation.
-/

namespace ExactHoeffding

/-- The first unnormalized tilted moment of a finite law. -/
noncomputable def finiteTiltFirst {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, weights i * (values i * Real.exp (t * values i))

/-- The second unnormalized tilted moment of a finite law. -/
noncomputable def finiteTiltSecond {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, weights i * (values i ^ 2 * Real.exp (t * values i))

/-- Exact first derivative of the finite exponential moment. -/
theorem finiteMGF_hasDerivAt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ) (t : ℝ) :
    HasDerivAt (finiteMGF s weights values)
      (finiteTiltFirst s weights values t) t := by
  have hi (i : ι) : HasDerivAt
      (fun τ : ℝ => weights i * Real.exp (τ * values i))
      (weights i * (values i * Real.exp (t * values i))) t := by
    have hinner : HasDerivAt (fun τ : ℝ => τ * values i) (values i) t := by
      simpa using (hasDerivAt_id t).mul_const (values i)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (hinner.exp).const_mul (weights i)
  change HasDerivAt
    (fun τ : ℝ => ∑ i ∈ s, weights i * Real.exp (τ * values i))
    (∑ i ∈ s, weights i * (values i * Real.exp (t * values i))) t
  exact (HasDerivAt.fun_sum (u := s)
      (A := fun i τ => weights i * Real.exp (τ * values i))
      (A' := fun i => weights i * (values i * Real.exp (t * values i)))
      (fun i _ => hi i))

/-- Exact first derivative of the tilted first moment, hence second derivative
of the original finite exponential moment. -/
theorem finiteTiltFirst_hasDerivAt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ) (t : ℝ) :
    HasDerivAt (finiteTiltFirst s weights values)
      (finiteTiltSecond s weights values t) t := by
  have hi (i : ι) : HasDerivAt
      (fun τ : ℝ => weights i * (values i * Real.exp (τ * values i)))
      (weights i * (values i ^ 2 * Real.exp (t * values i))) t := by
    have hinner : HasDerivAt (fun τ : ℝ => τ * values i) (values i) t := by
      simpa using (hasDerivAt_id t).mul_const (values i)
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
      ((hinner.exp).const_mul (values i)).const_mul (weights i)
  change HasDerivAt
    (fun τ : ℝ => ∑ i ∈ s, weights i * (values i * Real.exp (τ * values i)))
    (∑ i ∈ s, weights i * (values i ^ 2 * Real.exp (t * values i))) t
  exact (HasDerivAt.fun_sum (u := s)
      (A := fun i τ => weights i * (values i * Real.exp (τ * values i)))
      (A' := fun i => weights i * (values i ^ 2 * Real.exp (t * values i)))
      (fun i _ => hi i))

/-- The derivative at the origin is the first ordinary moment. -/
theorem finiteMGF_deriv_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ) :
    deriv (finiteMGF s weights values) 0 =
      ∑ i ∈ s, weights i * values i := by
  rw [(finiteMGF_hasDerivAt s weights values 0).deriv]
  simp [finiteTiltFirst]

/-- The second tilted moment at zero is the ordinary raw second moment. -/
theorem finiteTiltSecond_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ) :
    finiteTiltSecond s weights values 0 =
      ∑ i ∈ s, weights i * values i ^ 2 := by
  simp [finiteTiltSecond]

end ExactHoeffding
