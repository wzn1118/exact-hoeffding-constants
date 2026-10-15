import ExactHoeffding.Jacobi
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

/-!
# Root counting for the Jacobi Rodrigues construction

The real-rootedness argument here uses the multiplicity-counting Rolle bound
from `Polynomial.card_roots_le_derivative`; it does not assume a Jacobi root
theorem.
-/

namespace ExactHoeffding

/-- A polynomial over `ℝ` that splits remains split after differentiation.

The lower bound comes from Rolle's theorem with multiplicities; the matching
upper bound is the exact degree drop of a derivative. -/
theorem splits_derivative_of_splits {p : Polynomial ℝ} (hp : p.Splits) :
    p.derivative.Splits := by
  rw [Polynomial.splits_iff_card_roots]
  apply le_antisymm
  · exact Polynomial.card_roots' _
  · have hrolle := Polynomial.card_roots_le_derivative p
    have hsplit : p.natDegree = p.roots.card := hp.natDegree_eq_card_roots
    rw [← hsplit] at hrolle
    rw [Polynomial.natDegree_derivative]
    omega

/-- Repeated derivatives of a split real polynomial still split. -/
theorem iterate_derivative_splits {p : Polynomial ℝ} (hp : p.Splits) (n : ℕ) :
    (Polynomial.derivative^[n] p).Splits := by
  induction n with
  | zero => simpa using hp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact splits_derivative_of_splits ih

/-- The polynomial whose `j`th derivative gives the shifted Jacobi Rodrigues
formula with endpoint multiplicities `h` and `r`. -/
noncomputable def jacobiRodriguesBase (j h r : ℕ) : Polynomial ℝ :=
  (Polynomial.X : Polynomial ℝ) ^ (h + j) *
    (Polynomial.X - Polynomial.C 1) ^ (r + j)

/-- The actual `j`th Rodrigues derivative, before removing its endpoint
factors. -/
noncomputable def jacobiRodriguesRaw (j h r : ℕ) : Polynomial ℝ :=
  Polynomial.derivative^[j] (jacobiRodriguesBase j h r)

theorem jacobiRodriguesBase_splits (j h r : ℕ) :
    (jacobiRodriguesBase j h r).Splits := by
  unfold jacobiRodriguesBase
  exact (Polynomial.Splits.X_pow _).mul
    ((Polynomial.Splits.X_sub_C 1).pow _)

/-- The Rodrigues derivative is genuinely real-rooted, by repeated Rolle
counting from its explicit endpoint-rooted base polynomial. -/
theorem jacobiRodriguesRaw_splits (j h r : ℕ) :
    (jacobiRodriguesRaw j h r).Splits := by
  unfold jacobiRodriguesRaw
  exact iterate_derivative_splits (jacobiRodriguesBase_splits j h r) j

theorem jacobiRodriguesRaw_X_pow_dvd (j h r : ℕ) :
    (Polynomial.X : Polynomial ℝ) ^ h ∣ jacobiRodriguesRaw j h r := by
  have hbase :
      (Polynomial.X : Polynomial ℝ) ^ (h + j) ∣ jacobiRodriguesBase j h r := by
    exact dvd_mul_right _ _
  have hderiv := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd
    (p := jacobiRodriguesBase j h r) (q := (Polynomial.X : Polynomial ℝ))
    (n := h + j) j hbase
  have hexp : h + j - j = h := by omega
  simpa [jacobiRodriguesRaw, hexp] using hderiv

theorem jacobiRodriguesRaw_X_sub_one_pow_dvd (j h r : ℕ) :
    (Polynomial.X - Polynomial.C (1 : ℝ)) ^ r ∣ jacobiRodriguesRaw j h r := by
  have hbase :
      (Polynomial.X - Polynomial.C (1 : ℝ)) ^ (r + j) ∣ jacobiRodriguesBase j h r := by
    exact dvd_mul_of_dvd_right dvd_rfl _
  have hderiv := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd
    (p := jacobiRodriguesBase j h r)
    (q := Polynomial.X - Polynomial.C (1 : ℝ)) (n := r + j) j hbase
  have hexp : r + j - j = r := by omega
  simpa [jacobiRodriguesRaw, hexp] using hderiv

/-- The endpoint powers left by the Rodrigues derivative. -/
noncomputable def jacobiRodriguesEndpointFactor (h r : ℕ) : Polynomial ℝ :=
  (Polynomial.X : Polynomial ℝ) ^ h *
    (Polynomial.X - Polynomial.C (1 : ℝ)) ^ r

/-- The degree-`j` Jacobi Rodrigues polynomial after removing its endpoint
factors. -/
noncomputable def jacobiRodrigues (j h r : ℕ) : Polynomial ℝ :=
  jacobiRodriguesRaw j h r /ₘ jacobiRodriguesEndpointFactor h r

theorem jacobiRodriguesEndpointFactor_monic (h r : ℕ) :
    (jacobiRodriguesEndpointFactor h r).Monic := by
  unfold jacobiRodriguesEndpointFactor
  exact (Polynomial.monic_X.pow h).mul
    ((Polynomial.monic_X_sub_C 1).pow r)

theorem jacobiRodrigues_factorization (j h r : ℕ) :
    jacobiRodriguesRaw j h r =
      jacobiRodriguesEndpointFactor h r * jacobiRodrigues j h r := by
  let e := jacobiRodriguesEndpointFactor h r
  let p := jacobiRodriguesRaw j h r
  have hcop0 : IsCoprime (Polynomial.X : Polynomial ℝ)
      (Polynomial.X - Polynomial.C (1 : ℝ)) := by
    have hu : IsUnit ((0 : ℝ) - 1) := by
      apply isUnit_iff_ne_zero.mpr
      simp
    simpa using
      Polynomial.isCoprime_X_sub_C_of_isUnit_sub (a := 0) (b := 1) hu
  have hcop := hcop0.pow (m := h) (n := r)
  have hdiv : e ∣ p := by
    exact hcop.mul_dvd (jacobiRodriguesRaw_X_pow_dvd j h r)
      (jacobiRodriguesRaw_X_sub_one_pow_dvd j h r)
  have heMonic : e.Monic := jacobiRodriguesEndpointFactor_monic h r
  have hmod : p %ₘ e = 0 := (Polynomial.modByMonic_eq_zero_iff_dvd heMonic).2 hdiv
  have heq := Polynomial.modByMonic_add_div p e
  dsimp [p, e, jacobiRodrigues] at hmod heq ⊢
  rw [hmod, zero_add] at heq
  exact heq.symm

theorem jacobiRodrigues_splits (j h r : ℕ) :
    (jacobiRodrigues j h r).Splits := by
  have hraw := jacobiRodriguesRaw_splits j h r
  rw [jacobiRodrigues_factorization] at hraw
  have heMonic := jacobiRodriguesEndpointFactor_monic h r
  have hprod := (Polynomial.splits_mul' (f := jacobiRodriguesEndpointFactor h r)
    (g := jacobiRodrigues j h r)).mp hraw
  exact hprod.2.resolve_right heMonic.ne_zero

end ExactHoeffding
