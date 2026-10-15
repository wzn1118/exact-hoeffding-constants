import ExactHoeffding.JacobiSimpleRoots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ExactHoeffding

open scoped BigOperators

/-- The endpoint-removed Rodrigues polynomial does not vanish at the left endpoint.

This is the constant term of its Leibniz expansion.  It is the nonvanishing input
needed to invert the reciprocal-root map. -/
theorem jacobiRodrigues_eval_zero_ne (j h r : ℕ) :
    (jacobiRodrigues j h r).eval 0 ≠ 0 := by
  rw [jacobiRodrigues_eq_expansion]
  unfold jacobiRodriguesExpansion
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  have hsum := Finset.sum_eq_single (s := Finset.range (j + 1))
    (f := fun x : ℕ =>
      (j.choose x : ℝ) * (Nat.descFactorial (h + j) (j - x) : ℝ) *
        (Nat.descFactorial (r + j) x : ℝ) * 0 ^ x *
        Polynomial.eval 0 (Polynomial.X - Polynomial.C 1) ^ (j - x)) 0
    (fun x hx hne => by
      have hxpos : 0 < x := by omega
      simp [Nat.ne_of_gt hxpos])
    (by simp)
  rw [hsum]
  simp [Polynomial.eval_sub]

/-- A zero of the Rodrigues polynomial maps to a zero of the canonical PGF under
`y ↦ 1 - y⁻¹`. -/
theorem jacobiRodrigues_root_transform (j h r : ℕ) {y : ℝ}
    (hy : y ∈ (jacobiRodrigues j h r).roots) :
    (jacobiPGF j h r).eval (1 - y⁻¹) = 0 := by
  have hq0 : (jacobiRodrigues j h r).eval 0 ≠ 0 :=
    jacobiRodrigues_eval_zero_ne j h r
  have hyroot : (jacobiRodrigues j h r).eval y = 0 :=
    Polynomial.isRoot_of_mem_roots hy
  have hyne : y ≠ 0 := by
    intro hy0
    apply hq0
    simpa [hy0] using hyroot
  letI : Invertible y := invertibleOfNonzero hyne
  have hrev : (jacobiRodrigues j h r).reverse.eval y⁻¹ = 0 := by
    have hh := (Polynomial.eval₂_reverse_eq_zero_iff (RingHom.id ℝ) y
      (jacobiRodrigues j h r)).2 hyroot
    simpa [invOf_eq_inv] using hh
  rw [jacobiPGF_eq_rodrigues_mobius]
  rw [Polynomial.eval_comp]
  simpa [Polynomial.eval_sub, invOf_eq_inv] using hrev

/-- Every real zero of the normalized Rodrigues polynomial lies strictly between
its two endpoint roots.  The proof uses the canonical PGF's positive
coefficients and the exact reciprocal Mobius bridge. -/
theorem jacobiRodrigues_root_mem_Ioo (j h r : ℕ) {y : ℝ}
    (hy : y ∈ (jacobiRodrigues j h r).roots) :
    y ∈ Set.Ioo 0 1 := by
  have hq0 : (jacobiRodrigues j h r).eval 0 ≠ 0 :=
    jacobiRodrigues_eval_zero_ne j h r
  have hyroot : (jacobiRodrigues j h r).eval y = 0 :=
    Polynomial.isRoot_of_mem_roots hy
  have hyne : y ≠ 0 := by
    intro hy0
    apply hq0
    simpa [hy0] using hyroot
  have hpgf0 : (jacobiPGF j h r).eval (1 - y⁻¹) = 0 :=
    jacobiRodrigues_root_transform j h r hy
  have hpgfroot : 1 - y⁻¹ ∈ (jacobiPGF j h r).roots :=
    (Polynomial.mem_roots (jacobiPGF_ne_zero j h r)).2 hpgf0
  have hneg : 1 - y⁻¹ < 0 :=
    jacobiPGF_roots_negative j h r hpgfroot
  have hypos : 0 < y := by
    rcases lt_or_gt_of_ne hyne with hyneg | hypos
    · have hinvneg : y⁻¹ < 0 :=
        lt_of_le_of_ne (inv_nonpos.mpr hyneg.le) (inv_ne_zero hyne)
      linarith
    · exact hypos
  constructor
  · exact hypos
  · exact (one_lt_inv₀ hypos).mp (sub_neg.mp hneg)

/-- After the usual affine change of variables, the same roots belong to the
standard Jacobi interval `(-1,1)`. -/
theorem jacobiRodrigues_root_affine_mem_Ioo (j h r : ℕ) {y : ℝ}
    (hy : y ∈ (jacobiRodrigues j h r).roots) :
    2 * y - 1 ∈ Set.Ioo (-1) 1 := by
  have hyIoo : y ∈ Set.Ioo 0 1 := jacobiRodrigues_root_mem_Ioo j h r hy
  constructor <;> linarith [hyIoo.1, hyIoo.2]

#print axioms jacobiRodrigues_eval_zero_ne
#print axioms jacobiRodrigues_root_transform
#print axioms jacobiRodrigues_root_mem_Ioo

end ExactHoeffding
