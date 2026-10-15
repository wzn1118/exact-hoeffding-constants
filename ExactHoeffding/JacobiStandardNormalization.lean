import ExactHoeffding.JacobiRootLocalization
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Standard Jacobi normalization and the canonical hypergeometric PGF

`standardJacobi j α β` uses the standard binomial definition of
`P_j^(α,β)` for nonnegative integral parameters.  The coefficients and the
normalizing factorial are proved to agree with the independent Rodrigues
construction before the root theorems are transferred.
-/

namespace ExactHoeffding

open scoped BigOperators
open Polynomial

/-- The standard Jacobi polynomial `P_j^(α,β)` in its binomial expansion. -/
noncomputable def standardJacobi (j α β : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    C ((Nat.choose (j + α) k : ℝ) * (Nat.choose (j + β) (j - k) : ℝ)) *
      (C (1 / 2 : ℝ) * (X + C 1)) ^ k *
      (C (1 / 2 : ℝ) * (X - C 1)) ^ (j - k)

/-- The coefficient identity furnishing the exact Rodrigues normalization. -/
theorem jacobiRodrigues_coefficient_standard {j h r k : ℕ} (hk : k ≤ j) :
    Nat.choose j k * Nat.descFactorial (h + j) (j - k) *
        Nat.descFactorial (r + j) k =
      Nat.factorial j * Nat.choose (j + r) k * Nat.choose (j + h) (j - k) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  calc
    j.choose k * ((j - k).factorial * (h + j).choose (j - k)) *
        (k.factorial * (r + j).choose k) =
      (j.choose k * k.factorial * (j - k).factorial) *
        (j + r).choose k * (j + h).choose (j - k) := by
      simp only [Nat.add_comm h j, Nat.add_comm r j]
      ring
    _ = _ := by rw [Nat.choose_mul_factorial_mul_factorial hk]

/-- The shift from `[-1,1]` to `[0,1]` has the normalization `j!`. -/
theorem jacobiRodrigues_eq_factorial_standard_comp (j h r : ℕ) :
    jacobiRodrigues j h r =
      C (Nat.factorial j : ℝ) *
        (standardJacobi j r h).comp (C 2 * X - C 1) := by
  classical
  rw [jacobiRodrigues_eq_expansion]
  unfold jacobiRodriguesExpansion standardJacobi
  rw [Polynomial.sum_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≤ j := by
    simp only [Finset.mem_range] at hk
    omega
  have hcoef := jacobiRodrigues_coefficient_standard (h := h) (r := r) hkj
  have hcoefR :
      (j.choose k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
          (Nat.descFactorial (r + j) k : ℝ) =
        (Nat.factorial j : ℝ) * (Nat.choose (j + r) k : ℝ) *
          (Nat.choose (j + h) (j - k) : ℝ) := by
    exact_mod_cast hcoef
  have hp : (C (1 / 2 : ℝ) * (X + C 1) : Polynomial ℝ).comp
      (C 2 * X - C 1) = X := by
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hm : (C (1 / 2 : ℝ) * (X - C 1) : Polynomial ℝ).comp
      (C 2 * X - C 1) = X - C 1 := by
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.pow_comp, Polynomial.pow_comp, hp, hm, hcoefR]
  simp only [map_mul]
  ring

/-- The denominator-cleared Jacobi substitution, meaningful also at `z = 1`. -/
noncomputable def standardJacobiMobiusCleared (j α β : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    C ((Nat.choose (j + α) (j - i) : ℝ) * (Nat.choose (j + β) i : ℝ)) * X ^ i

/-- The exact coefficient comparison, with the manuscript's parameters `(r,h)`. -/
theorem jacobiPGF_eq_factorial_standard_cleared (j h r : ℕ) :
    jacobiPGF j h r =
      C (Nat.factorial j : ℝ) * standardJacobiMobiusCleared j r h := by
  classical
  unfold jacobiPGF standardJacobiMobiusCleared
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := by
    simp only [Finset.mem_range] at hi
    omega
  have hcoef := jacobiRodrigues_coefficient_standard
    (j := j) (h := h) (r := r) (k := j - i) (by omega)
  have hsub : j - (j - i) = i := Nat.sub_sub_self hij
  rw [hsub, Nat.choose_symm hij, Nat.add_comm h j] at hcoef
  have hcoefR : (jacobiCoeff j h r i : ℝ) =
      (Nat.factorial j : ℝ) * (Nat.choose (j + r) (j - i) : ℝ) *
        (Nat.choose (j + h) i : ℝ) := by
    unfold jacobiCoeff
    exact_mod_cast hcoef
  rw [← Polynomial.C_mul_X_pow_eq_monomial, hcoefR]
  simp only [map_mul]
  ring

/-- The manuscript's rational Jacobi representation, away from its removable
singularity at `z = 1`.  The preceding polynomial identity gives its value
at every `z`, including `z = 1`. -/
theorem jacobiPGF_eval_eq_standardJacobi (j h r : ℕ) {z : ℝ} (hz : z ≠ 1) :
    (jacobiPGF j h r).eval z =
      (Nat.factorial j : ℝ) * (1 - z) ^ j *
        (standardJacobi j r h).eval ((1 + z) / (1 - z)) := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  let : Invertible ((1 - z)⁻¹) := invertibleOfNonzero (inv_ne_zero hd)
  have hrev := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℝ) ((1 - z)⁻¹)
    (jacobiRodrigues j h r)
  have hrev' : (jacobiRodrigues j h r).reverse.eval (1 - z) *
      ((1 - z)⁻¹) ^ j = (jacobiRodrigues j h r).eval ((1 - z)⁻¹) := by
    simpa [invOf_eq_inv, jacobiRodrigues_natDegree] using hrev
  have hcancel : ((1 - z)⁻¹) ^ j * (1 - z) ^ j = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hd, one_pow]
  have harg : 2 * ((1 - z)⁻¹) - 1 = (1 + z) / (1 - z) := by
    field_simp
    ring
  calc
    (jacobiPGF j h r).eval z =
        (jacobiRodrigues j h r).reverse.eval (1 - z) := by
      rw [jacobiPGF_eq_rodrigues_mobius, Polynomial.eval_comp]
      simp
    _ = ((jacobiRodrigues j h r).reverse.eval (1 - z) *
        ((1 - z)⁻¹) ^ j) * (1 - z) ^ j := by
      rw [mul_assoc, hcancel, mul_one]
    _ = (jacobiRodrigues j h r).eval ((1 - z)⁻¹) * (1 - z) ^ j := by
      rw [hrev']
    _ = _ := by
      rw [jacobiRodrigues_eq_factorial_standard_comp]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        Polynomial.eval_sub, Polynomial.eval_X, harg]
      ring

/-- The literal hypergeometric generating function has the same standard
Jacobi representation and the explicitly proved scaling constant. -/
theorem hypergeomPolynomial_eq_standardJacobi (j h r : ℕ) {z : ℝ} (hz : z ≠ 1) :
    jacobiHypergeomScale j h r *
        hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) z =
      (Nat.factorial j : ℝ) * (1 - z) ^ j *
        (standardJacobi j r h).eval ((1 + z) / (1 - z)) := by
  rw [← jacobiPGF_eval_eq_scaled_hypergeomPolynomial]
  exact jacobiPGF_eval_eq_standardJacobi j h r hz

private theorem reverse_X_sub_C_eq (y : ℝ) :
    (X - C y : Polynomial ℝ).reverse = 1 - C y * X := by
  rw [Polynomial.reverse, Polynomial.natDegree_X_sub_C, Polynomial.reflect_sub,
    Polynomial.reflect_one_X, Polynomial.reflect_C]
  simp only [pow_one]

private theorem reverse_linear_mobius (y : ℝ) (hy : y ≠ 0) :
    (X - C y : Polynomial ℝ).reverse.comp (C 1 - X) =
      C y * (X - C (1 - y⁻¹)) := by
  rw [reverse_X_sub_C_eq]
  apply Polynomial.funext
  intro z
  simp only [Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one]
  field_simp
  ring

/-- The endpoint-removed Rodrigues polynomial is nonzero, including degree zero. -/
theorem jacobiRodrigues_ne_zero (j h r : ℕ) : jacobiRodrigues j h r ≠ 0 := by
  intro hp
  apply jacobiRodrigues_eval_zero_ne j h r
  simp [hp]

/-- Every Rodrigues root is simple.  A repeated root would give a repeated
canonical PGF root under the exact reciprocal Mobius substitution. -/
theorem jacobiRodrigues_roots_nodup (j h r : ℕ) :
    (jacobiRodrigues j h r).roots.Nodup := by
  classical
  apply Multiset.nodup_iff_count_le_one.mpr
  intro y
  by_cases hy : y ∈ (jacobiRodrigues j h r).roots
  · rw [Polynomial.count_roots]
    by_contra hm
    have hm' : 2 ≤ (jacobiRodrigues j h r).rootMultiplicity y := by omega
    have hyne : y ≠ 0 := ne_of_gt (jacobiRodrigues_root_mem_Ioo j h r hy).1
    have hdiv : (X - C y : Polynomial ℝ) ^ 2 ∣ jacobiRodrigues j h r :=
      (Polynomial.le_rootMultiplicity_iff (jacobiRodrigues_ne_zero j h r)).mp hm'
    obtain ⟨g, hg⟩ := hdiv
    have hpgf : jacobiPGF j h r =
        (C y * (X - C (1 - y⁻¹))) ^ 2 * g.reverse.comp (C 1 - X) := by
      rw [jacobiPGF_eq_rodrigues_mobius, hg, pow_two,
        Polynomial.reverse_mul_of_domain, Polynomial.reverse_mul_of_domain,
        Polynomial.mul_comp, Polynomial.mul_comp, reverse_linear_mobius y hyne]
      ring
    have hdivQ : (X - C (1 - y⁻¹) : Polynomial ℝ) ^ 2 ∣ jacobiPGF j h r := by
      rw [hpgf]
      refine ⟨C y ^ 2 * g.reverse.comp (C 1 - X), ?_⟩
      ring
    have hmultQ : 1 < (jacobiPGF j h r).rootMultiplicity (1 - y⁻¹) := by
      have hh := (Polynomial.le_rootMultiplicity_iff (jacobiPGF_ne_zero j h r)).mpr hdivQ
      omega
    have hQroot : 1 - y⁻¹ ∈ (jacobiPGF j h r).roots :=
      (Polynomial.mem_roots (jacobiPGF_ne_zero j h r)).2
        (jacobiRodrigues_root_transform j h r hy)
    have hdQ := (Polynomial.one_lt_rootMultiplicity_iff_isRoot
      (jacobiPGF_ne_zero j h r)).mp hmultQ |>.2
    exact jacobiPGF_root_derivative_ne_zero j h r hQroot
      (by simpa [Polynomial.IsRoot] using hdQ)
  · simp [Multiset.count_eq_zero.mpr hy]

private theorem standardJacobi_affine_natDegree :
    (C 2 * X - C 1 : Polynomial ℝ).natDegree = 1 := by
  rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_C_mul (by norm_num : (2 : ℝ) ≠ 0),
    Polynomial.natDegree_X]

/-- The named standard Jacobi polynomial has its asserted degree. -/
theorem standardJacobi_natDegree (j α β : ℕ) :
    (standardJacobi j α β).natDegree = j := by
  have hh := congrArg Polynomial.natDegree
    (jacobiRodrigues_eq_factorial_standard_comp j β α)
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  rw [Polynomial.natDegree_C_mul hf, Polynomial.natDegree_comp,
    standardJacobi_affine_natDegree, mul_one, jacobiRodrigues_natDegree] at hh
  exact hh.symm

/-- Standard Jacobi polynomials are nonzero for all natural endpoint parameters. -/
theorem standardJacobi_ne_zero (j α β : ℕ) : standardJacobi j α β ≠ 0 := by
  intro hh
  have hq := jacobiRodrigues_eq_factorial_standard_comp j β α
  rw [hh, Polynomial.zero_comp, mul_zero] at hq
  exact jacobiRodrigues_ne_zero j β α hq

/-- The standard polynomial splits over the reals, proved through Rodrigues and
not supplied as a root-theorem hypothesis. -/
theorem standardJacobi_splits (j α β : ℕ) :
    (standardJacobi j α β).Splits := by
  have hh := jacobiRodrigues_splits j β α
  rw [jacobiRodrigues_eq_factorial_standard_comp] at hh
  have hc : (standardJacobi j α β).comp (C 2 * X - C 1) |>.Splits := by
    exact hh.of_dvd (by
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr
        (by exact_mod_cast Nat.factorial_ne_zero j))
        (by
          intro hzero
          have hq := jacobiRodrigues_eq_factorial_standard_comp j β α
          rw [hzero, mul_zero] at hq
          exact jacobiRodrigues_ne_zero j β α hq)) (dvd_mul_left _ _)
  exact (Polynomial.splits_iff_comp_splits_of_natDegree_eq_one
    standardJacobi_affine_natDegree).mpr hc

/-- The standard polynomial has exactly `j` real roots, counted with multiplicity. -/
theorem standardJacobi_roots_card (j α β : ℕ) :
    (standardJacobi j α β).roots.card = j := by
  rw [← (standardJacobi_splits j α β).natDegree_eq_card_roots,
    standardJacobi_natDegree]

/-- The standard polynomial's roots are simple. -/
theorem standardJacobi_roots_nodup (j α β : ℕ) :
    (standardJacobi j α β).roots.Nodup := by
  have hh := jacobiRodrigues_roots_nodup j β α
  rw [jacobiRodrigues_eq_factorial_standard_comp,
    Polynomial.roots_C_mul _ (by exact_mod_cast Nat.factorial_ne_zero j)] at hh
  have hmap := Polynomial.map_roots_comp_C_mul_X_add_C
    (standardJacobi j α β) (2 : ℝ) (-1 : ℝ) (isUnit_iff_ne_zero.mpr (by norm_num))
  have heq : C 2 * X + C (-1 : ℝ) = (C 2 * X - C 1 : Polynomial ℝ) := by
    simp only [Polynomial.C_neg, Polynomial.C_1]
    ring
  rw [heq] at hmap
  rw [← hmap]
  apply hh.map
  intro x y hxy
  linarith

/-- Every root of `P_j^(α,β)` lies strictly in the standard Jacobi interval. -/
theorem standardJacobi_roots_mem_Ioo (j α β : ℕ) {x : ℝ}
    (hx : x ∈ (standardJacobi j α β).roots) : x ∈ Set.Ioo (-1) 1 := by
  have hzero : (standardJacobi j α β).eval x = 0 := Polynomial.isRoot_of_mem_roots hx
  have hshift : (jacobiRodrigues j β α).eval ((x + 1) / 2) = 0 := by
    rw [jacobiRodrigues_eq_factorial_standard_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
      Polynomial.eval_sub, Polynomial.eval_X]
    have ha : 2 * ((x + 1) / 2) - 1 = x := by ring
    rw [ha, hzero, mul_zero]
  have hy : (x + 1) / 2 ∈ (jacobiRodrigues j β α).roots :=
    (Polynomial.mem_roots (jacobiRodrigues_ne_zero j β α)).mpr hshift
  have hI := jacobiRodrigues_root_mem_Ioo j β α hy
  constructor <;> linarith [hI.1, hI.2]

/-- End-to-end standard Jacobi root theorem for the manuscript's parameters. -/
theorem standardJacobi_exact_roots (j h r : ℕ) :
    (standardJacobi j r h).roots.card = j ∧
      (standardJacobi j r h).roots.Nodup ∧
      ∀ x ∈ (standardJacobi j r h).roots, x ∈ Set.Ioo (-1) 1 := by
  exact ⟨standardJacobi_roots_card j r h, standardJacobi_roots_nodup j r h,
    fun x hx => standardJacobi_roots_mem_Ioo j r h hx⟩

/-- The Rodrigues differential identity, including its exact factorial constant
and endpoint weight, in the shifted coordinate. -/
theorem standardJacobi_shifted_rodrigues_identity (j h r : ℕ) :
    Polynomial.derivative^[j]
        (X ^ (h + j) * (X - C 1) ^ (r + j) : Polynomial ℝ) =
      (X ^ h * (X - C 1) ^ r) *
        (C (Nat.factorial j : ℝ) *
          (standardJacobi j r h).comp (C 2 * X - C 1)) := by
  change jacobiRodriguesRaw j h r =
    jacobiRodriguesEndpointFactor h r * _
  rw [jacobiRodrigues_factorization, jacobiRodrigues_eq_factorial_standard_comp]

/-- A simple root is equivalently detected by a nonzero first derivative. -/
theorem standardJacobi_root_derivative_ne_zero (j α β : ℕ) {x : ℝ}
    (hx : x ∈ (standardJacobi j α β).roots) :
    (standardJacobi j α β).derivative.eval x ≠ 0 := by
  classical
  intro hd
  have hmult : 1 < (standardJacobi j α β).rootMultiplicity x :=
    (Polynomial.one_lt_rootMultiplicity_iff_isRoot
      (standardJacobi_ne_zero j α β)).mpr
        ⟨Polynomial.isRoot_of_mem_roots hx, hd⟩
  have hcount : (standardJacobi j α β).roots.count x ≤ 1 :=
    Multiset.nodup_iff_count_le_one.mp (standardJacobi_roots_nodup j α β) x
  rw [Polynomial.count_roots] at hcount
  omega

/-- The root map in the manuscript: `x` maps to `-(1-x)/(1+x)`. -/
theorem standardJacobi_root_maps_to_canonical (j h r : ℕ) {x : ℝ}
    (hx : x ∈ (standardJacobi j r h).roots) :
    -(1 - x) / (1 + x) ∈ (jacobiPGF j h r).roots := by
  have hI := standardJacobi_roots_mem_Ioo j r h hx
  have hx1 : 1 + x ≠ 0 := ne_of_gt (by linarith [hI.1] : 0 < 1 + x)
  have hz : -(1 - x) / (1 + x) ≠ 1 := by
    intro hh
    have hm := (div_eq_iff hx1).mp hh
    linarith
  have harg : (1 + (-(1 - x) / (1 + x))) /
      (1 - (-(1 - x) / (1 + x))) = x := by
    field_simp
    ring
  apply (Polynomial.mem_roots (jacobiPGF_ne_zero j h r)).mpr
  change (jacobiPGF j h r).eval (-(1 - x) / (1 + x)) = 0
  rw [jacobiPGF_eval_eq_standardJacobi j h r hz, harg,
    Polynomial.isRoot_of_mem_roots hx, mul_zero]

/-- The Jacobi denominator-cleared polynomial is the rational composition away
from `z=1`, while its polynomial definition supplies the value at `z=1`. -/
theorem standardJacobi_cleared_eval (j α β : ℕ) {z : ℝ} (hz : z ≠ 1) :
    (standardJacobiMobiusCleared j α β).eval z =
      (1 - z) ^ j * (standardJacobi j α β).eval ((1 + z) / (1 - z)) := by
  have hh := jacobiPGF_eval_eq_standardJacobi j β α hz
  rw [jacobiPGF_eq_factorial_standard_cleared, Polynomial.eval_mul,
    Polynomial.eval_C] at hh
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  apply mul_left_cancel₀ hf
  simpa only [mul_assoc] using hh

/-- The standard and canonical roots correspond in both directions under the
manuscript's fractional linear change of variable. -/
theorem jacobiPGF_root_iff_standardJacobi (j h r : ℕ) {z : ℝ} (hz : z ≠ 1) :
    z ∈ (jacobiPGF j h r).roots ↔
      (1 + z) / (1 - z) ∈ (standardJacobi j r h).roots := by
  rw [Polynomial.mem_roots (jacobiPGF_ne_zero j h r),
    Polynomial.mem_roots (standardJacobi_ne_zero j r h)]
  change (jacobiPGF j h r).eval z = 0 ↔
    (standardJacobi j r h).eval ((1 + z) / (1 - z)) = 0
  rw [jacobiPGF_eval_eq_standardJacobi j h r hz]
  have hf : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  exact mul_eq_zero.trans (by simp [hf, hd])

/-- The normalization, polynomial identity, and simple-root theorem for the
integer parameters actually used by the finite-population model. -/
theorem standardJacobi_hypergeom_end_to_end (j h r : ℕ) :
    jacobiPGF j h r =
        C (Nat.factorial j : ℝ) * standardJacobiMobiusCleared j r h ∧
      (standardJacobi j r h).natDegree = j ∧
      (standardJacobi j r h).roots.card = j ∧
      (standardJacobi j r h).roots.Nodup ∧
      (∀ x ∈ (standardJacobi j r h).roots, x ∈ Set.Ioo (-1) 1) ∧
      (∀ z : ℝ, z ≠ 1 →
        (jacobiPGF j h r).eval z =
          (Nat.factorial j : ℝ) * (1 - z) ^ j *
            (standardJacobi j r h).eval ((1 + z) / (1 - z))) := by
  exact ⟨jacobiPGF_eq_factorial_standard_cleared j h r,
    standardJacobi_natDegree j r h, standardJacobi_roots_card j r h,
    standardJacobi_roots_nodup j r h,
    fun x hx => standardJacobi_roots_mem_Ioo j r h hx,
    fun z hz => jacobiPGF_eval_eq_standardJacobi j h r hz⟩

/-- The usual Rodrigues identity on the standard `[-1,1]` coordinate, with the
exact factor `2^j j!` and the parameters ordered as in the manuscript. -/
theorem standardJacobi_rodrigues_identity (j h r : ℕ) :
    Polynomial.derivative^[j]
        ((X + C 1) ^ (h + j) * (X - C 1) ^ (r + j) : Polynomial ℝ) =
      C ((2 : ℝ) ^ j * Nat.factorial j) *
        ((X + C 1) ^ h * (X - C 1) ^ r) * standardJacobi j r h := by
  classical
  unfold standardJacobi
  rw [Polynomial.iterate_derivative_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≤ j := by
    simp only [Finset.mem_range] at hk
    omega
  have hexp₁ : h + j - (j - k) = h + k := by omega
  have hexp₂ : r + j - k = r + (j - k) := by omega
  have hcoef := jacobiRodrigues_coefficient_standard (h := h) (r := r) hkj
  have hcoefR :
      (j.choose k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
          (Nat.descFactorial (r + j) k : ℝ) =
        (Nat.factorial j : ℝ) * (Nat.choose (j + r) k : ℝ) *
          (Nat.choose (j + h) (j - k) : ℝ) := by exact_mod_cast hcoef
  rw [Polynomial.iterate_derivative_X_add_pow,
    Polynomial.iterate_derivative_X_sub_pow]
  simp only [nsmul_eq_mul, ← Polynomial.C_eq_natCast,
    hexp₁, hexp₂, pow_add, mul_pow]
  have hhalves : (C (2 : ℝ) : Polynomial ℝ) ^ j * C (1 / 2 : ℝ) ^ k *
      C (1 / 2 : ℝ) ^ (j - k) = 1 := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hkj, ← mul_pow, ← Polynomial.C_mul]
    norm_num
  have hcoefP := congrArg (fun a : ℝ => (C a : Polynomial ℝ)) hcoefR
  simp only [map_mul] at hcoefP
  simp only [Polynomial.C_mul, Polynomial.C_pow]
  calc
    _ = (C (j.choose k : ℝ) * C (Nat.descFactorial (h + j) (j - k) : ℝ) *
          C (Nat.descFactorial (r + j) k : ℝ)) *
        ((X + C 1) ^ h * (X - C 1) ^ r *
          (X + C 1) ^ k * (X - C 1) ^ (j - k)) := by ring
    _ = (C (Nat.factorial j : ℝ) * C (Nat.choose (j + r) k : ℝ) *
          C (Nat.choose (j + h) (j - k) : ℝ)) *
        ((X + C 1) ^ h * (X - C 1) ^ r *
          (X + C 1) ^ k * (X - C 1) ^ (j - k)) := by rw [hcoefP]
    _ = ((C (2 : ℝ)) ^ j * C (1 / 2 : ℝ) ^ k * C (1 / 2 : ℝ) ^ (j - k)) *
        ((C (Nat.factorial j : ℝ) * C (Nat.choose (j + r) k : ℝ) *
          C (Nat.choose (j + h) (j - k) : ℝ)) *
          ((X + C 1) ^ h * (X - C 1) ^ r *
            (X + C 1) ^ k * (X - C 1) ^ (j - k))) := by rw [hhalves, one_mul]
    _ = _ := by ring

/-- The endpoint normalization fixes the conventional Jacobi scale. -/
theorem standardJacobi_eval_one (j α β : ℕ) :
    (standardJacobi j α β).eval 1 = (Nat.choose (j + α) j : ℝ) := by
  classical
  unfold standardJacobi
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_X]
  norm_num
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    have hlt : k < j := by
      simp only [Finset.mem_range] at hk
      omega
    simp [Nat.ne_of_gt (Nat.sub_pos_of_lt hlt)]
  · simp

/-- The root parameter in the PGF's linear factors is strictly positive. -/
theorem standardJacobi_root_alpha_pos (j h r : ℕ) {x : ℝ}
    (hx : x ∈ (standardJacobi j r h).roots) : 0 < (1 - x) / (1 + x) := by
  have hI := standardJacobi_roots_mem_Ioo j r h hx
  exact div_pos (by linarith [hI.2]) (by linarith [hI.1])

end ExactHoeffding
