import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# The normalized Jacobi/hypergeometric coefficient polynomial

This file records the paper's normalization
`k = j`, `m = j + h`, `N = 2 * j + h + r` and constructs the associated
real polynomial from its positive integer coefficients.  The coefficient
formula is written with descending factorials, so no unproved factorial
division or root factorization is hidden in the definition.

The Jacobi root theorem and the resulting Poisson-binomial factorization are
not asserted here; they are proved in the later factorization module.
-/

namespace ExactHoeffding

/-! ## The paper's normalized parameters -/

def jacobiK (j : ℕ) : ℕ := j

def jacobiM (j h : ℕ) : ℕ := j + h

def jacobiN (j h r : ℕ) : ℕ := 2 * j + h + r

theorem jacobi_m_le_N (j h r : ℕ) :
    jacobiM j h ≤ jacobiN j h r := by
  simp [jacobiM, jacobiN]
  omega

theorem jacobi_k_le_N (j h r : ℕ) :
    jacobiK j ≤ jacobiN j h r := by
  simp [jacobiK, jacobiN]
  omega

theorem jacobi_k_le_N_sub_m (j h r : ℕ) :
    jacobiK j ≤ jacobiN j h r - jacobiM j h := by
  simp [jacobiK, jacobiM, jacobiN]
  omega

theorem jacobi_normalization (j h r : ℕ) :
    jacobiN j h r = jacobiK j + jacobiM j h + r := by
  simp [jacobiK, jacobiM, jacobiN]
  ring

/-! ## Integer coefficients and the real coefficient polynomial -/

/-- The integer coefficient used in the paper's `Q_j` polynomial.

The last descending factorial is the division-free form of
`(r + j)! / (r + i)!`.
-/
def jacobiCoeff (j h r i : ℕ) : ℕ :=
  Nat.choose j i * Nat.descFactorial (j + h) i *
    Nat.descFactorial (r + j) (j - i)

/-- The real polynomial associated with the normalized hypergeometric PGF. -/
noncomputable def jacobiPGF (j h r : ℕ) : Polynomial ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    Polynomial.monomial i (jacobiCoeff j h r i : ℝ)

theorem jacobiCoeff_factorial_form {j h r i : ℕ} (hi : i ≤ j) :
    jacobiCoeff j h r i =
      Nat.choose j i * Nat.descFactorial (j + h) i *
        (Nat.factorial (r + j) / Nat.factorial (r + i)) := by
  unfold jacobiCoeff
  have hji : j - i ≤ r + j := by omega
  have hsub : r + j - (j - i) = r + i := by omega
  rw [Nat.descFactorial_eq_div hji, hsub]

theorem jacobiCoeff_pos {j h r i : ℕ} (hi : i ≤ j) :
    0 < jacobiCoeff j h r i := by
  unfold jacobiCoeff
  have hijh : i ≤ j + h := by omega
  have hji : j - i ≤ r + j := by omega
  exact Nat.mul_pos
    (Nat.mul_pos (Nat.choose_pos hi) (Nat.descFactorial_pos.mpr hijh))
    (Nat.descFactorial_pos.mpr hji)

theorem jacobiPGF_coeff (j h r n : ℕ) :
    (jacobiPGF j h r).coeff n =
      if n ≤ j then (jacobiCoeff j h r n : ℝ) else 0 := by
  classical
  by_cases hn : n ≤ j
  · have hmem : n ∈ Finset.range (j + 1) := by
      simp only [Finset.mem_range]
      omega
    simp [jacobiPGF, Polynomial.coeff_monomial,
      Finset.sum_ite_eq', hmem, hn]
  · have hmem : n ∉ Finset.range (j + 1) := by
      simp only [Finset.mem_range]
      omega
    simp [jacobiPGF, Polynomial.coeff_monomial,
      Finset.sum_ite_eq', hmem, hn]

theorem jacobiPGF_coeff_zero (j h r : ℕ) :
    (jacobiPGF j h r).coeff 0 =
      (Nat.descFactorial (r + j) j : ℝ) := by
  rw [jacobiPGF_coeff]
  simp [jacobiCoeff]

theorem jacobiPGF_coeff_degree (j h r : ℕ) :
    (jacobiPGF j h r).coeff j =
      (Nat.descFactorial (j + h) j : ℝ) := by
  rw [jacobiPGF_coeff]
  simp [jacobiCoeff]

theorem jacobiPGF_coeff_pos {j h r i : ℕ} (hi : i ≤ j) :
    0 < (jacobiPGF j h r).coeff i := by
  rw [jacobiPGF_coeff, if_pos hi]
  exact_mod_cast jacobiCoeff_pos hi

theorem jacobiPGF_support_subset (j h r : ℕ) :
    (jacobiPGF j h r).support ⊆ Finset.range (j + 1) := by
  intro n hn
  by_contra hnot
  have hcoeff : (jacobiPGF j h r).coeff n = 0 := by
    rw [jacobiPGF_coeff]
    have hnle : ¬n ≤ j := by
      simp only [Finset.mem_range] at hnot
      omega
    simp [hnle]
  exact (Polynomial.mem_support_iff.mp hn) hcoeff

theorem jacobiPGF_ne_zero (j h r : ℕ) :
    jacobiPGF j h r ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff 0) hzero
  rw [jacobiPGF_coeff_zero] at hcoeff
  have hpos : 0 < Nat.descFactorial (r + j) j := by
    exact Nat.descFactorial_pos.mpr (by omega)
  exact (ne_of_gt (show (0 : ℝ) < (Nat.descFactorial (r + j) j : ℝ) by
    exact_mod_cast hpos)) hcoeff

/-! ## The coefficient recurrence behind the hypergeometric equation -/

theorem jacobiCoeff_recurrence {j h r i : ℕ} (hi : i < j) :
    jacobiCoeff j h r (i + 1) * (i + 1) * (r + i + 1) =
      jacobiCoeff j h r i * (j - i) * (j + h - i) := by
  have hdesc :
      (r + i + 1) * Nat.descFactorial (r + j) (j - (i + 1)) =
        Nat.descFactorial (r + j) (j - i) := by
    rw [show j - i = (j - (i + 1)) + 1 by omega,
      Nat.descFactorial_succ]
    congr 1
    omega
  unfold jacobiCoeff
  calc
    (Nat.choose j (i + 1) * Nat.descFactorial (j + h) (i + 1) *
        Nat.descFactorial (r + j) (j - (i + 1))) * (i + 1) *
        (r + i + 1) =
      (Nat.choose j (i + 1) * (i + 1)) *
        ((j + h - i) * Nat.descFactorial (j + h) i) *
        ((r + i + 1) * Nat.descFactorial (r + j) (j - (i + 1))) := by
          rw [Nat.descFactorial_succ]
          ring
    _ = (Nat.choose j i * (j - i)) *
        ((j + h - i) * Nat.descFactorial (j + h) i) *
        Nat.descFactorial (r + j) (j - i) := by
          rw [Nat.choose_succ_right_eq, hdesc]
    _ = (Nat.choose j i * Nat.descFactorial (j + h) i *
        Nat.descFactorial (r + j) (j - i)) * (j - i) * (j + h - i) := by
          ring

end ExactHoeffding
