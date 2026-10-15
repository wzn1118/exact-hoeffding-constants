import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.Basic
import ExactHoeffding.Hypergeometric
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

/-! ## Connection with the existing hypergeometric polynomial -/

/-- The coefficient-independent scale relating the Jacobi normalization to
the unnormalized hypergeometric counts. -/
noncomputable def jacobiHypergeomScale (j h r : ℕ) : ℝ :=
  ((Nat.factorial (j + h) : ℝ) * (Nat.factorial (r + j) : ℝ)) /
    (Nat.factorial (j + h + r) : ℝ)

theorem jacobiCoeff_scaled_hypergeomCount_of_le {j h r i : ℕ} (hi : i ≤ j) :
    (jacobiCoeff j h r i : ℝ) =
      jacobiHypergeomScale j h r *
        (hypergeomCount (jacobiN j h r) (jacobiK j) (jacobiM j h) i : ℝ) := by
  have hji : j - i ≤ r + j := by omega
  have hji' : r + j - (j - i) = r + i := by omega
  have hijh : i ≤ j + h := by omega
  have hchoose : j + h - i ≤ j + h + r := by omega
  have hchoose' : j + h + r - (j + h - i) = r + i := by omega
  have hdesc₁ := Nat.factorial_mul_descFactorial hijh
  have hdesc₂ := Nat.factorial_mul_descFactorial hji
  have hchoose₁ := Nat.choose_mul_factorial_mul_factorial hchoose
  have hdesc₁r :
      (Nat.factorial (j + h - i) : ℝ) *
          (Nat.descFactorial (j + h) i : ℝ) =
        (Nat.factorial (j + h) : ℝ) := by
    exact_mod_cast hdesc₁
  have hdesc₂r :
      (Nat.factorial (r + i) : ℝ) *
          (Nat.descFactorial (r + j) (j - i) : ℝ) =
        (Nat.factorial (r + j) : ℝ) := by
    rw [← hji']
    exact_mod_cast hdesc₂
  have hchooser :
      (Nat.choose (j + h + r) (j + h - i) : ℝ) *
          (Nat.factorial (j + h - i) : ℝ) *
          (Nat.factorial (r + i) : ℝ) =
        (Nat.factorial (j + h + r) : ℝ) := by
    rw [hchoose'] at hchoose₁
    exact_mod_cast hchoose₁
  have hcore :
      (Nat.descFactorial (j + h) i : ℝ) *
          (Nat.descFactorial (r + j) (j - i) : ℝ) *
          (Nat.factorial (j + h + r) : ℝ) =
        (Nat.factorial (j + h) : ℝ) *
          (Nat.factorial (r + j) : ℝ) *
          (Nat.choose (j + h + r) (j + h - i) : ℝ) := by
    calc
      _ = (Nat.descFactorial (j + h) i : ℝ) *
          (Nat.descFactorial (r + j) (j - i) : ℝ) *
          ((Nat.choose (j + h + r) (j + h - i) : ℝ) *
            (Nat.factorial (j + h - i) : ℝ) *
            (Nat.factorial (r + i) : ℝ)) := by rw [hchooser]
      _ = ((Nat.factorial (j + h - i) : ℝ) *
            (Nat.descFactorial (j + h) i : ℝ)) *
          ((Nat.factorial (r + i) : ℝ) *
            (Nat.descFactorial (r + j) (j - i) : ℝ)) *
          (Nat.choose (j + h + r) (j + h - i) : ℝ) := by ring
      _ = _ := by rw [hdesc₁r, hdesc₂r]
  unfold jacobiHypergeomScale hypergeomCount jacobiCoeff jacobiK jacobiM jacobiN
  simp only [Nat.cast_mul]
  field_simp [Nat.factorial_ne_zero]
  have hscaled := congrArg
    (fun x : ℝ => (Nat.choose j i : ℝ) * x) hcore
  have hNsub : 2 * j + h + r - j = j + h + r := by omega
  simp only [hNsub] at *
  nlinarith [hscaled]

theorem jacobiCoeff_zero_of_lt {j h r i : ℕ} (hij : j < i) :
    jacobiCoeff j h r i = 0 := by
  simp [jacobiCoeff, Nat.choose_eq_zero_of_lt hij]

theorem hypergeomCount_jacobi_zero_of_lt {j h r i : ℕ} (hij : j < i) :
    hypergeomCount (jacobiN j h r) (jacobiK j) (jacobiM j h) i = 0 := by
  simp [hypergeomCount, jacobiK, Nat.choose_eq_zero_of_lt hij]

theorem jacobiCoeff_scaled_hypergeomCount (j h r i : ℕ) :
    (jacobiCoeff j h r i : ℝ) =
      jacobiHypergeomScale j h r *
        (hypergeomCount (jacobiN j h r) (jacobiK j) (jacobiM j h) i : ℝ) := by
  by_cases hi : i ≤ j
  · exact jacobiCoeff_scaled_hypergeomCount_of_le hi
  · have hij : j < i := Nat.lt_of_not_ge hi
    simp [jacobiCoeff_zero_of_lt hij, hypergeomCount_jacobi_zero_of_lt hij]

theorem jacobiPGF_eval_eq_scaled_hypergeomPolynomial
    (j h r : ℕ) (z : ℝ) :
    (jacobiPGF j h r).eval z =
      jacobiHypergeomScale j h r *
        hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) z := by
  classical
  have hleft :
      (jacobiPGF j h r).eval z =
        ∑ i ∈ Finset.range (j + 1),
          (jacobiCoeff j h r i : ℝ) * z ^ i := by
    simp only [jacobiPGF, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  have hrange :
      ∑ i ∈ Finset.range (j + 1),
          (jacobiCoeff j h r i : ℝ) * z ^ i =
        ∑ i ∈ Finset.range (j + h + 1),
          (jacobiCoeff j h r i : ℝ) * z ^ i := by
    apply Finset.sum_subset
    · exact Finset.range_mono (by omega)
    · intro i hi hnot
      have hij : j < i := by
        simp only [Finset.mem_range] at hnot
        omega
      simp [jacobiCoeff_zero_of_lt hij]
  calc
    (jacobiPGF j h r).eval z =
        ∑ i ∈ Finset.range (j + 1),
          (jacobiCoeff j h r i : ℝ) * z ^ i := hleft
    _ = ∑ i ∈ Finset.range (j + h + 1),
          (jacobiCoeff j h r i : ℝ) * z ^ i := hrange
    _ = jacobiHypergeomScale j h r *
          ∑ i ∈ Finset.range (j + h + 1),
            (hypergeomCount (jacobiN j h r) (jacobiK j)
              (jacobiM j h) i : ℝ) * z ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [jacobiCoeff_scaled_hypergeomCount]
        ring
    _ = jacobiHypergeomScale j h r *
          hypergeomPolynomial (jacobiN j h r) (jacobiK j)
            (jacobiM j h) z := by
        simp only [hypergeomPolynomial, jacobiM]

#print axioms jacobiCoeff_scaled_hypergeomCount_of_le
#print axioms jacobiCoeff_scaled_hypergeomCount
#print axioms jacobiPGF_eval_eq_scaled_hypergeomPolynomial

end ExactHoeffding
