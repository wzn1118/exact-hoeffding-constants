import ExactHoeffding.HighCumulants
import Mathlib.Tactic.IntervalCases

/-!
# Continuous margin algebra for the fixed-sample hypergeometric family

This file records only the algebraic input used by the finite-imbalance
calculation.  The margin `d` is real, while `N` and `m` remain natural
parameters.  No optimizer or analytic continuation theorem is asserted here.
-/

namespace ExactHoeffding

noncomputable section

/-- Falling-factorial moments of the real-margin family, with `e = 1/N`. -/
def marginFactorialMoment (N m q : ℕ) (d : ℝ) : ℝ :=
  (Nat.descFactorial m q : ℝ) *
    ∏ r ∈ Finset.range q,
      (((1 - d) / 2 - (r : ℝ) / (N : ℝ)) /
        (1 - (r : ℝ) / (N : ℝ)))

/-- Raw moments obtained from the falling-factorial basis. -/
def marginRawMoment (N m r : ℕ) (d : ℝ) : ℝ :=
  momentFromFactorials (fun q => marginFactorialMoment N m q d) r

/-- The second, third and fourth cumulant polynomials of the margin family. -/
def marginCumulant2 (N m : ℕ) (d : ℝ) : ℝ :=
  let a := marginRawMoment N m 1 d
  let b := marginRawMoment N m 2 d
  b - a ^ 2

def marginCumulant3 (N m : ℕ) (d : ℝ) : ℝ :=
  let a := marginRawMoment N m 1 d
  let b := marginRawMoment N m 2 d
  let c := marginRawMoment N m 3 d
  c - 3 * b * a + 2 * a ^ 3

def marginCumulant4 (N m : ℕ) (d : ℝ) : ℝ :=
  let a := marginRawMoment N m 1 d
  let b := marginRawMoment N m 2 d
  let c := marginRawMoment N m 3 d
  let e := marginRawMoment N m 4 d
  e - 4 * c * a - 3 * b ^ 2 + 12 * b * a ^ 2 - 6 * a ^ 4

private lemma margin_denoms_nonzero (N : ℕ) (hN : 5 ≤ N) (r : ℕ) (hr : r < 4) :
    (1 : ℝ) - (r : ℝ) / (N : ℝ) ≠ 0 := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hNr : (r : ℝ) < (N : ℝ) := by
    exact_mod_cast (show r < N by omega)
  intro h
  field_simp [hN0] at h
  nlinarith

private lemma margin_moment_one (N m : ℕ) (d : ℝ) :
    marginRawMoment N m 1 d =
      (m : ℝ) * (1 - d) / 2 := by
  unfold marginRawMoment marginFactorialMoment momentFromFactorials
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.descFactorial_zero,
    Nat.cast_one, Finset.prod_range_succ, Finset.prod_range_zero, mul_one, pow_zero, add_zero,
    Nat.descFactorial_one]
  ring

private lemma margin_moment_two (N m : ℕ) (d : ℝ) :
    marginRawMoment N m 2 d =
      marginFactorialMoment N m 2 d + marginFactorialMoment N m 1 d := by
  rfl

private lemma margin_moment_three (N m : ℕ) (d : ℝ) :
    marginRawMoment N m 3 d =
      marginFactorialMoment N m 3 d + 3 * marginFactorialMoment N m 2 d +
        marginFactorialMoment N m 1 d := by
  rfl

private lemma margin_moment_four (N m : ℕ) (d : ℝ) :
    marginRawMoment N m 4 d =
      marginFactorialMoment N m 4 d + 6 * marginFactorialMoment N m 3 d +
        7 * marginFactorialMoment N m 2 d + marginFactorialMoment N m 1 d := by
  rfl

/-- Closed second cumulant of the continuous-margin family. -/
theorem margin_cumulant2_closed (N m : ℕ) (hN : 5 ≤ N) (d : ℝ) :
    marginCumulant2 N m d =
      (m : ℝ) * ((N : ℝ) - (m : ℝ)) * (1 - d ^ 2) /
        (4 * ((N : ℝ) - 1)) := by
  unfold marginCumulant2
  rw [margin_moment_one]
  rw [margin_moment_two]
  unfold marginFactorialMoment
  simp only [Finset.prod_range_succ, Finset.prod_range_zero,
    descFactorial_cast_product]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  field_simp [hN0, hN1]
  ring

/-- Closed third cumulant of the continuous-margin family. -/
theorem margin_cumulant3_closed (N m : ℕ) (hN : 5 ≤ N) (d : ℝ) :
    marginCumulant3 N m d =
      (m : ℝ) * ((N : ℝ) - (m : ℝ)) * ((N : ℝ) - 2 * (m : ℝ)) *
        d * (1 - d ^ 2) /
        (4 * (((N : ℝ) - 2) * ((N : ℝ) - 1))) := by
  unfold marginCumulant3
  rw [margin_moment_one, margin_moment_two, margin_moment_three]
  unfold marginFactorialMoment
  simp only [Finset.prod_range_succ, Finset.prod_range_zero,
    descFactorial_cast_product]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hN2 : (N : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  field_simp [hN0, hN1, hN2]
  ring

/-- The polynomial appearing in the exact fourth-cumulant formula. -/
def marginFourthPolynomial (N m : ℕ) (d : ℝ) : ℝ :=
  let n := (N : ℝ)
  let x := (m : ℝ)
  3 * n ^ 3 * d ^ 2 - n ^ 3 - 15 * n ^ 2 * d ^ 2 * x -
    3 * n ^ 2 * d ^ 2 + 3 * n ^ 2 * x + 3 * n ^ 2 +
    15 * n * d ^ 2 * x ^ 2 + 18 * n * d ^ 2 * x -
    3 * n * x ^ 2 - 6 * n * x - 2 * n - 18 * d ^ 2 * x ^ 2 + 6 * x ^ 2

/-- Closed fourth cumulant of the continuous-margin family. -/
theorem margin_cumulant4_closed (N m : ℕ) (hN : 5 ≤ N) (d : ℝ) :
    marginCumulant4 N m d =
      (m : ℝ) * ((N : ℝ) - (m : ℝ)) * (1 - d ^ 2) *
        marginFourthPolynomial N m d /
        (8 * (((N : ℝ) - 3) * ((N : ℝ) - 2) * ((N : ℝ) - 1) ^ 2)) := by
  unfold marginCumulant4
  rw [margin_moment_one, margin_moment_two, margin_moment_three,
    margin_moment_four]
  unfold marginFactorialMoment marginFourthPolynomial
  simp only [Finset.prod_range_succ, Finset.prod_range_zero,
    descFactorial_cast_product]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hN2 : (N : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  have hN3 : (N : ℝ) - 3 ≠ 0 := by
    have : (3 : ℝ) < (N : ℝ) := by exact_mod_cast (show 3 < N by omega)
    linarith
  field_simp [hN0, hN1, hN2, hN3]
  ring

/-- The denominator used by the finite-imbalance coefficient. -/
def imbalanceD (N m : ℕ) : ℝ :=
  (N : ℝ) ^ 2 - (N : ℝ) - 3 * (m : ℝ) * ((N : ℝ) - (m : ℝ))

/-- The centered fourth cumulant at zero margin. -/
theorem margin_cumulant4_zero (N m : ℕ) (hN : 5 ≤ N) :
    marginCumulant4 N m 0 =
      - (m : ℝ) * ((N : ℝ) - (m : ℝ)) * imbalanceD N m /
        (8 * ((N : ℝ) - 3) * ((N : ℝ) - 1) ^ 2) := by
  rw [margin_cumulant4_closed N m hN 0]
  unfold marginFourthPolynomial imbalanceD
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hN2 : (N : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  have hN3 : (N : ℝ) - 3 ≠ 0 := by
    have : (3 : ℝ) < (N : ℝ) := by exact_mod_cast (show 3 < N by omega)
    linarith
  field_simp [hN1, hN2, hN3]
  ring


/-- The linear stationary coefficient from the finite-imbalance calculation. -/
def imbalanceT (N m : ℕ) : ℝ :=
  4 * ((N : ℝ) - 2 * (m : ℝ)) * ((N : ℝ) - 3) * ((N : ℝ) - 1) /
    (((N : ℝ) - 2) * imbalanceD N m)

/-- The normalized quadratic imbalance coefficient. -/
def imbalanceA (N m : ℕ) : ℝ :=
  (N : ℝ) / (3 * ((N : ℝ) - 1)) +
    2 * (N : ℝ) ^ 2 * ((N : ℝ) - 4) * ((m : ℝ) - 1) *
        ((N : ℝ) - (m : ℝ) - 1) /
      (3 * ((N : ℝ) - 2) ^ 2 * ((N : ℝ) - 1) * imbalanceD N m)

/-- Positivity of the exact imbalance denominator in the stated range. -/
theorem imbalanceD_pos (N m : ℕ) (hN : 5 ≤ N) (hm : 2 ≤ m)
    (hNm : 2 * m ≤ N) : 0 < imbalanceD N m := by
  unfold imbalanceD
  have hN5 : (5 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hmn : 0 ≤ (m : ℝ) := by positivity
  have hNm' : 2 * (m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNm
  have hprod : (m : ℝ) * ((N : ℝ) - (m : ℝ)) ≤ (N : ℝ) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((N : ℝ) - 2 * (m : ℝ))]
  nlinarith

/-- The two algebraically equivalent forms of `A`. -/
theorem imbalanceA_identity (N m : ℕ) (hN : 5 ≤ N) (hm : 2 ≤ m)
    (hNm : 2 * m ≤ N) :
    imbalanceA N m =
      (N : ℝ) / ((N : ℝ) - 1) *
        (1 - 2 * ((N : ℝ) - 2 * (m : ℝ)) ^ 2 * ((N : ℝ) - 3) *
          ((N : ℝ) - 1) /
          (3 * ((N : ℝ) - 2) ^ 2 * imbalanceD N m)) := by
  have hD : imbalanceD N m ≠ 0 := ne_of_gt (imbalanceD_pos N m hN hm hNm)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hN2 : (N : ℝ) - 2 ≠ 0 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  unfold imbalanceA
  simp only [imbalanceD]
  have hDprime :
      - (N : ℝ) - (N : ℝ) * (m : ℝ) * 3 + (N : ℝ) ^ 2 +
        (m : ℝ) ^ 2 * 3 ≠ 0 := by
    have heq :
        - (N : ℝ) - (N : ℝ) * (m : ℝ) * 3 + (N : ℝ) ^ 2 +
            (m : ℝ) ^ 2 * 3 = imbalanceD N m := by
      unfold imbalanceD
      ring
    rw [heq]
    exact hD
  have hDnorm :
      (N : ℝ) * ((N : ℝ) - 1) - 3 * (m : ℝ) *
          ((N : ℝ) - (m : ℝ)) ≠ 0 := by
    intro hz
    apply hD
    unfold imbalanceD
    nlinarith
  field_simp [hDprime, hDnorm, hN1, hN2]
  ring

/-- The Bernoulli coefficient is strictly smaller for every `m ≥ 2`. -/
theorem imbalanceA_strict (N m : ℕ) (hN : 5 ≤ N) (hm : 2 ≤ m)
    (hNm : 2 * m ≤ N) :
    imbalanceA N m - (N : ℝ) / (3 * ((N : ℝ) - 1)) > 0 := by
  have hD : 0 < imbalanceD N m := imbalanceD_pos N m hN hm hNm
  have hN : (0 : ℝ) < (N : ℝ) := by positivity
  have hN4 : (0 : ℝ) < (N : ℝ) - 4 := by
    have : (4 : ℝ) < (N : ℝ) := by exact_mod_cast (show 4 < N by omega)
    linarith
  have hm1 : (0 : ℝ) < (m : ℝ) - 1 := by
    have : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
    linarith
  have hNm1 : (0 : ℝ) < (N : ℝ) - (m : ℝ) - 1 := by
    have hmn : (m : ℝ) + 1 < (N : ℝ) := by
      have : m + 1 < N := by omega
      exact_mod_cast this
    linarith
  have hN1 : 0 < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    linarith
  have hN2 : 0 < (N : ℝ) - 2 := by
    have : (2 : ℝ) < (N : ℝ) := by exact_mod_cast (show 2 < N by omega)
    linarith
  have hden : 0 < 3 * ((N : ℝ) - 2) ^ 2 * ((N : ℝ) - 1) * imbalanceD N m := by
    positivity
  unfold imbalanceA
  have hq : 0 <
      2 * (N : ℝ) ^ 2 * ((N : ℝ) - 4) * ((m : ℝ) - 1) *
        ((N : ℝ) - (m : ℝ) - 1) /
      (3 * ((N : ℝ) - 2) ^ 2 * ((N : ℝ) - 1) * imbalanceD N m) := by
    exact div_pos (by positivity) hden
  convert hq using 1 <;> ring

end
end ExactHoeffding
