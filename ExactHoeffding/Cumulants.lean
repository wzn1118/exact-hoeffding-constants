import ExactHoeffding.GeneralFactorialMoments
import ExactHoeffding.OrdinaryMomentsComplete
import Mathlib.Tactic.IntervalCases

/-!
# Raw moments and cumulants of the finite hypergeometric law

This module keeps the finite-distribution definitions explicit.  The raw
moment identities use the falling-factorial basis, with the Stirling
polynomials through degree four proved pointwise over `Nat` and then cast to
`Real`.  The third cumulant is given in its standard closed form for
`N >= 3`; the fourth cumulant is retained in an exact falling-factorial form.
-/

namespace ExactHoeffding

noncomputable section

/-- The `r`-th raw moment of a finitely supported weighted law. -/
def finiteRawMoment {ι : Type*} (s : Finset ι) (x w : ι → ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ s, (x i) ^ r * w i

/-- The first four cumulant polynomials in raw moments. -/
def finiteCumulant1 {ι : Type*} (s : Finset ι) (x w : ι → ℝ) : ℝ :=
  finiteRawMoment s x w 1

def finiteCumulant2 {ι : Type*} (s : Finset ι) (x w : ι → ℝ) : ℝ :=
  finiteRawMoment s x w 2 - finiteRawMoment s x w 1 ^ 2

def finiteCumulant3 {ι : Type*} (s : Finset ι) (x w : ι → ℝ) : ℝ :=
  finiteRawMoment s x w 3 - 3 * finiteRawMoment s x w 2 *
      finiteRawMoment s x w 1 + 2 * finiteRawMoment s x w 1 ^ 3

def finiteCumulant4 {ι : Type*} (s : Finset ι) (x w : ι → ℝ) : ℝ :=
  finiteRawMoment s x w 4 - 4 * finiteRawMoment s x w 3 *
      finiteRawMoment s x w 1 - 3 * finiteRawMoment s x w 2 ^ 2 +
    12 * finiteRawMoment s x w 2 * finiteRawMoment s x w 1 ^ 2 -
    6 * finiteRawMoment s x w 1 ^ 4

/-- The falling-factorial moment of the hypergeometric count. -/
def hypergeomFactorialMoment (N k m q : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1),
    (Nat.descFactorial i q : ℝ) * hypergeomMass N k m i

/-- The raw moment of the hypergeometric count. -/
def hypergeomRawMoment (N k m r : ℕ) : ℝ :=
  finiteRawMoment (Finset.range (m + 1)) (fun i => (i : ℝ))
    (hypergeomMass N k m) r

def hypergeomCumulant1 (N k m : ℕ) : ℝ :=
  finiteCumulant1 (Finset.range (m + 1)) (fun i => (i : ℝ))
    (hypergeomMass N k m)

def hypergeomCumulant2 (N k m : ℕ) : ℝ :=
  finiteCumulant2 (Finset.range (m + 1)) (fun i => (i : ℝ))
    (hypergeomMass N k m)

def hypergeomCumulant3 (N k m : ℕ) : ℝ :=
  finiteCumulant3 (Finset.range (m + 1)) (fun i => (i : ℝ))
    (hypergeomMass N k m)

def hypergeomCumulant4 (N k m : ℕ) : ℝ :=
  finiteCumulant4 (Finset.range (m + 1)) (fun i => (i : ℝ))
    (hypergeomMass N k m)

/-- The all-degree factorial moment in the new named interface. -/
theorem hypergeom_factorial_moment_formula (N k m q : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomFactorialMoment N k m q =
      if q ≤ N then
        ((Nat.descFactorial m q : ℝ) * (Nat.descFactorial k q : ℝ)) /
          (Nat.descFactorial N q : ℝ)
      else 0 := by
  exact hypergeom_descFactorial_expectation N k m q hk hm

private lemma cast_descFactorial_one (i : ℕ) :
    (Nat.descFactorial i 1 : ℝ) = (i : ℝ) := by
  rw [Nat.descFactorial_one]

private lemma cast_descFactorial_succ (i q : ℕ) :
    (Nat.descFactorial i (q + 1) : ℝ) =
      ((i : ℝ) - (q : ℝ)) * (Nat.descFactorial i q : ℝ) := by
  rw [Nat.descFactorial_succ, Nat.cast_mul]
  by_cases hqi : q ≤ i
  · rw [Nat.cast_sub hqi]
  · have hzero : Nat.descFactorial i q = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [hzero]

private lemma cast_descFactorial_two (i : ℕ) :
    (Nat.descFactorial i 2 : ℝ) = (i : ℝ) * ((i : ℝ) - 1) := by
  rw [cast_descFactorial_succ i 1, cast_descFactorial_one]
  norm_num
  ring

private lemma cast_descFactorial_three (i : ℕ) :
    (Nat.descFactorial i 3 : ℝ) =
      (i : ℝ) * ((i : ℝ) - 1) * ((i : ℝ) - 2) := by
  rw [cast_descFactorial_succ i 2, cast_descFactorial_two]
  norm_num
  ring

private lemma cast_descFactorial_four (i : ℕ) :
    (Nat.descFactorial i 4 : ℝ) =
      (i : ℝ) * ((i : ℝ) - 1) * ((i : ℝ) - 2) * ((i : ℝ) - 3) := by
  rw [cast_descFactorial_succ i 3, cast_descFactorial_three]
  norm_num
  ring

private lemma stirling_one (i : ℕ) :
    (i : ℝ) ^ 1 = (Nat.descFactorial i 1 : ℝ) := by
  rw [cast_descFactorial_one]
  simp

private lemma stirling_two (i : ℕ) :
    (i : ℝ) ^ 2 = (Nat.descFactorial i 2 : ℝ) +
      (Nat.descFactorial i 1 : ℝ) := by
  rw [cast_descFactorial_two, cast_descFactorial_one]
  ring

private lemma stirling_three (i : ℕ) :
    (i : ℝ) ^ 3 = (Nat.descFactorial i 3 : ℝ) +
      3 * (Nat.descFactorial i 2 : ℝ) +
      (Nat.descFactorial i 1 : ℝ) := by
  rw [cast_descFactorial_three, cast_descFactorial_two,
    cast_descFactorial_one]
  ring

private lemma stirling_four (i : ℕ) :
    (i : ℝ) ^ 4 = (Nat.descFactorial i 4 : ℝ) +
      6 * (Nat.descFactorial i 3 : ℝ) +
      7 * (Nat.descFactorial i 2 : ℝ) +
      (Nat.descFactorial i 1 : ℝ) := by
  rw [cast_descFactorial_four, cast_descFactorial_three,
    cast_descFactorial_two, cast_descFactorial_one]
  ring

private lemma hypergeom_raw_one_factorial (N k m : ℕ) :
    hypergeomRawMoment N k m 1 = hypergeomFactorialMoment N k m 1 := by
  unfold hypergeomRawMoment finiteRawMoment hypergeomFactorialMoment
  apply Finset.sum_congr rfl
  intro i hi
  rw [stirling_one]

private lemma hypergeom_raw_two_factorial (N k m : ℕ) :
    hypergeomRawMoment N k m 2 =
      hypergeomFactorialMoment N k m 2 +
        hypergeomFactorialMoment N k m 1 := by
  unfold hypergeomRawMoment finiteRawMoment hypergeomFactorialMoment
  calc
    (∑ i ∈ Finset.range (m + 1), (i : ℝ) ^ 2 * hypergeomMass N k m i) =
        ∑ i ∈ Finset.range (m + 1),
          ((Nat.descFactorial i 2 : ℝ) +
            (Nat.descFactorial i 1 : ℝ)) * hypergeomMass N k m i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [stirling_two]
    _ = (∑ i ∈ Finset.range (m + 1),
          (Nat.descFactorial i 2 : ℝ) * hypergeomMass N k m i) +
        ∑ i ∈ Finset.range (m + 1),
          (Nat.descFactorial i 1 : ℝ) * hypergeomMass N k m i := by
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]

private lemma hypergeom_raw_three_factorial (N k m : ℕ) :
    hypergeomRawMoment N k m 3 =
      hypergeomFactorialMoment N k m 3 +
        3 * hypergeomFactorialMoment N k m 2 +
        hypergeomFactorialMoment N k m 1 := by
  unfold hypergeomRawMoment finiteRawMoment hypergeomFactorialMoment
  calc
    (∑ i ∈ Finset.range (m + 1), (i : ℝ) ^ 3 * hypergeomMass N k m i) =
        ∑ i ∈ Finset.range (m + 1),
          ((Nat.descFactorial i 3 : ℝ) +
            3 * (Nat.descFactorial i 2 : ℝ) +
            (Nat.descFactorial i 1 : ℝ)) * hypergeomMass N k m i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [stirling_three]
    _ = (∑ i ∈ Finset.range (m + 1),
          (Nat.descFactorial i 3 : ℝ) * hypergeomMass N k m i) +
        3 * (∑ i ∈ Finset.range (m + 1),
          (Nat.descFactorial i 2 : ℝ) * hypergeomMass N k m i) +
        ∑ i ∈ Finset.range (m + 1),
          (Nat.descFactorial i 1 : ℝ) * hypergeomMass N k m i := by
          simp_rw [add_mul, mul_assoc]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [← Finset.mul_sum]

private lemma hypergeom_raw_four_factorial (N k m : ℕ) :
    hypergeomRawMoment N k m 4 =
      hypergeomFactorialMoment N k m 4 +
        6 * hypergeomFactorialMoment N k m 3 +
        7 * hypergeomFactorialMoment N k m 2 +
        hypergeomFactorialMoment N k m 1 := by
  unfold hypergeomRawMoment finiteRawMoment hypergeomFactorialMoment
  calc
    (∑ i ∈ Finset.range (m + 1), (i : ℝ) ^ 4 * hypergeomMass N k m i) =
        ∑ i ∈ Finset.range (m + 1),
          ((Nat.descFactorial i 4 : ℝ) +
            6 * (Nat.descFactorial i 3 : ℝ) +
            7 * (Nat.descFactorial i 2 : ℝ) +
            (Nat.descFactorial i 1 : ℝ)) * hypergeomMass N k m i := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [stirling_four]
    _ = (∑ i ∈ Finset.range (m + 1),
          (Nat.descFactorial i 4 : ℝ) * hypergeomMass N k m i) +
        6 * (∑ i ∈ Finset.range (m + 1),
          (Nat.descFactorial i 3 : ℝ) * hypergeomMass N k m i) +
        7 * (∑ i ∈ Finset.range (m + 1),
          (Nat.descFactorial i 2 : ℝ) * hypergeomMass N k m i) +
        ∑ i ∈ Finset.range (m + 1),
          (Nat.descFactorial i 1 : ℝ) * hypergeomMass N k m i := by
          simp_rw [add_mul, mul_assoc]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]

private lemma hypergeom_factorial_moment_one (N k m : ℕ)
    (hN : 1 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomFactorialMoment N k m 1 =
      (m : ℝ) * (k : ℝ) / (N : ℝ) := by
  rw [hypergeom_factorial_moment_formula N k m 1 hk hm, if_pos hN]
  rw [cast_descFactorial_one, cast_descFactorial_one,
    cast_descFactorial_one]

private lemma hypergeom_factorial_moment_two (N k m : ℕ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomFactorialMoment N k m 2 =
      ((m : ℝ) * ((m : ℝ) - 1) * (k : ℝ) * ((k : ℝ) - 1)) /
        ((N : ℝ) * ((N : ℝ) - 1)) := by
  rw [hypergeom_factorial_moment_formula N k m 2 hk hm, if_pos hN]
  rw [cast_descFactorial_two, cast_descFactorial_two,
    cast_descFactorial_two]
  ring

private lemma hypergeom_factorial_moment_three (N k m : ℕ)
    (hN : 3 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomFactorialMoment N k m 3 =
      ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) *
          (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) /
        ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2)) := by
  rw [hypergeom_factorial_moment_formula N k m 3 hk hm, if_pos hN]
  rw [cast_descFactorial_three, cast_descFactorial_three,
    cast_descFactorial_three]
  ring

private lemma hypergeom_factorial_moment_four (N k m : ℕ)
    (hN : 4 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomFactorialMoment N k m 4 =
      ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 3) *
          (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3)) /
        ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) * ((N : ℝ) - 3)) := by
  rw [hypergeom_factorial_moment_formula N k m 4 hk hm, if_pos hN]
  rw [cast_descFactorial_four, cast_descFactorial_four,
    cast_descFactorial_four]
  ring

/-- Raw moments one through four in the falling-factorial basis. -/
theorem hypergeom_raw_moment_one (N k m : ℕ)
    (hN : 1 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomRawMoment N k m 1 =
      (m : ℝ) * (k : ℝ) / (N : ℝ) := by
  rw [hypergeom_raw_one_factorial]
  exact hypergeom_factorial_moment_one N k m hN hk hm

theorem hypergeom_raw_moment_two (N k m : ℕ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomRawMoment N k m 2 =
      ((m : ℝ) * ((m : ℝ) - 1) * (k : ℝ) * ((k : ℝ) - 1)) /
        ((N : ℝ) * ((N : ℝ) - 1)) +
      (m : ℝ) * (k : ℝ) / (N : ℝ) := by
  rw [hypergeom_raw_two_factorial,
    hypergeom_factorial_moment_two N k m hN hk hm,
    hypergeom_factorial_moment_one N k m (by omega) hk hm]

theorem hypergeom_raw_moment_three (N k m : ℕ)
    (hN : 3 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomRawMoment N k m 3 =
      ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) *
          (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) /
        ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2)) +
      3 * (((m : ℝ) * ((m : ℝ) - 1) * (k : ℝ) * ((k : ℝ) - 1)) /
        ((N : ℝ) * ((N : ℝ) - 1))) +
      (m : ℝ) * (k : ℝ) / (N : ℝ) := by
  rw [hypergeom_raw_three_factorial,
    hypergeom_factorial_moment_three N k m hN hk hm,
    hypergeom_factorial_moment_two N k m (by omega) hk hm,
    hypergeom_factorial_moment_one N k m (by omega) hk hm]

theorem hypergeom_raw_moment_four (N k m : ℕ)
    (hN : 4 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomRawMoment N k m 4 =
      ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * ((m : ℝ) - 3) *
          (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) * ((k : ℝ) - 3)) /
        ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) * ((N : ℝ) - 3)) +
      6 * (((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) *
          (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) /
        ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2))) +
      7 * (((m : ℝ) * ((m : ℝ) - 1) * (k : ℝ) * ((k : ℝ) - 1)) /
        ((N : ℝ) * ((N : ℝ) - 1))) +
      (m : ℝ) * (k : ℝ) / (N : ℝ) := by
  rw [hypergeom_raw_four_factorial,
    hypergeom_factorial_moment_four N k m hN hk hm,
    hypergeom_factorial_moment_three N k m (by omega) hk hm,
    hypergeom_factorial_moment_two N k m (by omega) hk hm,
    hypergeom_factorial_moment_one N k m (by omega) hk hm]

/-- The first cumulant is the exact hypergeometric mean. -/
theorem hypergeom_cumulant1_complete (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomCumulant1 N k m =
      (m : ℝ) * (k : ℝ) / (N : ℝ) := by
  simpa [hypergeomCumulant1, finiteCumulant1, hypergeomRawMoment,
    finiteRawMoment] using hypergeom_mean_complete N k m hk hm

/-- The second cumulant agrees with the exact finite-law variance. -/
theorem hypergeom_cumulant2_complete (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomCumulant2 N k m =
      (m : ℝ) * (k : ℝ) * ((N - k : ℕ) : ℝ) * ((N - m : ℕ) : ℝ) /
        ((N : ℝ) ^ 2 * ((N : ℝ) - 1)) := by
  by_cases hN : 2 ≤ N
  · change hypergeomRawMoment N k m 2 -
      hypergeomRawMoment N k m 1 ^ 2 = _
    rw [hypergeom_raw_moment_two N k m hN hk hm,
      hypergeom_raw_moment_one N k m (by omega) hk hm]
    have hNk : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) := by
      rw [Nat.cast_sub hk]
    have hNm : ((N - m : ℕ) : ℝ) = (N : ℝ) - (m : ℝ) := by
      rw [Nat.cast_sub hm]
    rw [hNk, hNm]
    have hN0 : (N : ℝ) ≠ 0 := by
      exact_mod_cast (show N ≠ 0 by omega)
    have hN1 : (N : ℝ) - 1 ≠ 0 := by
      have h : (1 : ℝ) < (N : ℝ) := by
        exact_mod_cast (show 1 < N by omega)
      linarith
    field_simp [hN0, hN1]
    ring
  · have hNsmall : N ≤ 1 := by omega
    interval_cases N <;> interval_cases k <;> interval_cases m <;>
      norm_num [hypergeomCumulant2, finiteCumulant2, finiteRawMoment,
        Finset.sum_range_succ, hypergeomMass, hypergeomCount]

/-- A fourth cumulant written without expanding the factorial terms. -/
def hypergeomCumulant4FactorialTerms (N k m : ℕ) : ℝ :=
  let f1 := hypergeomFactorialMoment N k m 1
  let f2 := hypergeomFactorialMoment N k m 2
  let f3 := hypergeomFactorialMoment N k m 3
  let f4 := hypergeomFactorialMoment N k m 4
  (f4 + 6 * f3 + 7 * f2 + f1) -
      4 * (f3 + 3 * f2 + f1) * f1 -
      3 * (f2 + f1) ^ 2 +
      12 * (f2 + f1) * f1 ^ 2 - 6 * f1 ^ 4

/-- The fourth cumulant is exactly the factorial-moment expression, including
the low-population cases where higher falling factorial moments vanish. -/
theorem hypergeom_cumulant4_factorial_complete (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomCumulant4 N k m =
      hypergeomCumulant4FactorialTerms N k m := by
  change hypergeomRawMoment N k m 4 -
      4 * hypergeomRawMoment N k m 3 * hypergeomRawMoment N k m 1 -
      3 * hypergeomRawMoment N k m 2 ^ 2 +
      12 * hypergeomRawMoment N k m 2 * hypergeomRawMoment N k m 1 ^ 2 -
      6 * hypergeomRawMoment N k m 1 ^ 4 = _
  rw [hypergeom_raw_four_factorial, hypergeom_raw_three_factorial,
    hypergeom_raw_two_factorial, hypergeom_raw_one_factorial]
  rfl

/-- For `N >= 4`, the fourth cumulant has the displayed closed factorial
formula, with no expansion of the resulting rational polynomial required. -/
theorem hypergeom_cumulant4_factorial_closed (N k m : ℕ)
    (hN : 4 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomCumulant4 N k m =
      (let f1 := (m : ℝ) * (k : ℝ) / (N : ℝ)
       let f2 := ((m : ℝ) * ((m : ℝ) - 1) * (k : ℝ) * ((k : ℝ) - 1)) /
         ((N : ℝ) * ((N : ℝ) - 1))
       let f3 := ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) *
           (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2)) /
         ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2))
       let f4 := ((m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) *
           ((m : ℝ) - 3) * (k : ℝ) * ((k : ℝ) - 1) *
           ((k : ℝ) - 2) * ((k : ℝ) - 3)) /
         ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) * ((N : ℝ) - 3))
       (f4 + 6 * f3 + 7 * f2 + f1) -
         4 * (f3 + 3 * f2 + f1) * f1 -
         3 * (f2 + f1) ^ 2 +
         12 * (f2 + f1) * f1 ^ 2 - 6 * f1 ^ 4) := by
  rw [hypergeom_cumulant4_factorial_complete N k m hk hm]
  simp only [hypergeomCumulant4FactorialTerms,
    hypergeom_factorial_moment_four N k m hN hk hm,
    hypergeom_factorial_moment_three N k m (by omega) hk hm,
    hypergeom_factorial_moment_two N k m (by omega) hk hm,
    hypergeom_factorial_moment_one N k m (by omega) hk hm]

/-- For `N >= 3`, the third cumulant has the standard exact closed form. -/
theorem hypergeom_cumulant3_standard (N k m : ℕ)
    (hN : 3 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomCumulant3 N k m =
      (m : ℝ) * (k : ℝ) * ((N - k : ℕ) : ℝ) * ((N - m : ℕ) : ℝ) *
          ((N : ℝ) - 2 * (k : ℝ)) * ((N : ℝ) - 2 * (m : ℝ)) /
        ((N : ℝ) ^ 3 * ((N : ℝ) - 1) * ((N : ℝ) - 2)) := by
  change hypergeomRawMoment N k m 3 -
      3 * hypergeomRawMoment N k m 2 * hypergeomRawMoment N k m 1 +
      2 * hypergeomRawMoment N k m 1 ^ 3 = _
  rw [hypergeom_raw_moment_three N k m hN hk hm,
    hypergeom_raw_moment_two N k m (by omega) hk hm,
    hypergeom_raw_moment_one N k m (by omega) hk hm]
  have hNk : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) := by
    rw [Nat.cast_sub hk]
  have hNm : ((N - m : ℕ) : ℝ) = (N : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub hm]
  rw [hNk, hNm]
  have hN0 : (N : ℝ) ≠ 0 := by
    exact_mod_cast (show N ≠ 0 by omega)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by
    have h : (1 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 1 < N by omega)
    linarith
  have hN2 : (N : ℝ) - 2 ≠ 0 := by
    have h : (2 : ℝ) < (N : ℝ) := by
      exact_mod_cast (show 2 < N by omega)
    linarith
  field_simp [hN0, hN1, hN2]
  ring

/-- The third cumulant is zero in the `N <= 2` boundary cases.  This is
proved from the actual finite support, not by substituting into a singular
closed formula. -/
theorem hypergeom_cumulant3_degenerate (N k m : ℕ)
    (hN : N ≤ 2) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomCumulant3 N k m = 0 := by
  interval_cases N <;> interval_cases k <;> interval_cases m <;>
    norm_num [hypergeomCumulant3, finiteCumulant3, finiteRawMoment,
      Finset.sum_range_succ, hypergeomMass, hypergeomCount]

end

end ExactHoeffding
