import ExactHoeffding.Cumulants
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Hypergeometric moments and cumulants through degree six

The identities in this module concern the actual hypergeometric masses.  All
population sizes are allowed in the factorial expressions: a factorial moment
whose order exceeds the population is zero.
-/

open Filter
open scoped Topology

namespace ExactHoeffding

noncomputable section

/-- The fifth cumulant polynomial, with arguments the first five raw moments. -/
def cumulant5Polynomial (a b c d e : ℝ) : ℝ :=
  e - 5 * d * a - 10 * c * b + 20 * c * a ^ 2 +
    30 * b ^ 2 * a - 60 * b * a ^ 3 + 24 * a ^ 5

/-- The sixth cumulant polynomial, with arguments the first six raw moments. -/
def cumulant6Polynomial (a b c d e f : ℝ) : ℝ :=
  f - 6 * e * a - 15 * d * b - 10 * c ^ 2 + 30 * d * a ^ 2 +
    120 * c * b * a + 30 * b ^ 3 - 120 * c * a ^ 3 -
    270 * b ^ 2 * a ^ 2 + 360 * b * a ^ 4 - 120 * a ^ 6

def finiteCumulant5 {ι : Type*} (s : Finset ι) (x w : ι → ℝ) : ℝ :=
  cumulant5Polynomial (finiteRawMoment s x w 1) (finiteRawMoment s x w 2)
    (finiteRawMoment s x w 3) (finiteRawMoment s x w 4) (finiteRawMoment s x w 5)

def finiteCumulant6 {ι : Type*} (s : Finset ι) (x w : ι → ℝ) : ℝ :=
  cumulant6Polynomial (finiteRawMoment s x w 1) (finiteRawMoment s x w 2)
    (finiteRawMoment s x w 3) (finiteRawMoment s x w 4) (finiteRawMoment s x w 5)
    (finiteRawMoment s x w 6)

/-- The degree-five case of the moment--cumulant recursion. -/
theorem finiteCumulant5_recursion {ι : Type*} (s : Finset ι) (x w : ι → ℝ) :
    finiteCumulant5 s x w = finiteRawMoment s x w 5 -
      (finiteCumulant1 s x w * finiteRawMoment s x w 4 +
        4 * finiteCumulant2 s x w * finiteRawMoment s x w 3 +
        6 * finiteCumulant3 s x w * finiteRawMoment s x w 2 +
        4 * finiteCumulant4 s x w * finiteRawMoment s x w 1) := by
  unfold finiteCumulant1 finiteCumulant2 finiteCumulant3 finiteCumulant4
    finiteCumulant5 cumulant5Polynomial
  ring

/-- The degree-six case of the moment--cumulant recursion. -/
theorem finiteCumulant6_recursion {ι : Type*} (s : Finset ι) (x w : ι → ℝ) :
    finiteCumulant6 s x w = finiteRawMoment s x w 6 -
      (finiteCumulant1 s x w * finiteRawMoment s x w 5 +
        5 * finiteCumulant2 s x w * finiteRawMoment s x w 4 +
        10 * finiteCumulant3 s x w * finiteRawMoment s x w 3 +
        10 * finiteCumulant4 s x w * finiteRawMoment s x w 2 +
        5 * finiteCumulant5 s x w * finiteRawMoment s x w 1) := by
  unfold finiteCumulant1 finiteCumulant2 finiteCumulant3 finiteCumulant4
    finiteCumulant5 finiteCumulant6 cumulant5Polynomial cumulant6Polynomial
  ring

def hypergeomCumulant5 (N k m : ℕ) : ℝ :=
  finiteCumulant5 (Finset.range (m + 1)) (fun i => (i : ℝ)) (hypergeomMass N k m)

def hypergeomCumulant6 (N k m : ℕ) : ℝ :=
  finiteCumulant6 (Finset.range (m + 1)) (fun i => (i : ℝ)) (hypergeomMass N k m)

private theorem descFactorial_cast_succ (i q : ℕ) :
    (Nat.descFactorial i (q + 1) : ℝ) =
      ((i : ℝ) - (q : ℝ)) * (Nat.descFactorial i q : ℝ) := by
  rw [Nat.descFactorial_succ, Nat.cast_mul]
  by_cases h : q ≤ i
  · rw [Nat.cast_sub h]
  · have hz : Nat.descFactorial i q = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [hz]

/-- Falling factorials over `Nat` agree with their real polynomial formula. -/
theorem descFactorial_cast_product (i q : ℕ) :
    (Nat.descFactorial i q : ℝ) = ∏ r ∈ Finset.range q, ((i : ℝ) - (r : ℝ)) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [descFactorial_cast_succ, ih, Finset.prod_range_succ]
      ring

private theorem stirling_one_six (i : ℕ) :
    (i : ℝ) ^ 1 = (Nat.descFactorial i 1 : ℝ) := by
  simp

private theorem stirling_two_six (i : ℕ) :
    (i : ℝ) ^ 2 = (Nat.descFactorial i 2 : ℝ) + (Nat.descFactorial i 1 : ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring

private theorem stirling_three_six (i : ℕ) :
    (i : ℝ) ^ 3 = (Nat.descFactorial i 3 : ℝ) +
      3 * (Nat.descFactorial i 2 : ℝ) + (Nat.descFactorial i 1 : ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring

private theorem stirling_four_six (i : ℕ) :
    (i : ℝ) ^ 4 = (Nat.descFactorial i 4 : ℝ) +
      6 * (Nat.descFactorial i 3 : ℝ) + 7 * (Nat.descFactorial i 2 : ℝ) +
      (Nat.descFactorial i 1 : ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring

theorem stirling_five_real (i : ℕ) :
    (i : ℝ) ^ 5 = (Nat.descFactorial i 5 : ℝ) +
      10 * (Nat.descFactorial i 4 : ℝ) + 25 * (Nat.descFactorial i 3 : ℝ) +
      15 * (Nat.descFactorial i 2 : ℝ) + (Nat.descFactorial i 1 : ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring

theorem stirling_six_real (i : ℕ) :
    (i : ℝ) ^ 6 = (Nat.descFactorial i 6 : ℝ) +
      15 * (Nat.descFactorial i 5 : ℝ) + 65 * (Nat.descFactorial i 4 : ℝ) +
      90 * (Nat.descFactorial i 3 : ℝ) + 31 * (Nat.descFactorial i 2 : ℝ) +
      (Nat.descFactorial i 1 : ℝ) := by
  simp only [descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  ring

/-- The first six Stirling transformations, as one moment interface. -/
def momentFromFactorials (f : ℕ → ℝ) (r : ℕ) : ℝ :=
  match r with
  | 0 => f 0
  | 1 => f 1
  | 2 => f 2 + f 1
  | 3 => f 3 + 3 * f 2 + f 1
  | 4 => f 4 + 6 * f 3 + 7 * f 2 + f 1
  | 5 => f 5 + 10 * f 4 + 25 * f 3 + 15 * f 2 + f 1
  | 6 => f 6 + 15 * f 5 + 65 * f 4 + 90 * f 3 + 31 * f 2 + f 1
  | _ + 7 => 0

theorem hypergeom_raw_moment_factorials_through_six (N k m r : ℕ) (hr : r ≤ 6) :
    hypergeomRawMoment N k m r =
      momentFromFactorials (hypergeomFactorialMoment N k m) r := by
  interval_cases r
  · simp [hypergeomRawMoment, finiteRawMoment, momentFromFactorials,
      hypergeomFactorialMoment]
  all_goals
    simp only [hypergeomRawMoment, finiteRawMoment, momentFromFactorials,
      hypergeomFactorialMoment, stirling_one_six, stirling_two_six, stirling_three_six,
      stirling_four_six, stirling_five_real, stirling_six_real, add_mul, mul_assoc,
      Finset.sum_add_distrib, ← Finset.mul_sum]

theorem hypergeom_raw_moment_five_factorial (N k m : ℕ) :
    hypergeomRawMoment N k m 5 = hypergeomFactorialMoment N k m 5 +
      10 * hypergeomFactorialMoment N k m 4 + 25 * hypergeomFactorialMoment N k m 3 +
      15 * hypergeomFactorialMoment N k m 2 + hypergeomFactorialMoment N k m 1 := by
  exact hypergeom_raw_moment_factorials_through_six N k m 5 (by omega)

theorem hypergeom_raw_moment_six_factorial (N k m : ℕ) :
    hypergeomRawMoment N k m 6 = hypergeomFactorialMoment N k m 6 +
      15 * hypergeomFactorialMoment N k m 5 + 65 * hypergeomFactorialMoment N k m 4 +
      90 * hypergeomFactorialMoment N k m 3 + 31 * hypergeomFactorialMoment N k m 2 +
      hypergeomFactorialMoment N k m 1 := by
  exact hypergeom_raw_moment_factorials_through_six N k m 6 (by omega)

/-- Totalized closed factorial moments, including the orders exceeding `N`. -/
def hypergeomFactorialClosed (N k m q : ℕ) : ℝ :=
  if q ≤ N then
    ((Nat.descFactorial m q : ℝ) * (Nat.descFactorial k q : ℝ)) /
      (Nat.descFactorial N q : ℝ)
  else 0

theorem hypergeom_raw_moment_closed_through_six (N k m r : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (hr : r ≤ 6) :
    hypergeomRawMoment N k m r =
      momentFromFactorials (hypergeomFactorialClosed N k m) r := by
  rw [hypergeom_raw_moment_factorials_through_six N k m r hr]
  have h : hypergeomFactorialMoment N k m = hypergeomFactorialClosed N k m := by
    funext q
    exact hypergeom_factorial_moment_formula N k m q hk hm
  rw [h]

theorem hypergeom_cumulant5_factorial_complete (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomCumulant5 N k m =
      cumulant5Polynomial
        (momentFromFactorials (hypergeomFactorialClosed N k m) 1)
        (momentFromFactorials (hypergeomFactorialClosed N k m) 2)
        (momentFromFactorials (hypergeomFactorialClosed N k m) 3)
        (momentFromFactorials (hypergeomFactorialClosed N k m) 4)
        (momentFromFactorials (hypergeomFactorialClosed N k m) 5) := by
  change cumulant5Polynomial (hypergeomRawMoment N k m 1)
    (hypergeomRawMoment N k m 2) (hypergeomRawMoment N k m 3)
    (hypergeomRawMoment N k m 4) (hypergeomRawMoment N k m 5) = _
  rw [hypergeom_raw_moment_closed_through_six N k m 1 hk hm (by omega),
    hypergeom_raw_moment_closed_through_six N k m 2 hk hm (by omega),
    hypergeom_raw_moment_closed_through_six N k m 3 hk hm (by omega),
    hypergeom_raw_moment_closed_through_six N k m 4 hk hm (by omega),
    hypergeom_raw_moment_closed_through_six N k m 5 hk hm (by omega)]

theorem hypergeom_cumulant6_factorial_complete (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomCumulant6 N k m =
      cumulant6Polynomial
        (momentFromFactorials (hypergeomFactorialClosed N k m) 1)
        (momentFromFactorials (hypergeomFactorialClosed N k m) 2)
        (momentFromFactorials (hypergeomFactorialClosed N k m) 3)
        (momentFromFactorials (hypergeomFactorialClosed N k m) 4)
        (momentFromFactorials (hypergeomFactorialClosed N k m) 5)
        (momentFromFactorials (hypergeomFactorialClosed N k m) 6) := by
  change cumulant6Polynomial (hypergeomRawMoment N k m 1)
    (hypergeomRawMoment N k m 2) (hypergeomRawMoment N k m 3)
    (hypergeomRawMoment N k m 4) (hypergeomRawMoment N k m 5)
    (hypergeomRawMoment N k m 6) = _
  rw [hypergeom_raw_moment_closed_through_six N k m 1 hk hm (by omega),
    hypergeom_raw_moment_closed_through_six N k m 2 hk hm (by omega),
    hypergeom_raw_moment_closed_through_six N k m 3 hk hm (by omega),
    hypergeom_raw_moment_closed_through_six N k m 4 hk hm (by omega),
    hypergeom_raw_moment_closed_through_six N k m 5 hk hm (by omega),
    hypergeom_raw_moment_closed_through_six N k m 6 hk hm (by omega)]

/-- The factorial-moment continuation in inverse population size. -/
def hypergeomRescaledFactorial (m q : ℕ) (s ε : ℝ) : ℝ :=
  (Nat.descFactorial m q : ℝ) *
    ∏ r ∈ Finset.range q, (((1 - s * ε) / 2 - (r : ℝ) * ε) /
      (1 - (r : ℝ) * ε))

theorem hypergeom_rescaled_factorial_at_zero (m q : ℕ) (s : ℝ) :
    hypergeomRescaledFactorial m q s 0 =
      (Nat.descFactorial m q : ℝ) / 2 ^ q := by
  simp [hypergeomRescaledFactorial, Finset.prod_const, div_eq_mul_inv]

/-- For a nonzero population the continuation is the actual factorial moment
at the population inverse, including zero factorials above the support. -/
theorem hypergeom_rescaled_factorial_actual (N k m q : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N)
    (s : ℝ) (hs : (N : ℝ) - 2 * (k : ℝ) = s) :
    hypergeomRescaledFactorial m q s (1 / (N : ℝ)) =
      hypergeomFactorialMoment N k m q := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hf (r : ℕ) :
      (((1 - s * (1 / (N : ℝ))) / 2 - (r : ℝ) * (1 / (N : ℝ))) /
        (1 - (r : ℝ) * (1 / (N : ℝ)))) =
      ((k : ℝ) - (r : ℝ)) / ((N : ℝ) - (r : ℝ)) := by
    have ha : (1 - s * (1 / (N : ℝ))) / 2 - (r : ℝ) * (1 / (N : ℝ)) =
        ((k : ℝ) - (r : ℝ)) / (N : ℝ) := by
      rw [← hs]
      field_simp [hn]
      ring
    have hb : 1 - (r : ℝ) * (1 / (N : ℝ)) =
        ((N : ℝ) - (r : ℝ)) / (N : ℝ) := by
      field_simp [hn]
    rw [ha, hb, div_div_div_cancel_right₀ hn]
  rw [hypergeomRescaledFactorial]
  simp_rw [hf]
  rw [Finset.prod_div_distrib, ← descFactorial_cast_product,
    ← descFactorial_cast_product]
  rw [hypergeom_factorial_moment_formula N k m q hk hm]
  split_ifs with hq
  · ring
  · have hz : Nat.descFactorial m q = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [hz]

def hypergeomRescaledMoment (m r : ℕ) (s ε : ℝ) : ℝ :=
  momentFromFactorials (fun q => hypergeomRescaledFactorial m q s ε) r

def hypergeomRescaledCumulant5 (m : ℕ) (s ε : ℝ) : ℝ :=
  cumulant5Polynomial (hypergeomRescaledMoment m 1 s ε)
    (hypergeomRescaledMoment m 2 s ε) (hypergeomRescaledMoment m 3 s ε)
    (hypergeomRescaledMoment m 4 s ε) (hypergeomRescaledMoment m 5 s ε)

def hypergeomRescaledCumulant6 (m : ℕ) (s ε : ℝ) : ℝ :=
  cumulant6Polynomial (hypergeomRescaledMoment m 1 s ε)
    (hypergeomRescaledMoment m 2 s ε) (hypergeomRescaledMoment m 3 s ε)
    (hypergeomRescaledMoment m 4 s ε) (hypergeomRescaledMoment m 5 s ε)
    (hypergeomRescaledMoment m 6 s ε)

theorem hypergeom_rescaled_cumulant5_actual (N k m : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N)
    (s : ℝ) (hs : (N : ℝ) - 2 * (k : ℝ) = s) :
    hypergeomRescaledCumulant5 m s (1 / (N : ℝ)) = hypergeomCumulant5 N k m := by
  have hq (q : ℕ) := hypergeom_rescaled_factorial_actual N k m q hN hk hm s hs
  simp_rw [hypergeomRescaledCumulant5, hypergeomRescaledMoment, hq]
  unfold hypergeomCumulant5 finiteCumulant5
  change _ = cumulant5Polynomial (hypergeomRawMoment N k m 1)
    (hypergeomRawMoment N k m 2) (hypergeomRawMoment N k m 3)
    (hypergeomRawMoment N k m 4) (hypergeomRawMoment N k m 5)
  rw [hypergeom_raw_moment_factorials_through_six N k m 1 (by omega),
    hypergeom_raw_moment_factorials_through_six N k m 2 (by omega),
    hypergeom_raw_moment_factorials_through_six N k m 3 (by omega),
    hypergeom_raw_moment_factorials_through_six N k m 4 (by omega),
    hypergeom_raw_moment_factorials_through_six N k m 5 (by omega)]

theorem hypergeom_rescaled_cumulant6_actual (N k m : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N)
    (s : ℝ) (hs : (N : ℝ) - 2 * (k : ℝ) = s) :
    hypergeomRescaledCumulant6 m s (1 / (N : ℝ)) = hypergeomCumulant6 N k m := by
  have hq (q : ℕ) := hypergeom_rescaled_factorial_actual N k m q hN hk hm s hs
  simp_rw [hypergeomRescaledCumulant6, hypergeomRescaledMoment, hq]
  unfold hypergeomCumulant6 finiteCumulant6
  change _ = cumulant6Polynomial (hypergeomRawMoment N k m 1)
    (hypergeomRawMoment N k m 2) (hypergeomRawMoment N k m 3)
    (hypergeomRawMoment N k m 4) (hypergeomRawMoment N k m 5)
    (hypergeomRawMoment N k m 6)
  rw [hypergeom_raw_moment_factorials_through_six N k m 1 (by omega),
    hypergeom_raw_moment_factorials_through_six N k m 2 (by omega),
    hypergeom_raw_moment_factorials_through_six N k m 3 (by omega),
    hypergeom_raw_moment_factorials_through_six N k m 4 (by omega),
    hypergeom_raw_moment_factorials_through_six N k m 5 (by omega),
    hypergeom_raw_moment_factorials_through_six N k m 6 (by omega)]

theorem hypergeom_rescaled_cumulant5_at_zero (m : ℕ) (s : ℝ) :
    hypergeomRescaledCumulant5 m s 0 = 0 := by
  unfold hypergeomRescaledCumulant5 hypergeomRescaledMoment
  simp only [momentFromFactorials, hypergeom_rescaled_factorial_at_zero,
    descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num [cumulant5Polynomial]
  ring

theorem hypergeom_rescaled_cumulant6_at_zero (m : ℕ) (s : ℝ) :
    hypergeomRescaledCumulant6 m s 0 = (m : ℝ) / 4 := by
  unfold hypergeomRescaledCumulant6 hypergeomRescaledMoment
  simp only [momentFromFactorials, hypergeom_rescaled_factorial_at_zero,
    descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num [cumulant6Polynomial]
  ring

theorem hypergeom_rescaled_factorial_continuousAt_zero (m q : ℕ) (s : ℝ) :
    ContinuousAt (hypergeomRescaledFactorial m q s) 0 := by
  unfold hypergeomRescaledFactorial
  fun_prop (disch := norm_num)

/-- The first inverse-population coefficient of every factorial moment. -/
theorem hypergeom_rescaled_factorial_hasDerivAt_zero (m q : ℕ) (s : ℝ) :
    HasDerivAt (hypergeomRescaledFactorial m q s)
      ((Nat.descFactorial m q : ℝ) / 2 ^ q *
        (-(q : ℝ) * s - (q : ℝ) * ((q : ℝ) - 1) / 2)) 0 := by
  let f (r : ℕ) (ε : ℝ) :=
    ((1 - s * ε) / 2 - (r : ℝ) * ε) / (1 - (r : ℝ) * ε)
  have hf (r : ℕ) : HasDerivAt (f r) (-(s + (r : ℝ)) / 2) 0 := by
    have ha := HasDerivAt.sub (HasDerivAt.div_const
      (HasDerivAt.sub (hasDerivAt_const (0 : ℝ) (1 : ℝ))
        (HasDerivAt.const_mul s (hasDerivAt_id (0 : ℝ)))) 2)
      (HasDerivAt.const_mul (r : ℝ) (hasDerivAt_id (0 : ℝ)))
    have hb := HasDerivAt.sub (hasDerivAt_const (0 : ℝ) (1 : ℝ))
      (HasDerivAt.const_mul (r : ℝ) (hasDerivAt_id (0 : ℝ)))
    convert! HasDerivAt.div ha hb (by norm_num) using 1 <;> (dsimp [f]; ring)
  have hval (r : ℕ) : (∏ i ∈ Finset.range r, f i 0) = 1 / 2 ^ r := by
    simp [f, Finset.prod_const]
  have hp (r : ℕ) :
      HasDerivAt (fun ε => ∏ i ∈ Finset.range r, f i ε)
        ((1 / 2 ^ r) * (-(r : ℝ) * s - (r : ℝ) * ((r : ℝ) - 1) / 2)) 0 := by
    induction r with
    | zero => simpa using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    | succ r ih =>
        simp only [Finset.prod_range_succ]
        convert! HasDerivAt.mul ih (hf r) using 1
        rw [hval]
        simp only [f, mul_zero, sub_zero, Nat.cast_add, Nat.cast_one, pow_succ]
        ring
  convert! (hp q).const_mul (Nat.descFactorial m q : ℝ) using 1
  all_goals first | rfl | ring

theorem hypergeom_rescaled_moment_continuousAt_zero (m r : ℕ) (s : ℝ) (hr : r ≤ 6) :
    ContinuousAt (hypergeomRescaledMoment m r s) 0 := by
  unfold hypergeomRescaledMoment
  interval_cases r <;> simp only [momentFromFactorials, hypergeomRescaledFactorial]
  all_goals fun_prop (disch := norm_num)

theorem hypergeom_rescaled_moment_hasDerivAt_zero (m r : ℕ) (s : ℝ) (hr : r ≤ 6) :
    HasDerivAt (hypergeomRescaledMoment m r s)
      (momentFromFactorials (fun q => (Nat.descFactorial m q : ℝ) / 2 ^ q *
        (-(q : ℝ) * s - (q : ℝ) * ((q : ℝ) - 1) / 2)) r) 0 := by
  have h1 := hypergeom_rescaled_factorial_hasDerivAt_zero m 1 s
  have h2 := hypergeom_rescaled_factorial_hasDerivAt_zero m 2 s
  have h3 := hypergeom_rescaled_factorial_hasDerivAt_zero m 3 s
  have h4 := hypergeom_rescaled_factorial_hasDerivAt_zero m 4 s
  have h5 := hypergeom_rescaled_factorial_hasDerivAt_zero m 5 s
  have h6 := hypergeom_rescaled_factorial_hasDerivAt_zero m 6 s
  interval_cases r
  · change HasDerivAt (fun ε => hypergeomRescaledFactorial m 0 s ε) _ 0
    exact hypergeom_rescaled_factorial_hasDerivAt_zero m 0 s
  · exact h1
  · exact HasDerivAt.add h2 h1
  · exact HasDerivAt.add (HasDerivAt.add h3 (h2.const_mul 3)) h1
  · exact HasDerivAt.add (HasDerivAt.add (HasDerivAt.add h4 (h3.const_mul 6)) (h2.const_mul 7)) h1
  · exact HasDerivAt.add (HasDerivAt.add (HasDerivAt.add (HasDerivAt.add h5
      (h4.const_mul 10)) (h3.const_mul 25)) (h2.const_mul 15)) h1
  · exact HasDerivAt.add (HasDerivAt.add (HasDerivAt.add (HasDerivAt.add
      (HasDerivAt.add h6 (h5.const_mul 15)) (h4.const_mul 65))
      (h3.const_mul 90)) (h2.const_mul 31)) h1

/-- The manuscript's leading fifth-cumulant coefficient is `-m*s/2`. -/
theorem hypergeom_rescaled_cumulant5_hasDerivAt_zero (m : ℕ) (s : ℝ) :
    HasDerivAt (hypergeomRescaledCumulant5 m s) (-(m : ℝ) * s / 2) 0 := by
  have h1 := hypergeom_rescaled_moment_hasDerivAt_zero m 1 s (by omega)
  have h2 := hypergeom_rescaled_moment_hasDerivAt_zero m 2 s (by omega)
  have h3 := hypergeom_rescaled_moment_hasDerivAt_zero m 3 s (by omega)
  have h4 := hypergeom_rescaled_moment_hasDerivAt_zero m 4 s (by omega)
  have h5 := hypergeom_rescaled_moment_hasDerivAt_zero m 5 s (by omega)
  have h := HasDerivAt.add (HasDerivAt.sub
    (HasDerivAt.add (HasDerivAt.add (HasDerivAt.sub
      (HasDerivAt.sub h5 ((HasDerivAt.mul h4 h1).const_mul 5))
      ((HasDerivAt.mul h3 h2).const_mul 10))
      ((HasDerivAt.mul h3 (h1.pow 2)).const_mul 20))
      ((HasDerivAt.mul (h2.pow 2) h1).const_mul 30))
      ((HasDerivAt.mul h2 (h1.pow 3)).const_mul 60)) ((h1.pow 5).const_mul 24)
  convert! h using 1
  · funext ε
    simp only [hypergeomRescaledCumulant5, cumulant5Polynomial,
      Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    ring
  · simp only [Pi.pow_apply, hypergeomRescaledMoment, momentFromFactorials,
      hypergeom_rescaled_factorial_at_zero, descFactorial_cast_product,
      Finset.prod_range_succ, Finset.prod_range_zero]
    norm_num
    ring

theorem hypergeom_rescaled_cumulant5_limit_zero (m : ℕ) (s : ℝ) :
    Tendsto (hypergeomRescaledCumulant5 m s) (𝓝 0) (𝓝 0) := by
  have h : ContinuousAt (hypergeomRescaledCumulant5 m s) 0 := by
    unfold hypergeomRescaledCumulant5 cumulant5Polynomial hypergeomRescaledMoment
    simp only [momentFromFactorials, hypergeomRescaledFactorial]
    fun_prop (disch := norm_num)
  simpa [hypergeom_rescaled_cumulant5_at_zero] using h.tendsto

/-- The first-order fifth-cumulant expansion, with a little-o remainder. -/
theorem hypergeom_rescaled_cumulant5_first_order (m : ℕ) (s : ℝ) :
    (fun ε => hypergeomRescaledCumulant5 m s ε + (m : ℝ) * s * ε / 2)
      =o[𝓝 0] (fun ε : ℝ => ε) := by
  have h := (hypergeom_rescaled_cumulant5_hasDerivAt_zero m s).isLittleO
  convert! h using 1
  all_goals
    funext ε
    simp only [hypergeom_rescaled_cumulant5_at_zero, sub_zero, smul_eq_mul]
    all_goals ring

theorem hypergeom_rescaled_cumulant6_limit_zero (m : ℕ) (s : ℝ) :
    Tendsto (hypergeomRescaledCumulant6 m s) (𝓝 0) (𝓝 ((m : ℝ) / 4)) := by
  have h : ContinuousAt (hypergeomRescaledCumulant6 m s) 0 := by
    unfold hypergeomRescaledCumulant6 cumulant6Polynomial hypergeomRescaledMoment
    simp only [momentFromFactorials, hypergeomRescaledFactorial]
    fun_prop (disch := norm_num)
  simpa [hypergeom_rescaled_cumulant6_at_zero] using h.tendsto

/-- The balanced limit along any sequence of legal population parameters. -/
theorem hypergeom_cumulant6_balanced_limit
    (Ns ks : ℕ → ℕ) (m : ℕ) (s : ℝ)
    (hN : ∀ n, 0 < Ns n) (hk : ∀ n, ks n ≤ Ns n) (hm : ∀ n, m ≤ Ns n)
    (hs : ∀ n, (Ns n : ℝ) - 2 * (ks n : ℝ) = s)
    (hlim : Tendsto (fun n => (Ns n : ℝ)) atTop atTop) :
    Tendsto (fun n => hypergeomCumulant6 (Ns n) (ks n) m) atTop (𝓝 ((m : ℝ) / 4)) := by
  have h := (hypergeom_rescaled_cumulant6_limit_zero m s).comp (hlim.const_div_atTop 1)
  simpa only [Function.comp_def,
    hypergeom_rescaled_cumulant6_actual _ _ _ (hN _) (hk _) (hm _) s (hs _)] using h

theorem hypergeom_cumulant5_balanced_limit
    (Ns ks : ℕ → ℕ) (m : ℕ) (s : ℝ)
    (hN : ∀ n, 0 < Ns n) (hk : ∀ n, ks n ≤ Ns n) (hm : ∀ n, m ≤ Ns n)
    (hs : ∀ n, (Ns n : ℝ) - 2 * (ks n : ℝ) = s)
    (hlim : Tendsto (fun n => (Ns n : ℝ)) atTop atTop) :
    Tendsto (fun n => hypergeomCumulant5 (Ns n) (ks n) m) atTop (𝓝 0) := by
  have h := (hypergeom_rescaled_cumulant5_limit_zero m s).comp (hlim.const_div_atTop 1)
  simpa only [Function.comp_def,
    hypergeom_rescaled_cumulant5_actual _ _ _ (hN _) (hk _) (hm _) s (hs _)] using h


/-- Analyticity supplies a quadratic remainder for the linear Taylor jet. -/
theorem analyticAt_linear_remainder_bigO {f : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f 0) (hd : HasDerivAt f a 0) :
    (fun ε => f ε - f 0 - a * ε) =O[𝓝 0] (fun ε : ℝ => ε ^ 2) := by
  obtain ⟨p, hp⟩ := hf
  have hcoeff : p.coeff 1 = a := hp.hasDerivAt.unique hd
  have hsum (ε : ℝ) : p.partialSum 2 ε = f 0 + a * ε := by
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add]
    rw [hp.coeff_zero, FormalMultilinearSeries.apply_eq_pow_smul_coeff, hcoeff]
    simp only [pow_one, smul_eq_mul]
    ring
  have h := hp.isBigO_sub_partialSum_pow 2
  simp only [zero_add, hsum, ← norm_pow, Asymptotics.isBigO_norm_right] at h
  convert! h using 1
  funext ε
  ring

theorem hypergeom_rescaled_cumulant5_analyticAt_zero (m : ℕ) (s : ℝ) :
    AnalyticAt ℝ (hypergeomRescaledCumulant5 m s) 0 := by
  unfold hypergeomRescaledCumulant5 cumulant5Polynomial hypergeomRescaledMoment
  simp only [momentFromFactorials, hypergeomRescaledFactorial]
  fun_prop (disch := norm_num)

theorem hypergeom_rescaled_cumulant6_analyticAt_zero (m : ℕ) (s : ℝ) :
    AnalyticAt ℝ (hypergeomRescaledCumulant6 m s) 0 := by
  unfold hypergeomRescaledCumulant6 cumulant6Polynomial hypergeomRescaledMoment
  simp only [momentFromFactorials, hypergeomRescaledFactorial]
  fun_prop (disch := norm_num)

/-- The full fifth-cumulant remainder from the manuscript. -/
theorem hypergeom_rescaled_cumulant5_remainder (m : ℕ) (s : ℝ) :
    (fun ε => hypergeomRescaledCumulant5 m s ε + (m : ℝ) * s * ε / 2)
      =O[𝓝 0] (fun ε : ℝ => ε ^ 2) := by
  have h := analyticAt_linear_remainder_bigO
    (hypergeom_rescaled_cumulant5_analyticAt_zero m s)
    (hypergeom_rescaled_cumulant5_hasDerivAt_zero m s)
  convert! h using 1
  funext ε
  rw [hypergeom_rescaled_cumulant5_at_zero]
  ring

/-- The sixth cumulant approaches its binomial value at order `1/N`. -/
theorem hypergeom_rescaled_cumulant6_remainder (m : ℕ) (s : ℝ) :
    (fun ε => hypergeomRescaledCumulant6 m s ε - (m : ℝ) / 4)
      =O[𝓝 0] (fun ε : ℝ => ε) := by
  have h := (hypergeom_rescaled_cumulant6_analyticAt_zero m s).differentiableAt.isBigO_sub
  simpa only [hypergeom_rescaled_cumulant6_at_zero, sub_zero] using h


/-- The actual fourth cumulant continued in inverse population size. -/
def hypergeomRescaledCumulant4 (m : ℕ) (s ε : ℝ) : ℝ :=
  let a := hypergeomRescaledMoment m 1 s ε
  let b := hypergeomRescaledMoment m 2 s ε
  let c := hypergeomRescaledMoment m 3 s ε
  let d := hypergeomRescaledMoment m 4 s ε
  d - 4 * c * a - 3 * b ^ 2 + 12 * b * a ^ 2 - 6 * a ^ 4

theorem hypergeom_rescaled_cumulant4_actual (N k m : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N)
    (s : ℝ) (hs : (N : ℝ) - 2 * (k : ℝ) = s) :
    hypergeomRescaledCumulant4 m s (1 / (N : ℝ)) = hypergeomCumulant4 N k m := by
  have hq (q : ℕ) := hypergeom_rescaled_factorial_actual N k m q hN hk hm s hs
  simp_rw [hypergeomRescaledCumulant4, hypergeomRescaledMoment, hq]
  rw [hypergeom_cumulant4_factorial_complete N k m hk hm]
  rfl

/-- The complete second-order fourth-cumulant jet. -/
def hypergeomCumulant4Taylor (m : ℕ) (s ε : ℝ) : ℝ :=
  -(m : ℝ) / 8 + (m : ℝ) * ((m : ℝ) - 1) / 2 * ε +
    (m : ℝ) * (-6 * (m : ℝ) ^ 2 + 19 * (m : ℝ) + 4 * s ^ 2 - 13) / 8 * ε ^ 2

/-- An explicit polynomial certificate for the third-order fourth-cumulant remainder. -/
def hypergeomCumulant4RemainderNumerator (m : ℕ) (s ε : ℝ) : ℝ :=
  let x := (m : ℝ);
  -x * (x - 1) * (-3 * x ^ 2 + 27 * x + 22 * s ^ 2 - 40) / 8 +
  (-3 * x * (2 * x ^ 3 - 12 * x ^ 2 * s ^ 2 - 34 * x ^ 2 -
    10 * x * s ^ 2 + 85 * x + s ^ 4 + 22 * s ^ 2 - 53) / 8) * ε +
  (x * (-18 * x ^ 3 * s ^ 2 - 48 * x ^ 2 * s ^ 2 - 102 * x ^ 2 +
    18 * x * s ^ 4 - 2 * x * s ^ 2 + 299 * x + 3 * s ^ 4 +
    68 * s ^ 2 - 197) / 8) * ε ^ 2 +
  (-3 * x * (-8 * x ^ 3 * s ^ 2 + 10 * x ^ 2 * s ^ 4 - 12 * x ^ 2 +
    7 * x * s ^ 4 + 38 * x + 8 * s ^ 2 - 26) / 8) * ε ^ 3 +
  (3 * x ^ 3 * s ^ 4 * (5 * x + 12) / 8) * ε ^ 4 -
  (9 * x ^ 4 * s ^ 4 / 4) * ε ^ 5


def hypergeomCumulant4RemainderFactor (m : ℕ) (s ε : ℝ) : ℝ :=
  hypergeomCumulant4RemainderNumerator m s ε /
    ((1 - ε) ^ 2 * (1 - 2 * ε) * (1 - 3 * ε))

/-- Exact algebraic remainder, verified by ring normalization after denominator clearing. -/
theorem hypergeom_rescaled_cumulant4_remainder_identity (m : ℕ) (s ε : ℝ)
    (h1 : 1 - ε ≠ 0) (h2 : 1 - 2 * ε ≠ 0) (h3 : 1 - 3 * ε ≠ 0) :
    hypergeomRescaledCumulant4 m s ε - hypergeomCumulant4Taylor m s ε =
      hypergeomCumulant4RemainderFactor m s ε * ε ^ 3 := by
  unfold hypergeomRescaledCumulant4 hypergeomRescaledMoment
    hypergeomCumulant4Taylor hypergeomCumulant4RemainderFactor
    hypergeomCumulant4RemainderNumerator
  simp only [momentFromFactorials, hypergeomRescaledFactorial,
    descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  field_simp [h1, h2, h3] <;> ring

/-- The fourth-cumulant expansion has its asserted cubic remainder. -/
theorem hypergeom_rescaled_cumulant4_remainder (m : ℕ) (s : ℝ) :
    (fun ε => hypergeomRescaledCumulant4 m s ε - hypergeomCumulant4Taylor m s ε)
      =O[𝓝 0] (fun ε : ℝ => ε ^ 3) := by
  have hc : ContinuousAt (hypergeomCumulant4RemainderFactor m s) 0 := by
    unfold hypergeomCumulant4RemainderFactor hypergeomCumulant4RemainderNumerator
    fun_prop (disch := norm_num)
  have h := hc.isBigO.mul (Asymptotics.isBigO_refl (fun ε : ℝ => ε ^ 3) (𝓝 0))
  have h1 : ∀ᶠ ε : ℝ in 𝓝 0, 1 - ε ≠ 0 := by
    exact (continuousAt_const.sub continuousAt_id).eventually_ne (by norm_num)
  have h2 : ∀ᶠ ε : ℝ in 𝓝 0, 1 - 2 * ε ≠ 0 := by
    exact (continuousAt_const.sub (continuousAt_id.const_mul 2)).eventually_ne (by norm_num)
  have h3 : ∀ᶠ ε : ℝ in 𝓝 0, 1 - 3 * ε ≠ 0 := by
    exact (continuousAt_const.sub (continuousAt_id.const_mul 3)).eventually_ne (by norm_num)
  simp only [one_mul] at h
  refine h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [h1, h2, h3] with ε h1 h2 h3
  exact (hypergeom_rescaled_cumulant4_remainder_identity m s ε h1 h2 h3).symm


/-- Fifth-cumulant expansion for the actual sequence of hypergeometric laws. -/
theorem hypergeom_cumulant5_balanced_expansion
    (Ns ks : ℕ → ℕ) (m : ℕ) (s : ℝ)
    (hN : ∀ n, 0 < Ns n) (hk : ∀ n, ks n ≤ Ns n) (hm : ∀ n, m ≤ Ns n)
    (hs : ∀ n, (Ns n : ℝ) - 2 * (ks n : ℝ) = s)
    (hlim : Tendsto (fun n => (Ns n : ℝ)) atTop atTop) :
    (fun n => hypergeomCumulant5 (Ns n) (ks n) m +
      (m : ℝ) * s * (1 / (Ns n : ℝ)) / 2)
      =O[atTop] (fun n => (1 / (Ns n : ℝ)) ^ 2) := by
  have h := (hypergeom_rescaled_cumulant5_remainder m s).comp_tendsto
    (hlim.const_div_atTop 1)
  simpa only [Function.comp_def,
    hypergeom_rescaled_cumulant5_actual _ _ _ (hN _) (hk _) (hm _) s (hs _)] using h

/-- Sixth-cumulant expansion for the actual sequence of hypergeometric laws. -/
theorem hypergeom_cumulant6_balanced_expansion
    (Ns ks : ℕ → ℕ) (m : ℕ) (s : ℝ)
    (hN : ∀ n, 0 < Ns n) (hk : ∀ n, ks n ≤ Ns n) (hm : ∀ n, m ≤ Ns n)
    (hs : ∀ n, (Ns n : ℝ) - 2 * (ks n : ℝ) = s)
    (hlim : Tendsto (fun n => (Ns n : ℝ)) atTop atTop) :
    (fun n => hypergeomCumulant6 (Ns n) (ks n) m - (m : ℝ) / 4)
      =O[atTop] (fun n => 1 / (Ns n : ℝ)) := by
  have h := (hypergeom_rescaled_cumulant6_remainder m s).comp_tendsto
    (hlim.const_div_atTop 1)
  simpa only [Function.comp_def,
    hypergeom_rescaled_cumulant6_actual _ _ _ (hN _) (hk _) (hm _) s (hs _)] using h

/-- Second-order fourth-cumulant expansion for the actual hypergeometric laws. -/
theorem hypergeom_cumulant4_balanced_expansion
    (Ns ks : ℕ → ℕ) (m : ℕ) (s : ℝ)
    (hN : ∀ n, 0 < Ns n) (hk : ∀ n, ks n ≤ Ns n) (hm : ∀ n, m ≤ Ns n)
    (hs : ∀ n, (Ns n : ℝ) - 2 * (ks n : ℝ) = s)
    (hlim : Tendsto (fun n => (Ns n : ℝ)) atTop atTop) :
    (fun n => hypergeomCumulant4 (Ns n) (ks n) m -
      hypergeomCumulant4Taylor m s (1 / (Ns n : ℝ)))
      =O[atTop] (fun n => (1 / (Ns n : ℝ)) ^ 3) := by
  have h := (hypergeom_rescaled_cumulant4_remainder m s).comp_tendsto
    (hlim.const_div_atTop 1)
  simpa only [Function.comp_def,
    hypergeom_rescaled_cumulant4_actual _ _ _ (hN _) (hk _) (hm _) s (hs _)] using h

end
end ExactHoeffding
