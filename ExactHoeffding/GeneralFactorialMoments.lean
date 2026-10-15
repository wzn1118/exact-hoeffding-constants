import ExactHoeffding.Normalization
import Mathlib.Data.Nat.Choose.Basic

/-!
# All-degree factorial moments of the hypergeometric count

The unnormalized identity is proved over `ℕ` by a factorial/binomial shift
and induction on the degree. The normalized expectation follows by exact
binomial identities, with the degree-above-population case totalized to zero.
-/

namespace ExactHoeffding

private lemma hypergeomCount_descFactorial_shift (k h m q : ℕ) :
    (∑ i ∈ Finset.range (m + 2),
      Nat.descFactorial i (q + 1) *
        (Nat.choose (k + 1) i * Nat.choose h (m + 1 - i))) =
      (k + 1) *
        ∑ i ∈ Finset.range (m + 1),
          Nat.descFactorial i q *
            (Nat.choose k i * Nat.choose h (m - i)) := by
  rw [show m + 2 = (m + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.zero_descFactorial_succ, zero_mul, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hsub : m + 1 - (i + 1) = m - i := by omega
  rw [hsub]
  have hdesc : Nat.descFactorial (i + 1) (q + 1) =
      (i + 1) * Nat.descFactorial i q := by
    exact Nat.succ_descFactorial_succ i q
  have hchoose : (i + 1) * Nat.choose (k + 1) (i + 1) =
      (k + 1) * Nat.choose k i := by
    calc
      _ = Nat.choose (k + 1) (i + 1) * (i + 1) := by ac_rfl
      _ = (k + 1) * Nat.choose k i :=
        (Nat.add_one_mul_choose_eq k i).symm
  calc
    Nat.descFactorial (i + 1) (q + 1) *
        (Nat.choose (k + 1) (i + 1) * Nat.choose h (m - i)) =
      ((i + 1) * Nat.choose (k + 1) (i + 1)) *
        (Nat.descFactorial i q * Nat.choose h (m - i)) := by
          rw [hdesc]
          ac_rfl
    _ = ((k + 1) * Nat.choose k i) *
        (Nat.descFactorial i q * Nat.choose h (m - i)) := by
          rw [hchoose]
    _ = (k + 1) *
        (Nat.descFactorial i q *
          (Nat.choose k i * Nat.choose h (m - i))) := by ac_rfl

/-- The all-degree unnormalized factorial-moment identity. For `q > m`,
the finite sum is zero; the guard prevents truncated natural subtraction on
the binomial-coefficient side from producing a spurious term. -/
theorem hypergeomCount_descFactorial_moment (N k m q : ℕ) (hk : k ≤ N) :
    (∑ i ∈ Finset.range (m + 1),
      Nat.descFactorial i q * hypergeomCount N k m i) =
      if q ≤ m then
        Nat.descFactorial k q * Nat.choose (N - q) (m - q)
      else 0 := by
  induction q generalizing N k m with
  | zero =>
      simpa [Nat.descFactorial_zero] using hypergeomCount_total N k m hk
  | succ q ih =>
      by_cases hqm : q + 1 ≤ m
      · by_cases hk0 : k = 0
        · subst k
          have hsum :
              (∑ i ∈ Finset.range (m + 1),
                Nat.descFactorial i (q + 1) * hypergeomCount N 0 m i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            by_cases hi0 : i = 0
            · subst i
              simp [Nat.zero_descFactorial_succ]
            · have hchoose : Nat.choose 0 i = 0 :=
                Nat.choose_eq_zero_of_lt (by omega)
              simp [hypergeomCount, hchoose]
          rw [if_pos hqm, hsum]
          simp [Nat.zero_descFactorial_succ]
        · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
          have hmpos : 0 < m := by omega
          have hkprev : k - 1 ≤ N - 1 := by omega
          have hqprev : q ≤ m - 1 := by omega
          have hlen₂ : (m - 1) + 2 = m + 1 := by omega
          have hlen₁ : (m - 1) + 1 = m := by omega
          have hklen : (k - 1) + 1 = k := by omega
          have hpop : (N - 1) - (k - 1) = N - k := by omega
          have hrec :
              (∑ i ∈ Finset.range (m + 1),
                Nat.descFactorial i (q + 1) * hypergeomCount N k m i) =
                k * (∑ i ∈ Finset.range m,
                  Nat.descFactorial i q *
                    hypergeomCount (N - 1) (k - 1) (m - 1) i) := by
            simpa [hypergeomCount, hlen₂, hlen₁, hklen, hpop] using
              (hypergeomCount_descFactorial_shift (k - 1) (N - k) (m - 1) q)
          have hIH := ih (N - 1) (k - 1) (m - 1) hkprev
          rw [if_pos hqprev] at hIH
          have hdesc : Nat.descFactorial k (q + 1) =
              k * Nat.descFactorial (k - 1) q := by
            simpa [hklen] using Nat.succ_descFactorial_succ (k - 1) q
          have hNsub : (N - 1) - q = N - (q + 1) := by omega
          have hmsub : (m - 1) - q = m - (q + 1) := by omega
          rw [if_pos hqm]
          calc
            _ = k * (∑ i ∈ Finset.range m,
                Nat.descFactorial i q *
                  hypergeomCount (N - 1) (k - 1) (m - 1) i) := hrec
            _ = k * (Nat.descFactorial (k - 1) q *
                Nat.choose ((N - 1) - q) ((m - 1) - q)) := by
                  have hIH' := hIH
                  rw [hlen₁] at hIH'
                  rw [hIH']
            _ = Nat.descFactorial k (q + 1) *
                Nat.choose (N - (q + 1)) (m - (q + 1)) := by
                  rw [hNsub, hmsub, hdesc]
                  ring
      · have hsum :
            (∑ i ∈ Finset.range (m + 1),
              Nat.descFactorial i (q + 1) * hypergeomCount N k m i) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have him : i ≤ m := by
            exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hiq : i < q + 1 := by omega
          rw [Nat.descFactorial_eq_zero_iff_lt.mpr hiq]
          simp
        simpa [hqm] using hsum

private lemma hypergeom_descFactorial_mass_sum_as_count
    (N k m q : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
      (Nat.descFactorial i q : ℝ) * hypergeomMass N k m i) =
      (∑ i ∈ Finset.range (m + 1),
        ((Nat.descFactorial i q * hypergeomCount N k m i : ℕ) : ℝ)) /
        (Nat.choose N m : ℝ) := by
  simp only [hypergeomMass]
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Nat.cast_mul, mul_assoc]

/-- The normalized all-degree factorial moment. For valid population
parameters, `E[(H)_q] = (m)_q (k)_q / (N)_q` through degree `N`, and is
zero above degree `N` (including the `N = 0` case). -/
theorem hypergeom_descFactorial_expectation (N k m q : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    (∑ i ∈ Finset.range (m + 1),
      (Nat.descFactorial i q : ℝ) * hypergeomMass N k m i) =
      if q ≤ N then
        ((Nat.descFactorial m q : ℝ) * (Nat.descFactorial k q : ℝ)) /
          (Nat.descFactorial N q : ℝ)
      else 0 := by
  by_cases hqm : q ≤ m
  · have hqN : q ≤ N := hqm.trans hm
    have hchooseN : (Nat.choose N m : ℝ) ≠ 0 := by
      exact_mod_cast Nat.choose_ne_zero hm
    have hdescN : (Nat.descFactorial N q : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hqN))
    have hchoose := Nat.choose_mul (n := N) (k := m) (s := q) hqm
    have hchooseR :
        (Nat.choose N m : ℝ) * (Nat.choose m q : ℝ) =
          (Nat.choose N q : ℝ) *
            (Nat.choose (N - q) (m - q) : ℝ) := by
      exact_mod_cast hchoose
    have hmfact : (Nat.descFactorial m q : ℝ) =
        (Nat.factorial q : ℝ) * (Nat.choose m q : ℝ) := by
      exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose m q
    have hNfact : (Nat.descFactorial N q : ℝ) =
        (Nat.factorial q : ℝ) * (Nat.choose N q : ℝ) := by
      exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose N q
    have hcross :
        (Nat.choose (N - q) (m - q) : ℝ) *
            (Nat.descFactorial N q : ℝ) =
          (Nat.descFactorial m q : ℝ) * (Nat.choose N m : ℝ) := by
      calc
        _ = ((Nat.factorial q : ℝ) * (Nat.choose N q : ℝ)) *
              (Nat.choose (N - q) (m - q) : ℝ) := by
                rw [hNfact]
                ring
        _ = (Nat.factorial q : ℝ) *
              ((Nat.choose N q : ℝ) *
                (Nat.choose (N - q) (m - q) : ℝ)) := by ring
        _ = (Nat.factorial q : ℝ) *
              ((Nat.choose N m : ℝ) * (Nat.choose m q : ℝ)) := by
                rw [hchooseR]
        _ = _ := by rw [hmfact]; ring
    have hraw := hypergeomCount_descFactorial_moment N k m q hk
    rw [if_pos hqm] at hraw
    have hrawR :
        (∑ i ∈ Finset.range (m + 1),
          ((Nat.descFactorial i q * hypergeomCount N k m i : ℕ) : ℝ)) =
          ((Nat.descFactorial k q * Nat.choose (N - q) (m - q) : ℕ) : ℝ) := by
      exact_mod_cast hraw
    rw [hypergeom_descFactorial_mass_sum_as_count, hrawR]
    simp only [Nat.cast_mul, if_pos hqN]
    calc
      ((Nat.descFactorial k q : ℝ) *
          (Nat.choose (N - q) (m - q) : ℝ)) /
          (Nat.choose N m : ℝ) =
        (Nat.descFactorial k q : ℝ) *
          ((Nat.choose (N - q) (m - q) : ℝ) /
            (Nat.choose N m : ℝ)) := by rw [mul_div_assoc]
      _ = (Nat.descFactorial k q : ℝ) *
          ((Nat.descFactorial m q : ℝ) /
            (Nat.descFactorial N q : ℝ)) := by
              field_simp [hchooseN, hdescN]
              nlinarith [hcross]
      _ = ((Nat.descFactorial m q : ℝ) *
          (Nat.descFactorial k q : ℝ)) /
          (Nat.descFactorial N q : ℝ) := by ring
  · have hraw := hypergeomCount_descFactorial_moment N k m q hk
    rw [if_neg hqm] at hraw
    have hrawR :
        (∑ i ∈ Finset.range (m + 1),
          ((Nat.descFactorial i q * hypergeomCount N k m i : ℕ) : ℝ)) = 0 := by
      exact_mod_cast hraw
    rw [hypergeom_descFactorial_mass_sum_as_count, hrawR]
    by_cases hqN : q ≤ N
    · have hzero : (Nat.descFactorial m q : ℝ) = 0 := by
        exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.mpr (by omega))
      simp [hqN, hzero]
    · simp [hqN]

end ExactHoeffding
