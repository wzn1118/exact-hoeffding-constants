import ExactHoeffding.Support
import ExactHoeffding.FactorialMoments
import ExactHoeffding.OrdinaryMoments

/-!
# Complete ordinary hypergeometric moments

This file closes the finite, un-tilted first and second moments without
changing the existing `hypergeomMass` definition.  Every sum is over the
effective finite range `Finset.range (m + 1)`.  The totalized PMF from
`Support.lean` is available for statements over all natural indices, while
the moment identities below use the original finite-sum API.

For `N = 0` and `N = 1`, real division by zero is Lean's totalized real
division, so the displayed quotient is zero.  The proofs still identify the
actual degenerate finite laws separately rather than treating a zero
denominator as a probabilistic normalization argument.
-/

namespace ExactHoeffding

private lemma hypergeom_mean_zero_marks (N m : ℕ) (hm : m ≤ N) :
    (∑ i ∈ Finset.range (m + 1),
      (i : ℝ) * hypergeomMass N 0 m i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [hypergeomMass_zero_marks N m i hm him]
  by_cases hzero : i = 0 <;> simp [hzero]

/-- The ordinary mean, including the totalized `N = 0` quotient case. -/
theorem hypergeom_mean_complete (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) :
    (∑ i ∈ Finset.range (m + 1),
      (i : ℝ) * hypergeomMass N k m i) =
      (m : ℝ) * (k : ℝ) / (N : ℝ) := by
  by_cases hN : N = 0
  · have hk0 : k = 0 := by omega
    have hm0 : m = 0 := by omega
    subst N
    subst k
    subst m
    simp [hypergeomMass, hypergeomCount]
  · by_cases hm0 : m = 0
    · subst m
      simp [hypergeomMass_no_draws]
    · by_cases hk0 : k = 0
      · subst k
        rw [hypergeom_mean_zero_marks N m hm]
        norm_num
      · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
        obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        have hdecomp : k' + (N - (k' + 1)) + 1 = N := by omega
        have hcond : m' + 1 ≤ k' + (N - (k' + 1)) + 1 := by omega
        simpa [hdecomp] using
          (hypergeom_mean_succ k' (N - (k' + 1)) m' hcond)

private lemma hypergeomCount_factorial_second_zero_of_k_le_one
    (N k m : ℕ) (hk : k ≤ 1) :
    (∑ i ∈ Finset.range (m + 1),
      i * (i - 1) * hypergeomCount N k m i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hi1 : i ≤ 1
  · have hcases : i = 0 ∨ i = 1 := by omega
    rcases hcases with rfl | rfl <;> simp
  · have hik : k < i := by omega
    have hchoose : Nat.choose k i = 0 := Nat.choose_eq_zero_of_lt hik
    simp [hypergeomCount, hchoose]

private lemma hypergeomCount_factorial_second_zero_of_m_le_one
    (N k m : ℕ) (hm : m ≤ 1) :
    (∑ i ∈ Finset.range (m + 1),
      i * (i - 1) * hypergeomCount N k m i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hi1 : i ≤ 1 := him.trans hm
  have hcases : i = 0 ∨ i = 1 := by omega
  rcases hcases with rfl | rfl <;> simp

private lemma choose_two_step (N m : ℕ) (hN : 2 ≤ N)
    (hm : 2 ≤ m) (hmN : m ≤ N) :
    N * (N - 1) * Nat.choose (N - 2) (m - 2) =
      Nat.choose N m * m * (m - 1) := by
  have h₁ := Nat.add_one_mul_choose_eq (N - 2) (m - 2)
  have h₂ := Nat.add_one_mul_choose_eq (N - 1) (m - 1)
  have hN₁ : N - 2 + 1 = N - 1 := by omega
  have hm₁ : m - 2 + 1 = m - 1 := by omega
  have hN₂ : N - 1 + 1 = N := by omega
  have hm₂ : m - 1 + 1 = m := by omega
  have h₁' : (N - 1) * Nat.choose (N - 2) (m - 2) =
      Nat.choose (N - 1) (m - 1) * (m - 1) := by
    simpa [hN₁, hm₁] using h₁
  have h₂' : N * Nat.choose (N - 1) (m - 1) =
      Nat.choose N m * m := by
    simpa [hN₂, hm₂] using h₂
  calc
    N * (N - 1) * Nat.choose (N - 2) (m - 2) =
        N * ((N - 1) * Nat.choose (N - 2) (m - 2)) := by ring
    _ = N * (Nat.choose (N - 1) (m - 1) * (m - 1)) := by rw [h₁']
    _ = (N * Nat.choose (N - 1) (m - 1)) * (m - 1) := by ring
    _ = (Nat.choose N m * m) * (m - 1) := by rw [h₂']
    _ = Nat.choose N m * m * (m - 1) := by ring

private lemma hypergeomCount_factorial_second_core
    (N k m : ℕ) (hN : 2 ≤ N) (hk : 2 ≤ k) (hm : 2 ≤ m)
    (hkN : k ≤ N) (hmN : m ≤ N) :
    (∑ i ∈ Finset.range (m + 1),
      i * (i - 1) * hypergeomCount N k m i) =
      k * (k - 1) * Nat.choose (N - 2) (m - 2) := by
  have hraw := hypergeomCount_second_factorial_succ
    (k - 2) (N - k) (m - 2)
  have hk2 : k - 2 + 2 = k := by omega
  have hk1 : k - 2 + 1 = k - 1 := by omega
  have hkh : k - 2 + (N - k) = N - 2 := by omega
  have hm2 : m - 2 + 2 = m := by omega
  have hlen : m - 2 + 3 = m + 1 := by omega
  simpa [hypergeomCount, hk2, hk1, hkh, hm2, hlen] using hraw

private lemma hypergeom_factorial_sum_as_count (N k m : ℕ) (hm : m ≤ N) :
    (∑ i ∈ Finset.range (m + 1),
      ((i * (i - 1) : ℕ) : ℝ) * hypergeomMass N k m i) =
      (∑ i ∈ Finset.range (m + 1),
        ((i * (i - 1) * hypergeomCount N k m i : ℕ) : ℝ)) /
        (Nat.choose N m : ℝ) := by
  simp only [hypergeomMass]
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Nat.cast_mul, mul_assoc]

/-- Exact normalized second factorial moment for every valid finite law. -/
theorem hypergeom_factorial_second_complete (N k m : ℕ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    (∑ i ∈ Finset.range (m + 1),
      ((i * (i - 1) : ℕ) : ℝ) * hypergeomMass N k m i) =
      ((m : ℝ) * ((m : ℝ) - 1) * (k : ℝ) * ((k : ℝ) - 1)) /
        ((N : ℝ) * ((N : ℝ) - 1)) := by
  have hden : (Nat.choose N m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hm
  by_cases hsmall : k ≤ 1 ∨ m ≤ 1
  · have hzero :
        (∑ i ∈ Finset.range (m + 1),
          (i * (i - 1) * hypergeomCount N k m i : ℕ)) = 0 := by
      by_cases hk1 : k ≤ 1
      · exact hypergeomCount_factorial_second_zero_of_k_le_one N k m hk1
      · exact hypergeomCount_factorial_second_zero_of_m_le_one N k m
          (hsmall.resolve_left hk1)
    have hzeroR :
        (∑ i ∈ Finset.range (m + 1),
          ((i * (i - 1) * hypergeomCount N k m i : ℕ) : ℝ)) = 0 := by
      exact_mod_cast hzero
    rw [hypergeom_factorial_sum_as_count N k m hm, hzeroR]
    simp only [Nat.cast_zero, zero_div]
    rcases hsmall with hk1 | hm1
    · have hkc : k = 0 ∨ k = 1 := by omega
      rcases hkc with rfl | rfl <;> norm_num
    · have hmc : m = 0 ∨ m = 1 := by omega
      rcases hmc with rfl | rfl <;> norm_num
  · have hk2 : 2 ≤ k := by omega
    have hm2 : 2 ≤ m := by omega
    have hcount := hypergeomCount_factorial_second_core N k m hN hk2 hm2 hk hm
    rw [hypergeom_factorial_sum_as_count N k m hm]
    have hchoose :
        N * (N - 1) * Nat.choose (N - 2) (m - 2) =
          Nat.choose N m * m * (m - 1) :=
      choose_two_step N m hN hm2 hm
    have hchooseR :
        (N : ℝ) * ((N : ℝ) - 1) * (Nat.choose (N - 2) (m - 2) : ℝ) =
          (Nat.choose N m : ℝ) * (m : ℝ) * ((m : ℝ) - 1) := by
      have hchooseR0 :
          ((N * (N - 1) * Nat.choose (N - 2) (m - 2) : ℕ) : ℝ) =
            ((Nat.choose N m * m * (m - 1) : ℕ) : ℝ) := by
        exact_mod_cast hchoose
      have hNsub : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hmsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      simpa [Nat.cast_mul, hNsub, hmsub] using hchooseR0
    have hcountR :
        (∑ i ∈ Finset.range (m + 1),
          ((i * (i - 1) * hypergeomCount N k m i : ℕ) : ℝ)) =
          ((k * (k - 1) * Nat.choose (N - 2) (m - 2) : ℕ) : ℝ) := by
      exact_mod_cast hcount
    rw [hcountR]
    have hN0 : (N : ℝ) ≠ 0 := by
      exact_mod_cast (show N ≠ 0 by omega)
    have hN1 : (N : ℝ) - 1 ≠ 0 := by
      have hNgt : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
      linarith
    have hkSub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hfactorR :
        ((k * (k - 1) * Nat.choose (N - 2) (m - 2) : ℕ) : ℝ) =
          (k : ℝ) * ((k : ℝ) - 1) *
            (Nat.choose (N - 2) (m - 2) : ℝ) := by
      simp [Nat.cast_mul, hkSub]
    rw [hfactorR]
    field_simp [hden, hN0, hN1]
    nlinarith [hchooseR]

private lemma factorial_cast_identity (i : ℕ) :
    (i : ℝ) ^ 2 = ((i * (i - 1) : ℕ) : ℝ) + (i : ℝ) := by
  by_cases hi : i = 0
  · subst i
    norm_num
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    simp [Nat.succ_sub_one]
    ring

/-- Exact normalized raw second moment. -/
theorem hypergeom_raw_second_complete (N k m : ℕ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hm : m ≤ N) :
    (∑ i ∈ Finset.range (m + 1),
      (i : ℝ) ^ 2 * hypergeomMass N k m i) =
      (((m : ℝ) * ((m : ℝ) - 1) * (k : ℝ) * ((k : ℝ) - 1)) /
        ((N : ℝ) * ((N : ℝ) - 1))) +
      ((m : ℝ) * (k : ℝ) / (N : ℝ)) := by
  have hfac := hypergeom_factorial_second_complete N k m hN hk hm
  have hmean := hypergeom_mean_complete N k m hk hm
  calc
    (∑ i ∈ Finset.range (m + 1),
        (i : ℝ) ^ 2 * hypergeomMass N k m i) =
      ∑ i ∈ Finset.range (m + 1),
        (((i * (i - 1) : ℕ) : ℝ) + (i : ℝ)) *
          hypergeomMass N k m i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [factorial_cast_identity]
    _ = (∑ i ∈ Finset.range (m + 1),
          ((i * (i - 1) : ℕ) : ℝ) * hypergeomMass N k m i) +
        ∑ i ∈ Finset.range (m + 1),
          (i : ℝ) * hypergeomMass N k m i := by
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib]
    _ = (((m : ℝ) * ((m : ℝ) - 1) * (k : ℝ) * ((k : ℝ) - 1)) /
          ((N : ℝ) * ((N : ℝ) - 1))) +
        ((m : ℝ) * (k : ℝ) / (N : ℝ)) := by
          rw [hfac, hmean]

private lemma centered_sum_expansion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (μ : ℝ) :
    (∑ i ∈ s, (x i - μ) ^ 2 * w i) =
      (∑ i ∈ s, x i ^ 2 * w i) -
        2 * μ * (∑ i ∈ s, x i * w i) +
        μ ^ 2 * (∑ i ∈ s, w i) := by
  calc
    (∑ i ∈ s, (x i - μ) ^ 2 * w i) =
        ∑ i ∈ s, (x i ^ 2 * w i - 2 * μ * (x i * w i) + μ ^ 2 * w i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i ∈ s, x i ^ 2 * w i) -
          (∑ i ∈ s, 2 * μ * (x i * w i)) +
          ∑ i ∈ s, μ ^ 2 * w i := by
          rw [show (∑ i ∈ s,
              (x i ^ 2 * w i - 2 * μ * (x i * w i) + μ ^ 2 * w i)) =
            (∑ i ∈ s, (x i ^ 2 * w i - 2 * μ * (x i * w i))) +
              ∑ i ∈ s, μ ^ 2 * w i by rw [Finset.sum_add_distrib]]
          rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ s, x i ^ 2 * w i) -
          2 * μ * (∑ i ∈ s, x i * w i) +
          μ ^ 2 * (∑ i ∈ s, w i) := by
          have hfirst :
              (∑ i ∈ s, 2 * μ * (x i * w i)) =
                2 * μ * (∑ i ∈ s, x i * w i) := by
            rw [← Finset.mul_sum]
          have hsecond :
              (∑ i ∈ s, μ ^ 2 * w i) =
                μ ^ 2 * (∑ i ∈ s, w i) := by
            rw [← Finset.mul_sum]
          rw [hfirst, hsecond]

/-- The un-tilted variance, with Lean's total real division at `N = 0, 1`.
The two small-population branches are proved from their actual finite
degenerate laws; the quotient notation is not used as a normalization
argument in those branches. -/
theorem hypergeom_variance_complete (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) :
    (∑ i ∈ Finset.range (m + 1),
      ((i : ℝ) - (m : ℝ) * (k : ℝ) / (N : ℝ)) ^ 2 *
        hypergeomMass N k m i) =
      (m : ℝ) * (k : ℝ) * ((N - k : ℕ) : ℝ) * ((N - m : ℕ) : ℝ) /
        ((N : ℝ) ^ 2 * ((N : ℝ) - 1)) := by
  by_cases hN0 : N = 0
  · have hk0 : k = 0 := by omega
    have hm0 : m = 0 := by omega
    subst N
    subst k
    subst m
    simp [hypergeomMass, hypergeomCount]
  · by_cases hNbig : 2 ≤ N
    · have hfac := hypergeom_factorial_second_complete N k m hNbig hk hm
      have hraw := hypergeom_raw_second_complete N k m hNbig hk hm
      have hmean := hypergeom_mean_complete N k m hk hm
      have htotal := hypergeomMass_total N k m hk hm
      have hcenter := centered_sum_expansion
        (Finset.range (m + 1)) (hypergeomMass N k m)
        (fun i => (i : ℝ)) ((m : ℝ) * (k : ℝ) / (N : ℝ))
      rw [hcenter, hraw, hmean, htotal]
      have hNreal : (N : ℝ) ≠ 0 := by
        exact_mod_cast (show N ≠ 0 by omega)
      have hNsub1 : (N : ℝ) - 1 ≠ 0 := by
        have hgt : (1 : ℝ) < (N : ℝ) := by
          exact_mod_cast (show 1 < N by omega)
        linarith
      have hNk : ((N - k : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) := by
        rw [Nat.cast_sub hk]
      have hNm : ((N - m : ℕ) : ℝ) = (N : ℝ) - (m : ℝ) := by
        rw [Nat.cast_sub hm]
      rw [hNk, hNm]
      field_simp [hNreal, hNsub1]
      ring
    · have hN1 : N = 1 := by omega
      subst N
      have hk_cases : k = 0 ∨ k = 1 := by omega
      have hm_cases : m = 0 ∨ m = 1 := by omega
      rcases hk_cases with rfl | rfl
      · rcases hm_cases with rfl | rfl
        · simp [hypergeomMass, hypergeomCount]
        · have hsum :
              (∑ i ∈ Finset.range 2,
                ((i : ℝ) - (1 : ℝ) * 0 / 1) ^ 2 *
                  hypergeomMass 1 0 1 i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have him : i ≤ 1 := by
              exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
            rw [hypergeomMass_zero_marks 1 1 i le_rfl him]
            by_cases hzero : i = 0 <;> simp [hzero]
          simpa using hsum
      · rcases hm_cases with rfl | rfl
        · simp [hypergeomMass_no_draws]
        · have hsum :
              (∑ i ∈ Finset.range 2,
                ((i : ℝ) - (1 : ℝ) * 1 / 1) ^ 2 *
                  hypergeomMass 1 1 1 i) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have him : i ≤ 1 := by
              exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
            rw [hypergeomMass_full_draws 1 1 i le_rfl him]
            by_cases hone : i = 1 <;> simp [hone]
          simpa using hsum

end ExactHoeffding
