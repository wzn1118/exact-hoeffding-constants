import ExactHoeffding.Support

/-!
# Transposition symmetry of the hypergeometric law

The old `hypergeomMass` is only used on its finite draw range.  The
totalized `hypergeomPMFValue` makes the transposition identity pointwise on
all natural indices, while the finite MGF is compared after extending both
finite sums to `Finset.range (N + 1)`.
-/

namespace ExactHoeffding

/-- On the common valid index range, swapping the marked and sampled counts
leaves the hypergeometric probability unchanged. -/
theorem hypergeomMass_transpose_common (N k m i : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (hik : i ≤ k) (him : i ≤ m) :
    hypergeomMass N k m i = hypergeomMass N m k i := by
  have hden_m : (Nat.choose N m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hm
  have hden_k : (Nat.choose N k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hk
  by_cases hleft : m - i ≤ N - k
  · have hright : k - i ≤ N - m := by omega
    have hsum : N - k - (m - i) = N - m - (k - i) := by omega
    unfold hypergeomMass hypergeomCount
    simp only [Nat.cast_mul]
    rw [Nat.cast_choose ℝ hik, Nat.cast_choose ℝ hleft,
      Nat.cast_choose ℝ hm, Nat.cast_choose ℝ him,
      Nat.cast_choose ℝ hright, Nat.cast_choose ℝ hk, hsum]
    field_simp [Nat.factorial_ne_zero]
  · have hleft_zero : Nat.choose (N - k) (m - i) = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    have hright_zero : Nat.choose (N - m) (k - i) = 0 := by
      apply Nat.choose_eq_zero_of_lt
      omega
    simp [hypergeomMass, hypergeomCount, hleft_zero, hright_zero]

/-- The totalized PMF is invariant under transposition at every natural
index, including indices outside either finite sampling range. -/
theorem hypergeomPMFValue_transpose (N k m i : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomPMFValue N k m i = hypergeomPMFValue N m k i := by
  by_cases him : i ≤ m
  · by_cases hik : i ≤ k
    · simp only [hypergeomPMFValue, if_pos him, if_pos hik]
      exact hypergeomMass_transpose_common N k m i hk hm hik him
    · have hleft_zero : hypergeomMass N k m i = 0 := by
        have hchoose : Nat.choose k i = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        simp [hypergeomMass, hypergeomCount, hchoose]
      simp [hypergeomPMFValue, him, hik, hleft_zero]
  · by_cases hik : i ≤ k
    · have hright_zero : hypergeomMass N m k i = 0 := by
        have hchoose : Nat.choose m i = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        simp [hypergeomMass, hypergeomCount, hchoose]
      simp [hypergeomPMFValue, him, hik, hright_zero]
    · simp [hypergeomPMFValue, him, hik]

private theorem hypergeomMGF_eq_total_range (N k m : ℕ)
    (hm : m ≤ N) (t : ℝ) :
    hypergeomMGF N k m t =
      ∑ i ∈ Finset.range (N + 1),
        hypergeomPMFValue N k m i * Real.exp (t * (i : ℝ)) := by
  unfold hypergeomMGF finiteMGF
  calc
    (∑ i ∈ Finset.range (m + 1),
        hypergeomMass N k m i * Real.exp (t * (i : ℝ))) =
      ∑ i ∈ Finset.range (m + 1),
        hypergeomPMFValue N k m i * Real.exp (t * (i : ℝ)) := by
          apply Finset.sum_congr rfl
          intro i hi
          have him : i ≤ m := by
            exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          simp [hypergeomPMFValue, him]
    _ = ∑ i ∈ Finset.range (N + 1),
          hypergeomPMFValue N k m i * Real.exp (t * (i : ℝ)) := by
          apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hm))
          intro i hiN himrange
          have him : ¬ i ≤ m := by
            intro him
            exact himrange (Finset.mem_range.mpr (Nat.lt_succ_of_le him))
          simp [hypergeomPMFValue, him]

/-- The finite hypergeometric MGF is invariant under transposition. -/
theorem hypergeomMGF_transpose (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N)
    (t : ℝ) :
    hypergeomMGF N k m t = hypergeomMGF N m k t := by
  rw [hypergeomMGF_eq_total_range N k m hm t,
    hypergeomMGF_eq_total_range N m k hk t]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hypergeomPMFValue_transpose N k m i hk hm]

/-- Complementing marked and unmarked elements sends the count `i` to
`m - i` without changing its probability mass. -/
theorem hypergeomMass_success_complement (N k m i : ℕ)
    (hk : k ≤ N) (hi : i ≤ m) :
    hypergeomMass N (N - k) m (m - i) = hypergeomMass N k m i := by
  have hcomp : N - (N - k) = k := Nat.sub_sub_self hk
  have hsub : m - (m - i) = i := Nat.sub_sub_self hi
  simp [hypergeomMass, hypergeomCount, hcomp, hsub, Nat.mul_comm]

/-- Success-complement identity for the finite hypergeometric MGF. -/
theorem hypergeomMGF_success_complement (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    hypergeomMGF N k m t =
      Real.exp (t * (m : ℝ)) * hypergeomMGF N (N - k) m (-t) := by
  unfold hypergeomMGF finiteMGF
  calc
    (∑ i ∈ Finset.range (m + 1),
        hypergeomMass N k m i * Real.exp (t * (i : ℝ))) =
      ∑ i ∈ Finset.range (m + 1),
        hypergeomMass N k m i * Real.exp (t * (i : ℝ)) := rfl
    _ = ∑ j ∈ Finset.range (m + 1),
          hypergeomMass N k m (m - j) *
            (Real.exp (t * (m : ℝ)) * Real.exp ((-t) * (j : ℝ))) := by
          conv_lhs =>
            rw [← Finset.sum_range_reflect (fun i =>
              hypergeomMass N k m i * Real.exp (t * (i : ℝ))) (m + 1)]
          apply Finset.sum_congr rfl
          intro j hj
          have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hidx : m + 1 - 1 - j = m - j := by omega
          rw [hidx]
          have hexp : Real.exp (t * ((m - j : ℕ) : ℝ)) =
              Real.exp (t * (m : ℝ)) * Real.exp ((-t) * (j : ℝ)) := by
            rw [Nat.cast_sub hjm, ← Real.exp_add]
            congr 1 <;> ring
          rw [hexp]
    _ = ∑ j ∈ Finset.range (m + 1),
          hypergeomMass N (N - k) m j *
            (Real.exp (t * (m : ℝ)) * Real.exp ((-t) * (j : ℝ))) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
          have hsub : m - (m - j) = j := Nat.sub_sub_self hjm
          have hmass := hypergeomMass_success_complement N k m (m - j) hk
            (Nat.sub_le _ _)
          rw [hsub] at hmass
          rw [← hmass]
    _ = Real.exp (t * (m : ℝ)) *
          ∑ j ∈ Finset.range (m + 1),
            hypergeomMass N (N - k) m j * Real.exp ((-t) * (j : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring

/-- Sample-complement identity, obtained by transposing, complementing
successes, and transposing back. -/
theorem hypergeomMGF_sample_complement (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    hypergeomMGF N k m t =
      Real.exp (t * (k : ℝ)) * hypergeomMGF N k (N - m) (-t) := by
  calc
    hypergeomMGF N k m t = hypergeomMGF N m k t :=
      hypergeomMGF_transpose N k m hk hm t
    _ = Real.exp (t * (k : ℝ)) * hypergeomMGF N (N - m) k (-t) :=
      hypergeomMGF_success_complement N m k hm hk t
    _ = Real.exp (t * (k : ℝ)) * hypergeomMGF N k (N - m) (-t) := by
      rw [hypergeomMGF_transpose N (N - m) k (by omega) (by omega) (-t)]

end ExactHoeffding
