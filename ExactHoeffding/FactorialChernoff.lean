import ExactHoeffding.GeneralFactorialMoments
import ExactHoeffding.Chernoff
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-! # Integer-threshold factorial-moment bounds -/

namespace ExactHoeffding

noncomputable section

def finiteBinomialMoment {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ s, (Nat.choose (x i) j : ℝ) * w i

def finiteFactorialCandidate {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d j : ℕ) : ℝ :=
  finiteBinomialMoment s x w j / (Nat.choose d j : ℝ)

def finiteFactorialBound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d : ℕ) : ℝ :=
  (Finset.image (finiteFactorialCandidate s x w d) (Finset.range (d + 1))).min'
    (by
      apply Finset.Nonempty.image
      exact ⟨0, Finset.mem_range.mpr (by omega)⟩)

def finiteIntegerTailMass {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d : ℕ) : ℝ :=
  ∑ i ∈ s, if d ≤ x i then w i else 0

private theorem cast_choose_div_factorial (n j : ℕ) :
    (Nat.choose n j : ℝ) = (Nat.descFactorial n j : ℝ) / (Nat.factorial j : ℝ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  have hj : (Nat.factorial j : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  field_simp

private theorem choose_binomial_polynomial (z : ℝ) (n : ℕ) :
    (1 + z) ^ n =
      ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℝ) * z ^ j := by
  rw [show (1 : ℝ) + z = z + 1 by ring, add_pow]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [one_pow, mul_one]
  ring

private theorem choose_binomial_polynomial_trunc_le (z : ℝ) (hz : 0 ≤ z)
    (n d : ℕ) :
    (∑ j ∈ Finset.range (d + 1), (Nat.choose n j : ℝ) * z ^ j) ≤ (1 + z) ^ n := by
  rw [choose_binomial_polynomial]
  by_cases hdn : d ≤ n
  · apply Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.succ_le_succ hdn))
    intro j hj hnot
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _)
  · have hnd : n < d := by omega
    have hsum :
        (∑ j ∈ Finset.range (d + 1), (Nat.choose n j : ℝ) * z ^ j) =
          ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℝ) * z ^ j := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.le_of_lt hnd)))
      intro j hj hnot
      have hnj : n < j := by
        simp only [Finset.mem_range] at hj hnot
        omega
      simp [Nat.choose_eq_zero_of_lt hnj]
    rw [hsum]

private theorem finiteBinomialMoment_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (j : ℕ)
    (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ finiteBinomialMoment s x w j := by
  unfold finiteBinomialMoment
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (Nat.cast_nonneg _) (hw i hi)

theorem finiteFactorialCandidate_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d j : ℕ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    0 ≤ finiteFactorialCandidate s x w d j := by
  unfold finiteFactorialCandidate
  exact div_nonneg (finiteBinomialMoment_nonneg s x w j hw) (Nat.cast_nonneg _)

theorem finiteFactorialBound_le_candidate {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d j : ℕ) (hjd : j ≤ d) :
    finiteFactorialBound s x w d ≤ finiteFactorialCandidate s x w d j := by
  unfold finiteFactorialBound
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

theorem finiteIntegerTailMass_le_candidate {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d j : ℕ) (hjd : j ≤ d)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    finiteIntegerTailMass s x w d ≤ finiteFactorialCandidate s x w d j := by
  have hchooseD : 0 < (Nat.choose d j : ℝ) := by
    exact_mod_cast Nat.choose_pos hjd
  have hterm (i : ι) (hi : i ∈ s) :
      (if d ≤ x i then (Nat.choose d j : ℝ) * w i else 0) ≤
        (Nat.choose (x i) j : ℝ) * w i := by
    by_cases hd : d ≤ x i
    · rw [if_pos hd]
      exact mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr (Nat.choose_le_choose j hd)) (hw i hi)
    · rw [if_neg hd]
      exact mul_nonneg (Nat.cast_nonneg _) (hw i hi)
  have hsum :
      (Nat.choose d j : ℝ) * finiteIntegerTailMass s x w d ≤
        finiteBinomialMoment s x w j := by
    unfold finiteIntegerTailMass finiteBinomialMoment
    calc
      (Nat.choose d j : ℝ) *
          (∑ i ∈ s, if d ≤ x i then w i else 0) =
          ∑ i ∈ s, (Nat.choose d j : ℝ) *
            (if d ≤ x i then w i else 0) :=
        Finset.mul_sum s (fun i => if d ≤ x i then w i else 0)
          (Nat.choose d j : ℝ)
      _ = (∑ i ∈ s,
          if d ≤ x i then (Nat.choose d j : ℝ) * w i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hd : d ≤ x i
        · simp [hd]
        · simp [hd]
      _ ≤ (∑ i ∈ s, (Nat.choose (x i) j : ℝ) * w i) :=
          Finset.sum_le_sum (fun i hi => hterm i hi)
  rw [finiteFactorialCandidate]
  exact (le_div_iff₀ hchooseD).2 (by nlinarith [hsum])

theorem finiteIntegerTailMass_le_factorialBound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d : ℕ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    finiteIntegerTailMass s x w d ≤ finiteFactorialBound s x w d := by
  unfold finiteFactorialBound
  have hmem := Finset.min'_mem
    (Finset.image (finiteFactorialCandidate s x w d) (Finset.range (d + 1)))
    (by
      apply Finset.Nonempty.image
      exact ⟨0, Finset.mem_range.mpr (by omega)⟩)
  rcases Finset.mem_image.mp hmem with ⟨j, hj, hvalue⟩
  have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [← hvalue]
  exact finiteIntegerTailMass_le_candidate s x w d j hjd hw

private theorem finiteBinomialMoment_truncated_pgf {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d : ℕ) (z : ℝ) :
    (∑ j ∈ Finset.range (d + 1), finiteBinomialMoment s x w j * z ^ j) =
      ∑ i ∈ s, w i *
        (∑ j ∈ Finset.range (d + 1), (Nat.choose (x i) j : ℝ) * z ^ j) := by
  unfold finiteBinomialMoment
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem finiteFactorialBound_le_chernoff_tilt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d : ℕ) (t : ℝ)
    (ht : 0 ≤ t) (hw : ∀ i ∈ s, 0 ≤ w i) :
    finiteFactorialBound s x w d ≤
      Real.exp (-t * (d : ℝ)) *
        finiteMGF s w (fun i => (x i : ℝ)) t := by
  let z := Real.exp t - 1
  have hz : 0 ≤ z := by
    dsimp [z]
    linarith [Real.one_le_exp_iff.mpr ht]
  have hlow :
      finiteFactorialBound s x w d *
        (∑ j ∈ Finset.range (d + 1), (Nat.choose d j : ℝ) * z ^ j) ≤
          ∑ j ∈ Finset.range (d + 1),
            finiteBinomialMoment s x w j * z ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hbest := finiteFactorialBound_le_candidate s x w d j hjd
    have hc : 0 ≤ (Nat.choose d j : ℝ) * z ^ j :=
      mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _)
    have hmul := mul_le_mul_of_nonneg_right hbest hc
    have hchoose : 0 < (Nat.choose d j : ℝ) := by
      exact_mod_cast Nat.choose_pos hjd
    have hcancel :
        finiteFactorialCandidate s x w d j *
          ((Nat.choose d j : ℝ) * z ^ j) =
        finiteBinomialMoment s x w j * z ^ j := by
      unfold finiteFactorialCandidate
      field_simp
    rw [hcancel] at hmul
    exact hmul
  have hpoly :
      (∑ j ∈ Finset.range (d + 1), (Nat.choose d j : ℝ) * z ^ j) = (1 + z) ^ d := by
    symm
    exact choose_binomial_polynomial z d
  rw [hpoly] at hlow
  have hpartial :
      (∑ j ∈ Finset.range (d + 1),
          finiteBinomialMoment s x w j * z ^ j) ≤
        finiteMGF s w (fun i => (x i : ℝ)) t := by
    rw [finiteBinomialMoment_truncated_pgf]
    unfold finiteMGF
    apply Finset.sum_le_sum
    intro i hi
    have hbin := choose_binomial_polynomial_trunc_le z hz (x i) d
    have hmul := mul_le_mul_of_nonneg_left hbin (hw i hi)
    have hexp : (1 + z) ^ (x i) = Real.exp (t * (x i : ℝ)) := by
      dsimp [z]
      rw [add_sub_cancel, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    simpa [hexp] using hmul
  have hprod :
      Real.exp (-t * (d : ℝ)) * (1 + z) ^ d = 1 := by
    dsimp [z]
    rw [add_sub_cancel]
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    have he : -t * (d : ℝ) + (d : ℝ) * t = 0 := by ring
    rw [he, Real.exp_zero]
  calc
    finiteFactorialBound s x w d =
        Real.exp (-t * (d : ℝ)) *
          (finiteFactorialBound s x w d * (1 + z) ^ d) := by
            calc
              _ = (Real.exp (-t * (d : ℝ)) * (1 + z) ^ d) *
                    finiteFactorialBound s x w d := by rw [hprod]; ring
              _ = _ := by ring
    _ ≤ Real.exp (-t * (d : ℝ)) *
          (∑ j ∈ Finset.range (d + 1),
            finiteBinomialMoment s x w j * z ^ j) := by
          exact mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
    _ ≤ Real.exp (-t * (d : ℝ)) *
          finiteMGF s w (fun i => (x i : ℝ)) t :=
          mul_le_mul_of_nonneg_left hpartial (Real.exp_pos _).le

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The set of nonnegative-tilt Chernoff candidates. -/
def finiteChernoffSet {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d : ℕ) : Set ℝ :=
  {c : ℝ | ∃ t : ℝ, 0 ≤ t ∧
    c = Real.exp (-t * (d : ℝ)) *
      finiteMGF s w (fun i => (x i : ℝ)) t}

theorem finiteFactorialBound_le_chernoff_inf {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d : ℕ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    finiteFactorialBound s x w d ≤ sInf (finiteChernoffSet s x w d) := by
  apply le_csInf
  · refine ⟨Real.exp (-(0 : ℝ) * (d : ℝ)) *
      finiteMGF s w (fun i => (x i : ℝ)) 0, ?_⟩
    exact ⟨0, le_rfl, rfl⟩
  · rintro c ⟨t, ht, rfl⟩
    exact finiteFactorialBound_le_chernoff_tilt s x w d t ht hw

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- Exact binomial-basis moments of the actual hypergeometric law. -/
theorem hypergeom_binomialMoment (N k m j : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    finiteBinomialMoment (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) j =
      if j ≤ N then
        ((Nat.choose m j : ℝ) * (Nat.choose k j : ℝ)) /
          (Nat.choose N j : ℝ)
      else 0 := by
  unfold finiteBinomialMoment
  have hterm (i : ℕ) :
      (Nat.choose i j : ℝ) * hypergeomMass N k m i =
        ((Nat.descFactorial i j : ℝ) * hypergeomMass N k m i) /
          (Nat.factorial j : ℝ) := by
    rw [cast_choose_div_factorial]
    ring
  have hsum :
      (∑ i ∈ Finset.range (m + 1),
        (Nat.choose i j : ℝ) * hypergeomMass N k m i) =
      (∑ i ∈ Finset.range (m + 1),
        (Nat.descFactorial i j : ℝ) * hypergeomMass N k m i) /
          (Nat.factorial j : ℝ) := by
    simp_rw [hterm]
    rw [Finset.sum_div]
  rw [hsum, hypergeom_descFactorial_expectation N k m j hk hm]
  by_cases hjN : j ≤ N
  · rw [if_pos hjN]
    have hdesc (r : ℕ) :
        (Nat.descFactorial r j : ℝ) =
          (Nat.factorial j : ℝ) * (Nat.choose r j : ℝ) := by
      exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose r j
    rw [hdesc m, hdesc k, hdesc N]
    have hfact : (Nat.factorial j : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero j
    have hchoose : (Nat.choose N j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hjN))
    simp only [if_pos hjN]
    field_simp [hfact, hchoose]
  · simp [hjN]

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The hypergeometric factorial candidate is the exact finite binomial-basis
ratio; all denominators are shown nonzero on the admissible degree range. -/
theorem hypergeomFactorialCandidate_eq (N k m d j : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (hjd : j ≤ d) (hjN : j ≤ N) :
    finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d j =
      (((Nat.choose m j : ℝ) * (Nat.choose k j : ℝ)) /
          (Nat.choose N j : ℝ)) /
        (Nat.choose d j : ℝ) := by
  unfold finiteFactorialCandidate
  rw [hypergeom_binomialMoment N k m j hk hm, if_pos hjN]

end
end ExactHoeffding
