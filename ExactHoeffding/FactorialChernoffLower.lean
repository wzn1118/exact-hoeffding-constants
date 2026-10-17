import ExactHoeffding.FactorialChernoffExact

/-!
# Reflected factorial bounds for the actual hypergeometric lower tail

The reflected variable is the concrete finite-support map `i ↦ m - i`
with the original hypergeometric weights. No canonical-domain hypothesis
is transferred to the complemented success count.
-/

namespace ExactHoeffding
noncomputable section
open Set

/-- The actual lower-tail mass is bounded by the factorial bound of `m - H`. -/
theorem hypergeomLowerTailMass_le_reflectedFactorialBound
    (N k m d : ℕ) (hd : d ≤ m) :
    (∑ i ∈ Finset.range (m + 1), if i ≤ d then hypergeomMass N k m i else 0) ≤
      finiteFactorialBound (Finset.range (m + 1)) (fun i => m - i)
        (hypergeomMass N k m) (m - d) := by
  have h := finiteIntegerTailMass_le_factorialBound
    (Finset.range (m + 1)) (fun i => m - i) (hypergeomMass N k m) (m - d)
    (fun i hi => hypergeomMass_nonneg N k m i)
  convert h using 1
  unfold finiteIntegerTailMass
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hevent : m - d ≤ m - i ↔ i ≤ d := by omega
  simpa only [hevent]

/-- Each nonpositive tilt of the original variable dominates the factorial
bound for its concrete reflection. -/
theorem hypergeomReflectedFactorialBound_le_chernoff_tilt
    (N k m d : ℕ) (hd : d ≤ m) (t : ℝ) (ht : t ≤ 0) :
    finiteFactorialBound (Finset.range (m + 1)) (fun i => m - i)
      (hypergeomMass N k m) (m - d) ≤
      Real.exp (-t * (d : ℝ)) * hypergeomMGF N k m t := by
  have h := finiteFactorialBound_le_chernoff_tilt
    (Finset.range (m + 1)) (fun i => m - i) (hypergeomMass N k m)
    (m - d) (-t) (by linarith) (fun i hi => hypergeomMass_nonneg N k m i)
  refine h.trans_eq ?_
  unfold hypergeomMGF finiteMGF
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  dsimp only
  rw [Nat.cast_sub hd, Nat.cast_sub him]
  have hexp :
      Real.exp (-(-t) * ((m : ℝ) - d)) *
          Real.exp ((-t) * ((m : ℝ) - i)) =
        Real.exp (-t * (d : ℝ)) * Real.exp (t * (i : ℝ)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = hypergeomMass N k m i *
        (Real.exp (-(-t) * ((m : ℝ) - d)) *
          Real.exp ((-t) * ((m : ℝ) - i))) := by ring
    _ = hypergeomMass N k m i *
        (Real.exp (-t * (d : ℝ)) * Real.exp (t * (i : ℝ))) := by rw [hexp]
    _ = _ := by ring

/-- The reflected factorial bound is dominated by the exponential of the
actual hypergeometric Legendre rate at a supported lower threshold. -/
theorem hypergeomReflectedFactorialBound_le_exp_neg_KLRate
    (N k m d : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k)
    (hk : 2 * k ≤ N) (hhalf : 2 * m < N)
    (hd : d ≤ m) (hdmu : (d : ℝ) < (m : ℝ) * k / N) :
    finiteFactorialBound (Finset.range (m + 1)) (fun i => m - i)
      (hypergeomMass N k m) (m - d) ≤
      Real.exp (-hypergeomKLRate N k m (d : ℝ)) := by
  let F : ℝ := finiteFactorialBound (Finset.range (m + 1)) (fun i => m - i)
    (hypergeomMass N k m) (m - d)
  let μ : ℝ := (m : ℝ) * k / N
  change F ≤ Real.exp (-hypergeomKLRate N k m (d : ℝ))
  have hF0 : 0 ≤ F := by
    dsimp [F]
    unfold finiteFactorialBound
    apply Finset.le_min'
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    exact finiteFactorialCandidate_nonneg _ _ _ _ _
      (fun i hi => hypergeomMass_nonneg N k m i)
  have hF1 : F ≤ 1 := by
    have h := finiteFactorialBound_le_candidate
      (Finset.range (m + 1)) (fun i => m - i) (hypergeomMass N k m) (m - d) 0
      (Nat.zero_le _)
    have h0 : finiteFactorialCandidate (Finset.range (m + 1)) (fun i => m - i)
        (hypergeomMass N k m) (m - d) 0 = 1 := by
      unfold finiteFactorialCandidate finiteBinomialMoment
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, div_one]
      exact hypergeomMass_total N k m (by omega) (by omega)
    rw [h0] at h
    exact h
  by_cases hFzero : F = 0
  · rw [hFzero]
    exact (Real.exp_pos _).le
  have hFpos : 0 < F := lt_of_le_of_ne hF0 (Ne.symm hFzero)
  have hdμ : (d : ℝ) - μ ≤ 0 := by dsimp [μ]; linarith
  have hupper : ∀ y ∈ Set.range (fun t : ℝ =>
      t * ((d : ℝ) - μ) - hypergeomCenteredLogMGF N k m t),
      y ≤ -Real.log F := by
    rintro y ⟨t, rfl⟩
    by_cases ht : t ≤ 0
    · have hbound := hypergeomReflectedFactorialBound_le_chernoff_tilt N k m d hd t ht
      have hmgfpos : 0 < hypergeomMGF N k m t := by
        exact finiteMGF_pos_of_normalized (Finset.range (m + 1))
          (hypergeomMass N k m) (fun i => (i : ℝ))
          (fun i _ => hypergeomMass_nonneg N k m i)
          (hypergeomMass_total N k m (by omega) (by omega)) t
      have hrewrite : Real.exp (-t * (d : ℝ)) * hypergeomMGF N k m t =
          Real.exp (-(t * ((d : ℝ) - μ) - hypergeomCenteredLogMGF N k m t)) := by
        calc
          _ = Real.exp (-t * (d : ℝ)) * Real.exp (Real.log (hypergeomMGF N k m t)) := by
            rw [Real.exp_log hmgfpos]
          _ = Real.exp (-t * (d : ℝ) + Real.log (hypergeomMGF N k m t)) := by
            rw [← Real.exp_add]
          _ = _ := by
            congr 1
            unfold hypergeomCenteredLogMGF μ
            ring
      have hFexp : F ≤ Real.exp (-(t * ((d : ℝ) - μ) -
          hypergeomCenteredLogMGF N k m t)) := by
        rw [← hrewrite]
        exact hbound
      have hlog := (Real.log_le_iff_le_exp hFpos).2 hFexp
      linarith
    · have ht' : 0 ≤ t := le_of_not_ge ht
      have hnon := hypergeomCenteredLogMGF_nonneg N k m (by omega) (by omega) t
      have hterm : t * ((d : ℝ) - μ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht' hdμ
      have hcan : t * ((d : ℝ) - μ) - hypergeomCenteredLogMGF N k m t ≤ 0 := by
        linarith
      have hlogF : Real.log F ≤ 0 := Real.log_nonpos hF0 hF1
      linarith
  have hI : hypergeomKLRate N k m (d : ℝ) ≤ -Real.log F := by
    unfold hypergeomKLRate
    apply csSup_le
    · exact ⟨0, ⟨0, by simp [hypergeomCenteredLogMGF_zero N k m (by omega) (by omega)]⟩⟩
    · rintro y ⟨t, rfl⟩
      exact hupper _ ⟨t, rfl⟩
  have hlogexp : Real.log F ≤ -hypergeomKLRate N k m (d : ℝ) := by linarith
  have hexp := Real.exp_le_exp.mpr hlogexp
  simpa [Real.exp_log hFpos] using hexp

/-- The reflected factorial bound is strictly smaller than the closed
piecewise-KL exponential, including the supported endpoint `d = 0`. -/
theorem hypergeomReflectedFactorialBound_lt_exp_neg_piecewiseRate
    (N k m d : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k)
    (hk : 2 * k ≤ N) (hhalf : 2 * m < N)
    (hd : d ≤ m) (hdmu : (d : ℝ) < (m : ℝ) * k / N) :
    finiteFactorialBound (Finset.range (m + 1)) (fun i => m - i)
      (hypergeomMass N k m) (m - d) <
      Real.exp (-canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) (d : ℝ)) := by
  have hF := hypergeomReflectedFactorialBound_le_exp_neg_KLRate
    N k m d hm hmk hk hhalf hd hdmu
  have hstrict := hypergeomKLRate_strict_piecewise N k m hm hmk hk hhalf
    (d : ℝ) (by positivity) (by exact_mod_cast hd) (ne_of_lt hdmu)
  exact hF.trans_lt (Real.exp_lt_exp.mpr (neg_lt_neg hstrict))

/-- Complete factorial and exact-Chernoff chain for the actual lower event. -/
theorem hypergeom_lower_factorial_chernoff_end_to_end
    (N k m d : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k)
    (hk : 2 * k ≤ N) (hhalf : 2 * m < N)
    (hd : d ≤ m) (hdmu : (d : ℝ) < (m : ℝ) * k / N) :
    (∑ i ∈ Finset.range (m + 1), if i ≤ d then hypergeomMass N k m i else 0) ≤
        finiteFactorialBound (Finset.range (m + 1)) (fun i => m - i)
          (hypergeomMass N k m) (m - d) ∧
      finiteFactorialBound (Finset.range (m + 1)) (fun i => m - i)
          (hypergeomMass N k m) (m - d) ≤
        Real.exp (-hypergeomKLRate N k m (d : ℝ)) ∧
      Real.exp (-hypergeomKLRate N k m (d : ℝ)) <
        Real.exp (-canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) (d : ℝ)) := by
  refine ⟨hypergeomLowerTailMass_le_reflectedFactorialBound N k m d hd,
    hypergeomReflectedFactorialBound_le_exp_neg_KLRate N k m d hm hmk hk hhalf hd hdmu, ?_⟩
  have hstrict := hypergeomKLRate_strict_piecewise N k m hm hmk hk hhalf
    (d : ℝ) (by positivity) (by exact_mod_cast hd) (ne_of_lt hdmu)
  exact Real.exp_lt_exp.mpr (neg_lt_neg hstrict)

end
end ExactHoeffding
