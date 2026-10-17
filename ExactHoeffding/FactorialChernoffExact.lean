import ExactHoeffding.FactorialChernoff
import ExactHoeffding.PiecewiseKLStrict
import ExactHoeffding.HypergeomCenteredLogNonneg

namespace ExactHoeffding
noncomputable section
open Set

private theorem hypergeom_factorialBound_nonneg (N k m d : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    0 ≤ finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d := by
  unfold finiteFactorialBound
  apply Finset.le_min'
  intro y hy
  rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
  exact finiteFactorialCandidate_nonneg _ _ _ _ _
    (fun i hi => hypergeomMass_nonneg N k m i)

private theorem hypergeom_factorialBound_le_one (N k m d : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d ≤ 1 := by
  have h := finiteFactorialBound_le_candidate
    (Finset.range (m + 1)) (fun i => i) (hypergeomMass N k m) d 0 (by omega)
  have h0 : finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d 0 = 1 := by
    unfold finiteFactorialCandidate finiteBinomialMoment
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Finset.sum_const_zero,
      Finset.sum_ite_irrel, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hypergeomMass_total N k m hk hm]
    norm_num
  rw [h0] at h
  exact h

private theorem hypergeom_factorialBound_le_exp_neg_rate
    (N k m d : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k)
    (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hd : d ≤ m) (hdmu : (m : ℝ) * k / N < (d : ℝ)) :
    finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d ≤
      Real.exp (-hypergeomKLRate N k m (d : ℝ)) := by
  let F : ℝ := finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d
  let μ : ℝ := (m : ℝ) * k / N
  change F ≤ Real.exp (-hypergeomKLRate N k m (d : ℝ))
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkm : k + m ≤ N := by omega
  have hF0 : 0 ≤ F := by
    dsimp [F]
    exact hypergeom_factorialBound_nonneg N k m d (by omega) (by omega)
  have hF1 : F ≤ 1 := by
    dsimp [F]
    exact hypergeom_factorialBound_le_one N k m d (by omega) (by omega)
  by_cases hFzero : F = 0
  · rw [hFzero]
    exact (Real.exp_pos _).le
  have hFpos : 0 < F := lt_of_le_of_ne hF0 (Ne.symm hFzero)
  have hμd : 0 ≤ (d : ℝ) - μ := by
    dsimp [μ]
    linarith
  have hBdd : BddAbove (Set.range (fun t : ℝ =>
      t * ((d : ℝ) - μ) - hypergeomCenteredLogMGF N k m t)) := by
    simpa [μ] using hypergeomKLRate_bddAbove N k m hmk hkm
      (d : ℝ) (by positivity) (by exact_mod_cast hd)
  have hupper : ∀ y ∈ Set.range (fun t : ℝ =>
      t * ((d : ℝ) - μ) - hypergeomCenteredLogMGF N k m t),
      y ≤ -Real.log F := by
    rintro y ⟨t, rfl⟩
    by_cases ht : 0 ≤ t
    · have hbound := finiteFactorialBound_le_chernoff_tilt
        (Finset.range (m + 1)) (fun i => i) (hypergeomMass N k m) d t ht
        (fun i hi => hypergeomMass_nonneg N k m i)
      have hmgfpos : 0 < hypergeomMGF N k m t := by
        exact finiteMGF_pos_of_normalized (Finset.range (m + 1))
          (hypergeomMass N k m) (fun i => (i : ℝ))
          (fun i _ => hypergeomMass_nonneg N k m i)
          (hypergeomMass_total N k m (by omega) (by omega)) t
      have hrewrite : Real.exp (-(t * (d : ℝ))) * hypergeomMGF N k m t =
          Real.exp (-(t * ((d : ℝ) - μ) - hypergeomCenteredLogMGF N k m t)) := by
        calc
          Real.exp (-(t * (d : ℝ))) * hypergeomMGF N k m t =
              Real.exp (-(t * (d : ℝ))) * Real.exp (Real.log (hypergeomMGF N k m t)) := by
                rw [Real.exp_log hmgfpos]
          _ = Real.exp (-(t * (d : ℝ)) + Real.log (hypergeomMGF N k m t)) := by
                rw [← Real.exp_add]
          _ = Real.exp (-(t * ((d : ℝ) - μ) - hypergeomCenteredLogMGF N k m t)) := by
                congr 1
                unfold hypergeomCenteredLogMGF μ
                ring
      have hFexp : F ≤ Real.exp (-(t * ((d : ℝ) - μ) -
          hypergeomCenteredLogMGF N k m t)) := by
        dsimp [F] at hbound ⊢
        rw [← hrewrite]
        simpa [hypergeomMGF] using hbound
      have hlog := (Real.log_le_iff_le_exp hFpos).2 hFexp
      linarith
    · have ht' : t ≤ 0 := le_of_not_ge ht
      have hnon := hypergeomCenteredLogMGF_nonneg N k m (by omega) (by omega) t
      have hterm : t * ((d : ℝ) - μ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ht' hμd
      have hcan : t * ((d : ℝ) - μ) -
          hypergeomCenteredLogMGF N k m t ≤ 0 := by linarith
      have hlogF : Real.log F ≤ 0 := Real.log_nonpos hF0 hF1
      linarith
  have hI : hypergeomKLRate N k m (d : ℝ) ≤ -Real.log F := by
    unfold hypergeomKLRate
    apply csSup_le
    · exact ⟨0, ⟨0, by simp [hypergeomCenteredLogMGF_zero N k m (by omega) (by omega)]⟩⟩
    · rintro y ⟨t, rfl⟩
      exact hupper _ ⟨t, rfl⟩
  have hlogexp : Real.log F ≤ -hypergeomKLRate N k m (d : ℝ) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlogexp
  simpa [Real.exp_log hFpos] using hexp

/-- Exact factorial-moment domination by the actual hypergeometric Chernoff
rate on the supported canonical upper-tail domain. -/
theorem hypergeomFactorialBound_le_exp_neg_KLRate
    (N k m d : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k)
    (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hd : d ≤ m) (hdmu : (m : ℝ) * k / N < (d : ℝ)) :
    finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d ≤
      Real.exp (-hypergeomKLRate N k m (d : ℝ)) :=
  hypergeom_factorialBound_le_exp_neg_rate N k m d hm hmk hk hhalf hd hdmu

/-- The factorial bound is strictly below the closed piecewise-KL exponent on
noncentral supported upper integer thresholds. -/
theorem hypergeomFactorialBound_lt_exp_neg_piecewiseRate
    (N k m d : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k)
    (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hd : d ≤ m) (hdmu : (m : ℝ) * k / N < (d : ℝ)) :
    finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d <
      Real.exp (-canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) (d : ℝ)) := by
  have hF := hypergeom_factorialBound_le_exp_neg_rate N k m d hm hmk hk hhalf hd hdmu
  have hstrict := hypergeomKLRate_strict_piecewise N k m hm hmk hk hhalf
    (d : ℝ) (by positivity) (by exact_mod_cast hd) (by
      have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      dsimp
      exact ne_of_gt hdmu)
  have hexp : Real.exp (-hypergeomKLRate N k m (d : ℝ)) <
      Real.exp (-canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) (d : ℝ)) := by
    apply Real.exp_lt_exp.mpr
    linarith
  exact hF.trans_lt hexp

/-- The complete supported integer upper-tail comparison, including the tail
mass itself. -/
theorem hypergeomIntegerTail_le_exp_neg_piecewiseRate
    (N k m d : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k)
    (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hd : d ≤ m) (hdmu : (m : ℝ) * k / N < (d : ℝ)) :
    finiteIntegerTailMass (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d ≤
      Real.exp (-canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) (d : ℝ)) := by
  exact (show finiteIntegerTailMass (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d <
        Real.exp (-canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) (d : ℝ)) from by
    calc
      finiteIntegerTailMass (Finset.range (m + 1)) (fun i => i)
          (hypergeomMass N k m) d ≤
          finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
            (hypergeomMass N k m) d :=
        finiteIntegerTailMass_le_factorialBound
          (Finset.range (m + 1)) (fun i => i) (hypergeomMass N k m) d
          (fun i hi => hypergeomMass_nonneg N k m i)
      _ < Real.exp (-canonicalPiecewiseRate (N : ℝ) (k : ℝ) (m : ℝ) (d : ℝ)) :=
        hypergeomFactorialBound_lt_exp_neg_piecewiseRate N k m d hm hmk hk hhalf hd hdmu).le

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The exact falling-factorial form of the hypergeometric factorial candidate.

This is the form displayed in Proposition `A:factorial`; the preceding
binomial-basis theorem supplies the finite-law calculation and this corollary
only changes basis using `descFactorial = factorial * choose`. -/
theorem hypergeom_factorial_candidate_formula
    (N k m d j : ℕ) (hk : k ≤ N) (hm : m ≤ N)
    (hdm : d ≤ m) (hjd : j ≤ d) :
    finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d j =
      ((Nat.descFactorial k j : ℝ) * (Nat.descFactorial m j : ℝ)) /
        ((Nat.descFactorial N j : ℝ) * (Nat.descFactorial d j : ℝ)) := by
  have hjN : j ≤ N := hjd.trans (hdm.trans hm)
  calc
    finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d j =
      (((Nat.choose m j : ℝ) * (Nat.choose k j : ℝ)) /
          (Nat.choose N j : ℝ)) /
        (Nat.choose d j : ℝ) :=
      hypergeomFactorialCandidate_eq N k m d j hk hm hjd hjN
    _ = ((Nat.descFactorial k j : ℝ) * (Nat.descFactorial m j : ℝ)) /
        ((Nat.descFactorial N j : ℝ) * (Nat.descFactorial d j : ℝ)) := by
      have hfac : (Nat.factorial j : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero j
      have hchooseN : (Nat.choose N j : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hjN))
      have hchooseD : (Nat.choose d j : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hjd))
      have hdesc (r : ℕ) :
          (Nat.descFactorial r j : ℝ) =
            (Nat.factorial j : ℝ) * (Nat.choose r j : ℝ) := by
        exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose r j
      rw [hdesc k, hdesc m, hdesc N, hdesc d]
      field_simp [hfac, hchooseN, hchooseD]


/-- Exact factorial ratio on its full nonzero-denominator domain. -/
theorem hypergeom_factorial_candidate_formula_of_degree_le_population
    (N k m d j : ℕ) (hk : k ≤ N) (hm : m ≤ N)
    (hjd : j ≤ d) (hjN : j ≤ N) :
    finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d j =
      ((Nat.descFactorial k j : ℝ) * (Nat.descFactorial m j : ℝ)) /
        ((Nat.descFactorial N j : ℝ) * (Nat.descFactorial d j : ℝ)) := by
  calc
    finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d j =
      (((Nat.choose m j : ℝ) * (Nat.choose k j : ℝ)) /
          (Nat.choose N j : ℝ)) /
        (Nat.choose d j : ℝ) :=
      hypergeomFactorialCandidate_eq N k m d j hk hm hjd hjN
    _ = ((Nat.descFactorial k j : ℝ) * (Nat.descFactorial m j : ℝ)) /
        ((Nat.descFactorial N j : ℝ) * (Nat.descFactorial d j : ℝ)) := by
      have hfac : (Nat.factorial j : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero j
      have hchooseN : (Nat.choose N j : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hjN))
      have hchooseD : (Nat.choose d j : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hjd))
      have hdesc (r : ℕ) :
          (Nat.descFactorial r j : ℝ) =
            (Nat.factorial j : ℝ) * (Nat.choose r j : ℝ) := by
        exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose r j
      rw [hdesc k, hdesc m, hdesc N, hdesc d]
      field_simp [hfac, hchooseN, hchooseD]


/-- Beyond the population degree the binomial-basis moment is zero. This is
the separate zero branch of the ordinary (non-totalized) ratio formula. -/
theorem hypergeom_factorial_candidate_eq_zero_of_population_lt_degree
    (N k m d j : ℕ) (hk : k ≤ N) (hm : m ≤ N) (hjN : N < j) :
    finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
      (hypergeomMass N k m) d j = 0 := by
  unfold finiteFactorialCandidate
  rw [hypergeom_binomialMoment N k m j hk hm, if_neg (by omega)]
  exact zero_div _

end
end ExactHoeffding
