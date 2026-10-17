import ExactHoeffding.FactorialChernoff
import ExactHoeffding.FactorialChernoffExact
import ExactHoeffding.FactorialChernoffLower
import ExactHoeffding.FactorialSupportExterior

namespace ExactHoeffding
noncomputable section

/-- Full Lean transcription of manuscript result `A:factorial`: the generic
finite integer-valued factorial bound and Chernoff comparison; the actual
hypergeometric falling-factorial identity on its positive-denominator domain;
the supported upper and reflected lower KL comparisons; and the zero branch
beyond the true support. -/
theorem manuscript_A_factorial_full_contract
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → ℕ) (w : ι → ℝ) (d : ℕ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (htotal : ∑ i ∈ s, w i = 1) :
    (finiteIntegerTailMass s x w d ≤ finiteFactorialBound s x w d ∧
      finiteFactorialBound s x w d ≤ sInf (finiteChernoffSet s x w d)) ∧
    (∀ N k m d : ℕ, k ≤ N → m ≤ N → d ≤ min k m → 1 ≤ d →
      ((∀ j : ℕ, j ≤ d →
          finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
              (hypergeomMass N k m) d j =
            ((Nat.descFactorial k j : ℝ) * (Nat.descFactorial m j : ℝ)) /
              ((Nat.descFactorial N j : ℝ) * (Nat.descFactorial d j : ℝ))) ∧
       (∀ j : ℕ, j ≤ d →
          0 < (Nat.descFactorial N j : ℝ) ∧
          0 < (Nat.descFactorial d j : ℝ)))) ∧
    (∀ N k m d : ℕ, 3 ≤ m → m ≤ k → 2*k ≤ N → 2*m < N →
      d ≤ m → (m:ℝ)*k/N < (d:ℝ) →
      finiteIntegerTailMass (Finset.range (m+1)) (fun i => i)
          (hypergeomMass N k m) d ≤
        finiteFactorialBound (Finset.range (m+1)) (fun i => i)
          (hypergeomMass N k m) d ∧
      finiteFactorialBound (Finset.range (m+1)) (fun i => i)
          (hypergeomMass N k m) d ≤ Real.exp (-hypergeomKLRate N k m (d:ℝ)) ∧
      Real.exp (-hypergeomKLRate N k m (d:ℝ)) <
        Real.exp (-canonicalPiecewiseRate (N:ℝ) (k:ℝ) (m:ℝ) (d:ℝ)) ∧
      finiteFactorialBound (Finset.range (m+1)) (fun i => i)
          (hypergeomMass N k m) d <
        Real.exp (-canonicalPiecewiseRate (N:ℝ) (k:ℝ) (m:ℝ) (d:ℝ))) ∧
    (∀ N k m d : ℕ, k ≤ N → m ≤ N → m < d →
      finiteIntegerTailMass (Finset.range (m+1)) (fun i => i)
          (hypergeomMass N k m) d = 0 ∧
      finiteFactorialBound (Finset.range (m+1)) (fun i => i)
          (hypergeomMass N k m) d = 0 ∧
      sInf (finiteChernoffSet (Finset.range (m+1)) (fun i => i)
          (hypergeomMass N k m) d) = 0) ∧
    ∀ N k m d : ℕ, 3 ≤ m → m ≤ k → 2*k ≤ N → 2*m < N →
      d ≤ m → (d:ℝ) < (m:ℝ)*k/N →
      (∑ i ∈ Finset.range (m+1), if i ≤ d then hypergeomMass N k m i else 0) ≤
        finiteFactorialBound (Finset.range (m+1)) (fun i => m-i)
          (hypergeomMass N k m) (m-d) ∧
      finiteFactorialBound (Finset.range (m+1)) (fun i => m-i)
          (hypergeomMass N k m) (m-d) ≤ Real.exp (-hypergeomKLRate N k m (d:ℝ)) ∧
      Real.exp (-hypergeomKLRate N k m (d:ℝ)) <
        Real.exp (-canonicalPiecewiseRate (N:ℝ) (k:ℝ) (m:ℝ) (d:ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨finiteIntegerTailMass_le_factorialBound s x w d hw,
      finiteFactorialBound_le_chernoff_inf s x w d hw⟩
  · intro N k m d hk hm hd hpositive
    have hdm : d ≤ m := by omega
    have hdk : d ≤ k := by omega
    have hformula : ∀ j : ℕ, j ≤ d →
        finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
            (hypergeomMass N k m) d j =
          ((Nat.descFactorial k j : ℝ) * (Nat.descFactorial m j : ℝ)) /
            ((Nat.descFactorial N j : ℝ) * (Nat.descFactorial d j : ℝ)) := by
      intro j hj
      exact hypergeom_factorial_candidate_formula N k m d j hk hm hdm hj
    refine ⟨hformula, ?_⟩
    intro j hj
    have hjN : j ≤ N := hj.trans (hdm.trans hm)
    constructor
    · exact_mod_cast (Nat.descFactorial_pos.mpr hjN)
    · exact_mod_cast (Nat.descFactorial_pos.mpr hj)
  · intro N k m d hm hmk hk hhalf hd hdmu
    have hkn : k ≤ N := by omega
    have hmn : m ≤ N := by omega
    have htail := finiteIntegerTailMass_le_factorialBound
      (Finset.range (m+1)) (fun i => i) (hypergeomMass N k m) d
      (fun i hi => hypergeomMass_nonneg N k m i)
    have hI := hypergeomFactorialBound_le_exp_neg_KLRate
      N k m d hm hmk hk hhalf hd hdmu
    have hstrictRate := hypergeomKLRate_strict_piecewise N k m hm hmk hk hhalf
      (d:ℝ) (by positivity) (by exact_mod_cast hd) (ne_of_gt hdmu)
    have hstrictExp := Real.exp_lt_exp.mpr (neg_lt_neg hstrictRate)
    have hJ := hypergeomFactorialBound_lt_exp_neg_piecewiseRate
      N k m d hm hmk hk hhalf hd hdmu
    exact ⟨htail, hI, hstrictExp, hJ⟩
  · intro N k m d hk hm hmd
    have hsupp : min k m < d := lt_of_le_of_lt (min_le_right k m) hmd
    exact hypergeom_factorial_chernoff_support_exterior_end_to_end N k m d hk hm hsupp
  · intro N k m d hm hmk hk hhalf hd hdmu
    exact hypergeom_lower_factorial_chernoff_end_to_end
      N k m d hm hmk hk hhalf hd hdmu

end
end ExactHoeffding
