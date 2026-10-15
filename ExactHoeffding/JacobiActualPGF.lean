import ExactHoeffding.JacobiFactorization
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin

namespace ExactHoeffding

theorem jacobiHypergeomScale_pos (j h r : ℕ) :
    0 < jacobiHypergeomScale j h r := by
  unfold jacobiHypergeomScale
  apply div_pos
  · apply mul_pos <;> exact_mod_cast Nat.factorial_pos _
  · exact_mod_cast Nat.factorial_pos (j + h + r)

theorem jacobiHypergeomPolynomial_pos_of_nonneg (j h r : ℕ) {z : ℝ}
    (hz : 0 ≤ z) :
    0 < hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) z := by
  have hp := jacobiPGF_eval_pos_of_nonneg j h r hz
  rw [jacobiPGF_eval_eq_scaled_hypergeomPolynomial] at hp
  by_contra hnot
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos
    (jacobiHypergeomScale_pos j h r).le (le_of_not_gt hnot))) hp

/-- Zeros of the existing hypergeometric generating function are negative. -/
theorem jacobiHypergeomPolynomial_zero_negative (j h r : ℕ) {x : ℝ}
    (hx : hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) x = 0) :
    x < 0 := by
  apply jacobiPGF_roots_negative j h r
  apply (Polynomial.mem_roots (jacobiPGF_ne_zero j h r)).2
  change (jacobiPGF j h r).eval x = 0
  rw [jacobiPGF_eval_eq_scaled_hypergeomPolynomial, hx, mul_zero]

/-- The actual hypergeometric PGF has the same normalized root product. -/
theorem jacobiHypergeomPolynomial_root_factorization (j h r : ℕ) (w : ℝ) :
    hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) w =
      hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) 0 *
        (((jacobiPGF j h r).roots.map
          (fun x => (jacobiRootNormalizedFactor x).eval w)).prod) := by
  have hf := congrArg (fun p : Polynomial ℝ => p.eval w)
    (jacobiPGF_root_normalized_factorization j h r)
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_multiset_prod,
    Multiset.map_map, Function.comp_apply] at hf
  rw [jacobiPGF_eval_eq_scaled_hypergeomPolynomial,
    jacobiPGF_eval_eq_scaled_hypergeomPolynomial] at hf
  apply mul_left_cancel₀ (ne_of_gt (jacobiHypergeomScale_pos j h r))
  simpa only [mul_assoc] using hf

theorem jacobiHypergeomPolynomial_tilted_bernoulli_pgf (j h r : ℕ)
    {z : ℝ} (hz : 0 < z) (y : ℝ) :
    hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) (z * y) /
        hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) z =
      (((jacobiPGF j h r).roots.map
        (fun x => jacobiTiltedRootPGFFactor z x y)).prod) := by
  have hf := jacobiPGF_tilted_bernoulli_pgF j h r hz y
  rw [jacobiPGF_eval_eq_scaled_hypergeomPolynomial,
    jacobiPGF_eval_eq_scaled_hypergeomPolynomial] at hf
  simpa only [mul_div_mul_left _ _
    (ne_of_gt (jacobiHypergeomScale_pos j h r))] using hf

/-- Exactly `j` interior Bernoulli parameters represent the actual tilted PGF. -/
theorem jacobiHypergeom_tilted_bernoulli_representation (j h r : ℕ)
    {z : ℝ} (hz : 0 < z) :
    ∃ p : Fin j → ℝ, (∀ i, p i ∈ Set.Ioo 0 1) ∧
      ∀ y : ℝ,
        hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) (z * y) /
            hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) z =
          ∏ i, (1 - p i + p i * y) := by
  classical
  let roots := (jacobiPGF j h r).roots.toList
  have hlen : roots.length = j := by
    dsimp [roots]
    rw [Multiset.length_toList, jacobiPGF_roots_card]
  have hrep :
      ∃ p : Fin roots.length → ℝ, (∀ i, p i ∈ Set.Ioo 0 1) ∧
        ∀ y : ℝ,
          hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) (z * y) /
              hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) z =
            ∏ i, (1 - p i + p i * y) := by
    refine ⟨fun i => jacobiTiltedRootProbability z (roots.get i), ?_, ?_⟩
    · intro i
      apply jacobiTiltedRootProbability_mem_Ioo hz
      apply jacobiPGF_roots_negative j h r
      exact Multiset.mem_toList.mp (List.get_mem roots i)
    · intro y
      have hprod :
          (roots.map (fun x => jacobiTiltedRootPGFFactor z x y)).prod =
            ∏ i : Fin roots.length, jacobiTiltedRootPGFFactor z (roots.get i) y := by
        simpa only [List.get_eq_getElem] using
          (Fin.prod_univ_fun_getElem roots
            (fun x => jacobiTiltedRootPGFFactor z x y)).symm
      calc
        _ = (((jacobiPGF j h r).roots.map
            (fun x => jacobiTiltedRootPGFFactor z x y)).prod) :=
              jacobiHypergeomPolynomial_tilted_bernoulli_pgf j h r hz y
        _ = (roots.map (fun x => jacobiTiltedRootPGFFactor z x y)).prod :=
              (Multiset.prod_map_toList _ _).symm
        _ = _ := hprod
  rcases hrep with ⟨p, hp, hpgf⟩
  refine ⟨fun i => p (i.cast hlen.symm), ?_, ?_⟩
  · intro i
    exact hp (i.cast hlen.symm)
  · intro y
    rw [hpgf y]
    exact (Fin.prod_congr'
      (fun i : Fin roots.length => 1 - p i + p i * y) hlen.symm).symm

/-- The coefficient sum uses the original hypergeometric counts, not an
auxiliary Rodrigues polynomial or a factorization assumption. -/
theorem jacobiHypergeom_tilted_mass_pgf (j h r : ℕ) {z : ℝ} (hz : 0 < z) :
    ∃ p : Fin j → ℝ, (∀ i, p i ∈ Set.Ioo 0 1) ∧
      ∀ y : ℝ,
        (∑ i ∈ Finset.range (jacobiM j h + 1),
          ((hypergeomCount (jacobiN j h r) (jacobiK j) (jacobiM j h) i : ℝ) * z ^ i /
            hypergeomPolynomial (jacobiN j h r) (jacobiK j) (jacobiM j h) z) * y ^ i) =
          ∏ i, (1 - p i + p i * y) := by
  rcases jacobiHypergeom_tilted_bernoulli_representation j h r hz with ⟨p, hp, hpgf⟩
  refine ⟨p, hp, ?_⟩
  intro y
  rw [← hpgf y]
  unfold hypergeomPolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  ring

#print axioms jacobiHypergeomPolynomial_zero_negative
#print axioms jacobiHypergeomPolynomial_root_factorization
#print axioms jacobiHypergeomPolynomial_tilted_bernoulli_pgf
#print axioms jacobiHypergeom_tilted_bernoulli_representation
#print axioms jacobiHypergeom_tilted_mass_pgf

end ExactHoeffding
