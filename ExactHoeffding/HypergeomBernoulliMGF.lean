import ExactHoeffding.JacobiActualPGF
import ExactHoeffding.HypergeometricODE
import ExactHoeffding.Symmetries

namespace ExactHoeffding
noncomputable section

/-- An MGF identity for a deterministic shift plus independent Bernoulli
factors. The factors have strictly interior probabilities. -/
def HasShiftedBernoulliMGF (f : ℝ → ℝ) (t b : ℝ) (j : ℕ) : Prop :=
  ∃ p : Fin j → ℝ, (∀ i, p i ∈ Set.Ioo 0 1) ∧ ∀ u : ℝ,
    f (t + u) / f t = Real.exp (b * u) * ∏ i, (1 - p i + p i * Real.exp u)

theorem hypergeomMGF_eq_polynomial (N k m : ℕ) (t : ℝ) :
    hypergeomMGF N k m t = hypergeomPolynomial N k m (Real.exp t) /
      (Nat.choose N m : ℝ) := by
  unfold hypergeomMGF finiteMGF hypergeomMass hypergeomPolynomial
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm t (i : ℝ), Real.exp_nat_mul]
  ring

theorem jacobiHypergeom_tilted_bernoulli_mgf (j h r : ℕ) (t : ℝ) :
    HasShiftedBernoulliMGF
      (hypergeomMGF (jacobiN j h r) (jacobiK j) (jacobiM j h)) t 0 j := by
  obtain ⟨p, hp, hpgf⟩ := jacobiHypergeom_tilted_bernoulli_representation
    j h r (Real.exp_pos t)
  refine ⟨p, hp, ?_⟩
  intro u
  simp only [zero_mul, Real.exp_zero, one_mul]
  rw [hypergeomMGF_eq_polynomial, hypergeomMGF_eq_polynomial,
    div_div_div_cancel_right₀ (show (Nat.choose (jacobiN j h r) (jacobiM j h) : ℝ) ≠ 0 by
      exact_mod_cast Nat.choose_ne_zero (jacobi_m_le_N j h r)), Real.exp_add]
  exact hpgf (Real.exp u)

theorem hypergeom_tilted_bernoulli_mgf_canonical (N k m : ℕ)
    (hkm : k ≤ m) (hs : k + m ≤ N) (t : ℝ) :
    HasShiftedBernoulliMGF (hypergeomMGF N k m) t 0 k := by
  have hN : jacobiN k (m - k) (N - k - m) = N := by
    unfold jacobiN
    omega
  have hm : jacobiM k (m - k) = m := by unfold jacobiM; omega
  simpa only [hN, hm, jacobiK] using
    jacobiHypergeom_tilted_bernoulli_mgf k (m - k) (N - k - m) t

theorem shiftedBernoulliMGF_reflect {f g : ℝ → ℝ} {t a b : ℝ} {j : ℕ}
    (hf : ∀ s, f s = Real.exp (a * s) * g (-s))
    (hg : HasShiftedBernoulliMGF g (-t) b j) :
    HasShiftedBernoulliMGF f t (a - b - (j : ℝ)) j := by
  obtain ⟨p, hp, hprod⟩ := hg
  refine ⟨fun i => 1 - p i, ?_, ?_⟩
  · intro i
    exact ⟨sub_pos.mpr (hp i).2, by linarith [(hp i).1]⟩
  · intro u
    have heach (i : Fin j) : 1 - p i + p i * Real.exp (-u) =
        Real.exp (-u) * (1 - (1 - p i) + (1 - p i) * Real.exp u) := by
      rw [Real.exp_neg]
      field_simp [Real.exp_ne_zero u]
      ring
    have he : f (t + u) / f t =
        Real.exp (a * u) * (g ((-t) + (-u)) / g (-t)) := by
      rw [hf, hf, show a * (t + u) = a * t + a * u by ring, Real.exp_add]
      rw [show -(t + u) = (-t) + (-u) by ring]
      field_simp [Real.exp_ne_zero (a * t)]
    rw [he, hprod (-u)]
    simp_rw [heach]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← Real.exp_nat_mul]
    rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add]
    congr 2
    ring

theorem hypergeom_tilted_bernoulli_mgf_half (N k m : ℕ)
    (hk : 2 * k ≤ N) (hm : 2 * m ≤ N) (t : ℝ) :
    HasShiftedBernoulliMGF (hypergeomMGF N k m) t 0 (min k m) := by
  by_cases hkm : k ≤ m
  · rw [min_eq_left hkm]
    exact hypergeom_tilted_bernoulli_mgf_canonical N k m hkm (by omega) t
  · rw [min_eq_right (by omega : m ≤ k)]
    have he : hypergeomMGF N k m = hypergeomMGF N m k := by
      funext s
      exact hypergeomMGF_transpose N k m (by omega) (by omega) s
    rw [he]
    exact hypergeom_tilted_bernoulli_mgf_canonical N m k (by omega) (by omega) t

private theorem shiftedBernoulliMGF_sample_half (N k m : ℕ)
    (hk : k ≤ N) (hm : 2 * m ≤ N) (t : ℝ) :
    HasShiftedBernoulliMGF (hypergeomMGF N k m) t ((k + m - N : ℕ) : ℝ)
      (min (min k (N - k)) m) := by
  by_cases hh : 2 * k ≤ N
  · have hlow : k + m - N = 0 := by omega
    have hj : min (min k (N - k)) m = min k m := by omega
    rw [hlow, Nat.cast_zero, hj]
    exact hypergeom_tilted_bernoulli_mgf_half N k m hh hm t
  · have h := shiftedBernoulliMGF_reflect (a := (m : ℝ))
      (fun s => by simpa only [mul_comm (m : ℝ) s] using
        hypergeomMGF_success_complement N k m hk (by omega) s)
      (hypergeom_tilted_bernoulli_mgf_half N (N - k) m (by omega) hm (-t))
    have hj : min (min k (N - k)) m = min (N - k) m := by omega
    have hlow : m - min (N - k) m = k + m - N := by omega
    have hb : (m : ℝ) - 0 - (min (N - k) m : ℕ) = ((k + m - N : ℕ) : ℝ) := by
      rw [sub_zero, ← Nat.cast_sub (min_le_right _ _), hlow]
    rw [hb] at h
    rw [hj]
    exact h

/-- Every actual exponentially tilted hypergeometric MGF factors into a
deterministic lower-support shift and exactly its support width many
interior Bernoulli factors. No canonical-margin restriction remains. -/
theorem hypergeom_tilted_shifted_bernoulli_mgf (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    HasShiftedBernoulliMGF (hypergeomMGF N k m) t ((k + m - N : ℕ) : ℝ)
      (min (min k (N - k)) (min m (N - m))) := by
  by_cases hh : 2 * m ≤ N
  · have hj : min (min k (N - k)) (min m (N - m)) = min (min k (N - k)) m := by
      omega
    rw [hj]
    exact shiftedBernoulliMGF_sample_half N k m hk hh t
  · have h := shiftedBernoulliMGF_reflect (a := (k : ℝ))
      (fun s => by simpa only [mul_comm (k : ℝ) s] using
        hypergeomMGF_sample_complement N k m hk hm s)
      (shiftedBernoulliMGF_sample_half N k (N - m) hk (by omega) (-t))
    have hj : min (min k (N - k)) (min m (N - m)) = min (min k (N - k)) (N - m) := by
      omega
    have hwidth : (k + (N - m) - N) + min (min k (N - k)) (N - m) =
        min k (N - m) := by omega
    have hlow : k - min k (N - m) = k + m - N := by omega
    have hb : (k : ℝ) - ((k + (N - m) - N : ℕ) : ℝ) -
        (min (min k (N - k)) (N - m) : ℕ) = ((k + m - N : ℕ) : ℝ) := by
      rw [sub_sub, ← Nat.cast_add, hwidth,
        ← Nat.cast_sub (min_le_left _ _), hlow]
    rw [hb] at h
    rw [hj]
    exact h

theorem hypergeom_support_width (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) :
    min k m - (k + m - N) = min (min k (N - k)) (min m (N - m)) := by
  omega

end
end ExactHoeffding
