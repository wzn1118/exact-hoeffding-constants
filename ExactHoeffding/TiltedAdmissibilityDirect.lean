import ExactHoeffding.HypergeometricODE
import ExactHoeffding.CrossSum

/-!
# Direct hypergeometric tilted mean-variance admissibility

The adjacent coefficient recurrence proves the Poisson-binomial-shaped
variance bound directly, without assuming or using polynomial factorization.
-/

namespace ExactHoeffding

noncomputable def hypergeomTiltUp (k m r : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  ((i : ℝ) + 1) * hypergeomMass (k + m + r) k m (i + 1) *
    Real.exp (t * ((i + 1 : ℕ) : ℝ))

noncomputable def hypergeomTiltDown (k m r : ℕ) (t : ℝ) (i : ℕ) : ℝ :=
  ((m : ℝ) - i) * hypergeomMass (k + m + r) k m i * Real.exp (t * i)

theorem hypergeomTiltUpDown_balance (k m r i : ℕ) (hmk : m ≤ k)
    (hi : i < m) (t : ℝ) :
    ((i : ℝ) + 1 + r) * hypergeomTiltUp k m r t i =
      Real.exp t * ((k : ℝ) - i) * hypergeomTiltDown k m r t i := by
  have h := hypergeomMass_tilted_adjacent k m r i hmk hi t
  push_cast at h
  unfold hypergeomTiltUp hypergeomTiltDown
  push_cast
  nlinarith only [h]

theorem hypergeomTiltDown_nonneg (k m r i : ℕ) (hi : i ≤ m) (t : ℝ) :
    0 ≤ hypergeomTiltDown k m r t i := by
  have hi' : (i : ℝ) ≤ m := by exact_mod_cast hi
  unfold hypergeomTiltDown
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hi')
    (hypergeomMass_nonneg _ _ _ _)) (le_of_lt (Real.exp_pos _))

/-- The exact cross-product identity for the tilted upward and downward weights. -/
theorem hypergeomTiltUpDown_cross (k m r i j : ℕ) (hmk : m ≤ k)
    (hi : i < m) (hj : j < m) (t : ℝ) :
    ((i : ℝ) + 1 + r) * ((j : ℝ) + 1 + r) *
      (hypergeomTiltUp k m r t i * hypergeomTiltDown k m r t j -
        hypergeomTiltUp k m r t j * hypergeomTiltDown k m r t i) =
      Real.exp t * ((k : ℝ) + r + 1) * ((j : ℝ) - i) *
        hypergeomTiltDown k m r t i * hypergeomTiltDown k m r t j := by
  have hᵢ := hypergeomTiltUpDown_balance k m r i hmk hi t
  have hⱼ := hypergeomTiltUpDown_balance k m r j hmk hj t
  linear_combination
    (((j : ℝ) + 1 + r) * hypergeomTiltDown k m r t j) * hᵢ -
      (((i : ℝ) + 1 + r) * hypergeomTiltDown k m r t i) * hⱼ

theorem hypergeomTiltUpDown_cross_order (k m r i j : ℕ) (hmk : m ≤ k)
    (hi : i < m) (hj : j < m) (t : ℝ) :
    ((i : ℝ) - j) *
      (hypergeomTiltUp k m r t i * hypergeomTiltDown k m r t j -
        hypergeomTiltUp k m r t j * hypergeomTiltDown k m r t i) ≤ 0 := by
  have h := hypergeomTiltUpDown_cross k m r i j hmk hi hj t
  have hbᵢ := hypergeomTiltDown_nonneg k m r i (Nat.le_of_lt hi) t
  have hbⱼ := hypergeomTiltDown_nonneg k m r j (Nat.le_of_lt hj) t
  have hc : 0 ≤ Real.exp t * ((k : ℝ) + r + 1) *
      hypergeomTiltDown k m r t i * hypergeomTiltDown k m r t j := by positivity
  have hden : 0 < ((i : ℝ) + 1 + r) * ((j : ℝ) + 1 + r) := by positivity
  have hprod : ((i : ℝ) + 1 + r) * ((j : ℝ) + 1 + r) *
      (((i : ℝ) - j) *
        (hypergeomTiltUp k m r t i * hypergeomTiltDown k m r t j -
          hypergeomTiltUp k m r t j * hypergeomTiltDown k m r t i)) =
      -(Real.exp t * ((k : ℝ) + r + 1) *
        hypergeomTiltDown k m r t i * hypergeomTiltDown k m r t j) *
          ((i : ℝ) - j) ^ 2 := by
    linear_combination ((i : ℝ) - j) * h
  have hnonpos : ((i : ℝ) + 1 + r) * ((j : ℝ) + 1 + r) *
      (((i : ℝ) - j) *
        (hypergeomTiltUp k m r t i * hypergeomTiltDown k m r t j -
          hypergeomTiltUp k m r t j * hypergeomTiltDown k m r t i)) ≤ 0 := by
    rw [hprod]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg _)
  by_contra hpositive
  have hpos := mul_pos hden (lt_of_not_ge hpositive)
  linarith

theorem hypergeomTiltUp_sum (k m r : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range m, hypergeomTiltUp k m r t i) =
      finiteTiltFirst (Finset.range (m + 1)) (hypergeomMass (k + m + r) k m)
        (fun i => (i : ℝ)) t := by
  unfold finiteTiltFirst
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  unfold hypergeomTiltUp
  push_cast
  ring

theorem hypergeomTiltUp_first (k m r : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range m, (i : ℝ) * hypergeomTiltUp k m r t i) =
      finiteTiltSecond (Finset.range (m + 1)) (hypergeomMass (k + m + r) k m)
          (fun i => (i : ℝ)) t -
        finiteTiltFirst (Finset.range (m + 1)) (hypergeomMass (k + m + r) k m)
          (fun i => (i : ℝ)) t := by
  simp only [finiteTiltSecond, finiteTiltFirst, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero,
    Real.exp_zero, zero_mul, sub_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  unfold hypergeomTiltUp
  push_cast
  ring

theorem hypergeomTiltDown_sum (k m r : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range m, hypergeomTiltDown k m r t i) =
      (m : ℝ) * hypergeomMGF (k + m + r) k m t -
        finiteTiltFirst (Finset.range (m + 1)) (hypergeomMass (k + m + r) k m)
          (fun i => (i : ℝ)) t := by
  calc
    _ = ∑ i ∈ Finset.range (m + 1), hypergeomTiltDown k m r t i := by
      rw [Finset.sum_range_succ]
      simp [hypergeomTiltDown]
    _ = _ := by
      simp only [hypergeomMGF, finiteMGF, finiteTiltFirst,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      unfold hypergeomTiltDown
      ring

theorem hypergeomTiltDown_first (k m r : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range m, (i : ℝ) * hypergeomTiltDown k m r t i) =
      (m : ℝ) * finiteTiltFirst (Finset.range (m + 1))
          (hypergeomMass (k + m + r) k m) (fun i => (i : ℝ)) t -
        finiteTiltSecond (Finset.range (m + 1)) (hypergeomMass (k + m + r) k m)
          (fun i => (i : ℝ)) t := by
  calc
    _ = ∑ i ∈ Finset.range (m + 1), (i : ℝ) * hypergeomTiltDown k m r t i := by
      rw [Finset.sum_range_succ]
      simp [hypergeomTiltDown]
    _ = _ := by
      simp only [finiteTiltSecond, finiteTiltFirst,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      unfold hypergeomTiltDown
      ring

/-- The actual tilted variance obeys the degree-`m` mean-variance bound,
proved directly from adjacent hypergeometric counts. -/
theorem hypergeomTiltVariance_admissible (k m r : ℕ)
    (hmk : m ≤ k) (hm : 0 < m) (t : ℝ) :
    hypergeomTiltVariance (k + m + r) k m t ≤
      hypergeomTiltMean (k + m + r) k m t *
        ((m : ℝ) - hypergeomTiltMean (k + m + r) k m t) / m := by
  have h := cross_sum_order (Finset.range m) (fun i => (i : ℝ))
    (hypergeomTiltUp k m r t) (hypergeomTiltDown k m r t) (by
      intro i hi j hj
      exact hypergeomTiltUpDown_cross_order k m r i j hmk
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) t)
  rw [hypergeomTiltUp_first, hypergeomTiltDown_sum,
    hypergeomTiltDown_first, hypergeomTiltUp_sum] at h
  have hg := hypergeomMGF_pos (k + m + r) k m (by omega) (by omega) t
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply (le_div_iff₀ hm').mpr
  unfold hypergeomTiltVariance hypergeomTiltMean
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hg)).mp
  field_simp [ne_of_gt hg]
  nlinarith only [h]

/-- The direct admissibility estimate in the original population parameters. -/
theorem hypergeomTiltVariance_admissible_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hm : 0 < m) (t : ℝ) :
    hypergeomTiltVariance N k m t ≤
      hypergeomTiltMean N k m t * ((m : ℝ) - hypergeomTiltMean N k m t) / m := by
  have hn : k + m + (N - (k + m)) = N := Nat.add_sub_of_le hkm
  simpa only [hn] using hypergeomTiltVariance_admissible k m (N - (k + m)) hmk hm t

/-- Direct admissibility for the second logarithmic MGF derivative. -/
theorem hypergeomLogMGF_second_deriv_admissible (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hm : 0 < m) (t : ℝ) :
    deriv (deriv (fun s => Real.log (hypergeomMGF N k m s))) t ≤
      hypergeomTiltMean N k m t * ((m : ℝ) - hypergeomTiltMean N k m t) / m := by
  rw [hypergeomLogMGF_second_deriv_eq_variance N k m (by omega) (by omega) t]
  exact hypergeomTiltVariance_admissible_of_margins N k m hmk hkm hm t

end ExactHoeffding
