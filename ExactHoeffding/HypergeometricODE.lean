import ExactHoeffding.TiltedVariance
import Mathlib.Tactic.LinearCombination

/-!
# Hypergeometric adjacent-mass and Riccati identities

The recurrence is derived from the actual binomial-count weights. Every sum
uses the support `range (m + 1)`, including its vanishing boundary factors.
-/

namespace ExactHoeffding

/-- Adjacent hypergeometric counts, in the non-truncated population form. -/
theorem hypergeomCount_adjacent (k m r i : ℕ) (hi : i < m) :
    (i + 1) * (i + 1 + r) * hypergeomCount (k + m + r) k m (i + 1) =
      (k - i) * (m - i) * hypergeomCount (k + m + r) k m i := by
  have hn : k + m + r - k = m + r := by omega
  have hs : m - (i + 1) + 1 = m - i := by omega
  have ht : m + r - (m - (i + 1)) = i + 1 + r := by omega
  have hc := Nat.choose_succ_right_eq k i
  have hd := (Nat.choose_succ_right_eq (m + r) (m - (i + 1))).symm
  rw [hs, ht] at hd
  simp only [hypergeomCount, hn]
  calc
    _ = (Nat.choose k (i + 1) * (i + 1)) *
        (Nat.choose (m + r) (m - (i + 1)) * (i + 1 + r)) := by ring
    _ = (Nat.choose k i * (k - i)) *
        (Nat.choose (m + r) (m - i) * (m - i)) := by rw [hc, hd]
    _ = _ := by ring

/-- The same recurrence in real arithmetic, on its explicit support. -/
theorem hypergeomCount_adjacent_real (k m r i : ℕ)
    (hmk : m ≤ k) (hi : i < m) :
    ((i : ℝ) + 1) * ((i : ℝ) + 1 + r) *
        (hypergeomCount (k + m + r) k m (i + 1) : ℝ) =
      ((k : ℝ) - i) * ((m : ℝ) - i) *
        (hypergeomCount (k + m + r) k m i : ℝ) := by
  have hki : i ≤ k := le_trans (Nat.le_of_lt hi) hmk
  have hmi : i ≤ m := Nat.le_of_lt hi
  have h := congrArg (fun n : ℕ => (n : ℝ))
    (hypergeomCount_adjacent k m r i hi)
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub hki, Nat.cast_sub hmi] using h

/-- Dividing by the common counting denominator preserves adjacent balance. -/
theorem hypergeomMass_adjacent_real (k m r i : ℕ)
    (hmk : m ≤ k) (hi : i < m) :
    ((i : ℝ) + 1) * ((i : ℝ) + 1 + r) *
        hypergeomMass (k + m + r) k m (i + 1) =
      ((k : ℝ) - i) * ((m : ℝ) - i) *
        hypergeomMass (k + m + r) k m i := by
  unfold hypergeomMass
  simpa only [mul_div_assoc] using
    congrArg (fun x : ℝ => x / (Nat.choose (k + m + r) m : ℝ))
      (hypergeomCount_adjacent_real k m r i hmk hi)

/-- Adjacent balance after an arbitrary real exponential tilt. -/
theorem hypergeomMass_tilted_adjacent (k m r i : ℕ)
    (hmk : m ≤ k) (hi : i < m) (t : ℝ) :
    hypergeomMass (k + m + r) k m (i + 1) *
        (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + r) *
          Real.exp (t * ((i + 1 : ℕ) : ℝ))) =
      Real.exp t * (hypergeomMass (k + m + r) k m i *
        (((k : ℝ) - i) * ((m : ℝ) - i) * Real.exp (t * i))) := by
  have h := hypergeomMass_adjacent_real k m r i hmk hi
  push_cast
  rw [show t * ((i : ℝ) + 1) = t * i + t by ring, Real.exp_add]
  calc
    _ = (((i : ℝ) + 1) * ((i : ℝ) + 1 + r) *
        hypergeomMass (k + m + r) k m (i + 1)) *
        Real.exp (t * i) * Real.exp t := by ring
    _ = (((k : ℝ) - i) * ((m : ℝ) - i) *
        hypergeomMass (k + m + r) k m i) *
        Real.exp (t * i) * Real.exp t := by rw [h]
    _ = _ := by ring

/-- The adjacent-mass recurrence summed over exactly `0,...,m`.
The initial term on the left and the final term on the right vanish. -/
theorem hypergeomMass_tilted_balance (k m r : ℕ) (hmk : m ≤ k) (t : ℝ) :
    (∑ i ∈ Finset.range (m + 1), hypergeomMass (k + m + r) k m i *
      ((i : ℝ) * ((i : ℝ) + r) * Real.exp (t * i))) =
    Real.exp t * (∑ i ∈ Finset.range (m + 1),
      hypergeomMass (k + m + r) k m i *
        (((k : ℝ) - i) * ((m : ℝ) - i) * Real.exp (t * i))) := by
  calc
    _ = ∑ i ∈ Finset.range m, hypergeomMass (k + m + r) k m (i + 1) *
        (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + r) *
          Real.exp (t * ((i + 1 : ℕ) : ℝ))) := by
      rw [Finset.sum_range_succ']
      simp
    _ = Real.exp t * (∑ i ∈ Finset.range m,
        hypergeomMass (k + m + r) k m i *
          (((k : ℝ) - i) * ((m : ℝ) - i) * Real.exp (t * i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact hypergeomMass_tilted_adjacent k m r i hmk (Finset.mem_range.mp hi) t
    _ = _ := by rw [Finset.sum_range_succ]; simp

/-- Expectation under the normalized exponential tilt of the actual law. -/
noncomputable def hypergeomTiltExpectation (N k m : ℕ) (t : ℝ)
    (f : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (m + 1),
    hypergeomMass N k m i * (f i * Real.exp (t * i))) / hypergeomMGF N k m t

/-- The mean of the exponentially tilted hypergeometric law. -/
noncomputable def hypergeomTiltMean (N k m : ℕ) (t : ℝ) : ℝ :=
  finiteTiltFirst (Finset.range (m + 1)) (hypergeomMass N k m)
    (fun i => (i : ℝ)) t / hypergeomMGF N k m t

/-- The variance of the exponentially tilted hypergeometric law. -/
noncomputable def hypergeomTiltVariance (N k m : ℕ) (t : ℝ) : ℝ :=
  finiteTiltSecond (Finset.range (m + 1)) (hypergeomMass N k m)
    (fun i => (i : ℝ)) t / hypergeomMGF N k m t -
    (hypergeomTiltMean N k m t) ^ 2

/-- The exact normalized adjacent-mass expectation identity. -/
theorem hypergeomTiltExpectation_balance (k m r : ℕ) (hmk : m ≤ k) (t : ℝ) :
    hypergeomTiltExpectation (k + m + r) k m t (fun i => (i : ℝ) * (i + r)) =
      Real.exp t * hypergeomTiltExpectation (k + m + r) k m t
        (fun i => ((k : ℝ) - i) * ((m : ℝ) - i)) := by
  unfold hypergeomTiltExpectation
  rw [hypergeomMass_tilted_balance k m r hmk t]
  ring

/-- The same finite recurrence written using the three raw tilted moments. -/
theorem hypergeomTiltMoments_balance (k m r : ℕ) (hmk : m ≤ k) (t : ℝ) :
    finiteTiltSecond (Finset.range (m + 1)) (hypergeomMass (k + m + r) k m)
        (fun i => (i : ℝ)) t +
      (r : ℝ) * finiteTiltFirst (Finset.range (m + 1))
        (hypergeomMass (k + m + r) k m) (fun i => (i : ℝ)) t =
    Real.exp t *
      (finiteTiltSecond (Finset.range (m + 1)) (hypergeomMass (k + m + r) k m)
          (fun i => (i : ℝ)) t -
        ((k : ℝ) + m) * finiteTiltFirst (Finset.range (m + 1))
          (hypergeomMass (k + m + r) k m) (fun i => (i : ℝ)) t +
        (k : ℝ) * m * hypergeomMGF (k + m + r) k m t) := by
  have hl :
      (∑ i ∈ Finset.range (m + 1), hypergeomMass (k + m + r) k m i *
        ((i : ℝ) * ((i : ℝ) + r) * Real.exp (t * i))) =
      finiteTiltSecond (Finset.range (m + 1)) (hypergeomMass (k + m + r) k m)
          (fun i => (i : ℝ)) t +
        (r : ℝ) * finiteTiltFirst (Finset.range (m + 1))
          (hypergeomMass (k + m + r) k m) (fun i => (i : ℝ)) t := by
    simp only [finiteTiltSecond, finiteTiltFirst, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hr :
      (∑ i ∈ Finset.range (m + 1), hypergeomMass (k + m + r) k m i *
        (((k : ℝ) - i) * ((m : ℝ) - i) * Real.exp (t * i))) =
      finiteTiltSecond (Finset.range (m + 1)) (hypergeomMass (k + m + r) k m)
          (fun i => (i : ℝ)) t -
        ((k : ℝ) + m) * finiteTiltFirst (Finset.range (m + 1))
          (hypergeomMass (k + m + r) k m) (fun i => (i : ℝ)) t +
        (k : ℝ) * m * hypergeomMGF (k + m + r) k m t := by
    simp only [finiteTiltSecond, finiteTiltFirst, hypergeomMGF, finiteMGF,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [← hl, ← hr]
  exact hypergeomMass_tilted_balance k m r hmk t

/-- Every valid hypergeometric exponential moment is strictly positive. -/
theorem hypergeomMGF_pos (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    0 < hypergeomMGF N k m t := by
  exact finiteMGF_pos_of_normalized (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i)
    (hypergeomMass_total N k m hk hm) t

/-- The derivative of the actual tilted mean is the actual tilted variance. -/
theorem hypergeomTiltMean_hasDerivAt (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    HasDerivAt (hypergeomTiltMean N k m) (hypergeomTiltVariance N k m t) t := by
  have hg : hypergeomMGF N k m t ≠ 0 := ne_of_gt (hypergeomMGF_pos N k m hk hm t)
  have heq : hypergeomTiltVariance N k m t =
      (finiteTiltSecond (Finset.range (m + 1)) (hypergeomMass N k m)
          (fun i => (i : ℝ)) t * hypergeomMGF N k m t -
        finiteTiltFirst (Finset.range (m + 1)) (hypergeomMass N k m)
          (fun i => (i : ℝ)) t *
        finiteTiltFirst (Finset.range (m + 1)) (hypergeomMass N k m)
          (fun i => (i : ℝ)) t) / (hypergeomMGF N k m t) ^ 2 := by
    unfold hypergeomTiltVariance hypergeomTiltMean
    field_simp [hg]
  rw [heq]
  exact finiteTiltedMean_hasDerivAt (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i)
    (hypergeomMass_total N k m hk hm) t

/-- The adjacent recurrence as a mean-variance identity, with no division
by a quadratic coefficient or by `exp t - 1`. -/
theorem hypergeomTiltMeanVariance_balance (k m r : ℕ) (hmk : m ≤ k) (t : ℝ) :
    hypergeomTiltMean (k + m + r) k m t *
        (hypergeomTiltMean (k + m + r) k m t + r) +
      hypergeomTiltVariance (k + m + r) k m t =
    Real.exp t *
      (((k : ℝ) - hypergeomTiltMean (k + m + r) k m t) *
        ((m : ℝ) - hypergeomTiltMean (k + m + r) k m t) +
        hypergeomTiltVariance (k + m + r) k m t) := by
  have hg : hypergeomMGF (k + m + r) k m t ≠ 0 :=
    ne_of_gt (hypergeomMGF_pos (k + m + r) k m (by omega) (by omega) t)
  have h := congrArg (fun x : ℝ => x / hypergeomMGF (k + m + r) k m t)
    (hypergeomTiltMoments_balance k m r hmk t)
  simp only [add_div, sub_div, mul_div_assoc, div_self hg] at h
  unfold hypergeomTiltVariance hypergeomTiltMean
  nlinarith only [h]

/-- The Riccati equation for the hypergeometric tilted mean, derived from
its combinatorial weights and finite exponential-sum differentiation. -/
theorem hypergeomTiltMean_riccati (k m r : ℕ) (hmk : m ≤ k) (t : ℝ) :
    (1 - Real.exp t) * deriv (hypergeomTiltMean (k + m + r) k m) t +
      (1 - Real.exp t) * (hypergeomTiltMean (k + m + r) k m t) ^ 2 +
      ((r : ℝ) + Real.exp t * ((k : ℝ) + m)) *
        hypergeomTiltMean (k + m + r) k m t -
      Real.exp t * (k : ℝ) * m = 0 := by
  rw [(hypergeomTiltMean_hasDerivAt (k + m + r) k m
    (by omega) (by omega) t).deriv]
  nlinarith only [hypergeomTiltMeanVariance_balance k m r hmk t]

/-- Mean-variance balance with the original population parameter `N`. -/
theorem hypergeomTiltMeanVariance_balance_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (t : ℝ) :
    hypergeomTiltMean N k m t *
        (hypergeomTiltMean N k m t + (N : ℝ) - k - m) +
      hypergeomTiltVariance N k m t =
    Real.exp t *
      (((k : ℝ) - hypergeomTiltMean N k m t) *
        ((m : ℝ) - hypergeomTiltMean N k m t) +
        hypergeomTiltVariance N k m t) := by
  have hn : k + m + (N - (k + m)) = N := Nat.add_sub_of_le hkm
  have hr : ((N - (k + m) : ℕ) : ℝ) = (N : ℝ) - k - m := by
    rw [Nat.cast_sub hkm, Nat.cast_add]
    ring
  have h := hypergeomTiltMeanVariance_balance k m (N - (k + m)) hmk t
  rw [hn, hr] at h
  convert h using 1
  ring

/-- The population-parameter form of the genuine tilted-mean Riccati equation. -/
theorem hypergeomTiltMean_riccati_of_margins (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (t : ℝ) :
    (1 - Real.exp t) * deriv (hypergeomTiltMean N k m) t +
      (1 - Real.exp t) * (hypergeomTiltMean N k m t) ^ 2 +
      ((N : ℝ) - k - m + Real.exp t * ((k : ℝ) + m)) *
        hypergeomTiltMean N k m t - Real.exp t * (k : ℝ) * m = 0 := by
  rw [(hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).deriv]
  nlinarith only [hypergeomTiltMeanVariance_balance_of_margins N k m hmk hkm t]

end ExactHoeffding
