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

/-- Finite raw second tilted moments are differentiable at every real tilt. -/
theorem finiteTiltSecond_differentiableAt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ) (t : ℝ) :
    DifferentiableAt ℝ (finiteTiltSecond s weights values) t := by
  unfold finiteTiltSecond
  apply DifferentiableAt.fun_sum
  intro i hi
  exact ((((differentiableAt_id.mul_const (values i)).exp).const_mul
    (values i ^ 2)).const_mul (weights i))

/-- The actual tilted variance is differentiable, directly from finite sums. -/
theorem hypergeomTiltVariance_differentiableAt (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    DifferentiableAt ℝ (hypergeomTiltVariance N k m) t := by
  have hg := (finiteMGF_hasDerivAt (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ)) t).differentiableAt
  have hs := finiteTiltSecond_differentiableAt (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ)) t
  have hu := (hypergeomTiltMean_hasDerivAt N k m hk hm t).differentiableAt
  exact (hs.div hg (ne_of_gt (hypergeomMGF_pos N k m hk hm t))).sub (hu.pow 2)

/-- Differentiating the genuine adjacent balance once, keeping the equation
valid also at zero tilt and at variance stationary points. -/
theorem hypergeomTiltVariance_differential_balance (k m r : ℕ)
    (hmk : m ≤ k) (t : ℝ) :
    let u := hypergeomTiltMean (k + m + r) k m t
    let v := hypergeomTiltVariance (k + m + r) k m t
    let w := deriv (hypergeomTiltVariance (k + m + r) k m) t
    (2 * u + r) * v + w =
      Real.exp t * (((k : ℝ) - u) * ((m : ℝ) - u) + v) +
        Real.exp t * ((2 * u - k - m) * v + w) := by
  dsimp only
  let U := hypergeomTiltMean (k + m + r) k m
  let V := hypergeomTiltVariance (k + m + r) k m
  have hu : HasDerivAt U (V t) t :=
    hypergeomTiltMean_hasDerivAt (k + m + r) k m (by omega) (by omega) t
  have hv : HasDerivAt V (deriv V t) t :=
    (hypergeomTiltVariance_differentiableAt (k + m + r) k m
      (by omega) (by omega) t).hasDerivAt
  have hl : HasDerivAt (fun s => U s * (U s + (r : ℝ)) + V s)
      ((2 * U t + r) * V t + deriv V t) t := by
    exact ((hu.mul (hu.add_const (r : ℝ))).add hv).congr_deriv (by ring)
  have hk := ((hasDerivAt_const t (k : ℝ)).sub hu)
  have hm := ((hasDerivAt_const t (m : ℝ)).sub hu)
  have hr : HasDerivAt
      (fun s => Real.exp s * (((k : ℝ) - U s) * ((m : ℝ) - U s) + V s))
      (Real.exp t * (((k : ℝ) - U t) * ((m : ℝ) - U t) + V t) +
        Real.exp t * ((2 * U t - k - m) * V t + deriv V t)) t := by
    exact ((Real.hasDerivAt_exp t).mul ((hk.mul hm).add hv)).congr_deriv (by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring)
  have heq : (fun s => U s * (U s + (r : ℝ)) + V s) =
      (fun s => Real.exp s * (((k : ℝ) - U s) * ((m : ℝ) - U s) + V s)) := by
    funext s
    exact hypergeomTiltMeanVariance_balance k m r hmk s
  rw [heq] at hl
  exact hl.unique hr

/-- The stationary derivative equation needed by the algebraic curvature
certificate; its only extra hypothesis is actual derivative vanishing. -/
theorem hypergeomTiltVariance_stationary_balance (k m r : ℕ)
    (hmk : m ≤ k) (t : ℝ)
    (hw : deriv (hypergeomTiltVariance (k + m + r) k m) t = 0) :
    let u := hypergeomTiltMean (k + m + r) k m t
    let v := hypergeomTiltVariance (k + m + r) k m t
    Real.exp t * (((k : ℝ) - u) * ((m : ℝ) - u) -
      v * ((k : ℝ) + m - 2 * u - 1)) = v * ((r : ℝ) + 2 * u) := by
  have h := hypergeomTiltVariance_differential_balance k m r hmk t
  dsimp only at h ⊢
  rw [hw] at h
  nlinarith only [h]

/-- Eliminating the exponential tilt gives the denominator-free variance ODE.
Here the differentiated variance is with respect to the original tilt `t`. -/
theorem hypergeomTiltVariance_curve_identity (k m r : ℕ)
    (hmk : m ≤ k) (t : ℝ) :
    let u := hypergeomTiltMean (k + m + r) k m t
    let v := hypergeomTiltVariance (k + m + r) k m t
    let w := deriv (hypergeomTiltVariance (k + m + r) k m) t
    let A := u * (u + r)
    let C := ((k : ℝ) - u) * ((m : ℝ) - u)
    (C - A) * w =
      -((k : ℝ) + m + r - 1) * v ^ 2 +
        (A + C - (2 * u + r) * C + (2 * u - k - m) * A) * v + A * C := by
  have h₀ := hypergeomTiltMeanVariance_balance k m r hmk t
  have h₁ := hypergeomTiltVariance_differential_balance k m r hmk t
  dsimp only at h₁ ⊢
  let u := hypergeomTiltMean (k + m + r) k m t
  let v := hypergeomTiltVariance (k + m + r) k m t
  let w := deriv (hypergeomTiltVariance (k + m + r) k m) t
  change u * (u + r) + v =
    Real.exp t * (((k : ℝ) - u) * ((m : ℝ) - u) + v) at h₀
  change (2 * u + r) * v + w =
    Real.exp t * (((k : ℝ) - u) * ((m : ℝ) - u) + v) +
      Real.exp t * ((2 * u - k - m) * v + w) at h₁
  change (((k : ℝ) - u) * ((m : ℝ) - u) - u * (u + r)) * w = _
  linear_combination
    (((k : ℝ) - u) * ((m : ℝ) - u) + v) * h₁ -
      (((k : ℝ) - u) * ((m : ℝ) - u) + v +
        (2 * u - k - m) * v + w) * h₀

/-- Every mass in the stated canonical support is strictly positive. -/
theorem hypergeomMass_pos_canonical (k m r i : ℕ)
    (hmk : m ≤ k) (hi : i ≤ m) :
    0 < hypergeomMass (k + m + r) k m i := by
  have hn : k + m + r - k = m + r := by omega
  unfold hypergeomMass hypergeomCount
  rw [hn]
  apply div_pos
  · exact_mod_cast mul_pos (Nat.choose_pos (by omega : i ≤ k))
      (Nat.choose_pos (by omega : m - i ≤ m + r))
  · exact_mod_cast Nat.choose_pos (by omega : m ≤ k + m + r)

/-- A nondegenerate canonical tilted mean stays strictly above zero. -/
theorem hypergeomTiltMean_pos (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m)
    (t : ℝ) : 0 < hypergeomTiltMean (k + m + r) k m t := by
  apply div_pos
  · unfold finiteTiltFirst
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (hypergeomMass_nonneg _ _ _ _) (by positivity)
    · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
      have hmass := hypergeomMass_pos_canonical k m r 1 hmk (by omega)
      simpa using mul_pos hmass (Real.exp_pos t)
  · exact hypergeomMGF_pos (k + m + r) k m (by omega) (by omega) t

/-- A nondegenerate canonical tilted mean stays strictly below its support maximum. -/
theorem hypergeomTiltMean_lt (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m)
    (t : ℝ) : hypergeomTiltMean (k + m + r) k m t < (m : ℝ) := by
  have hg := hypergeomMGF_pos (k + m + r) k m (by omega) (by omega) t
  have hsum :
      (∑ i ∈ Finset.range (m + 1), hypergeomMass (k + m + r) k m i *
        (((m : ℝ) - i) * Real.exp (t * i))) =
      (m : ℝ) * hypergeomMGF (k + m + r) k m t -
        finiteTiltFirst (Finset.range (m + 1))
          (hypergeomMass (k + m + r) k m) (fun i => (i : ℝ)) t := by
    simp only [hypergeomMGF, finiteMGF, finiteTiltFirst, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hp : 0 <
      ∑ i ∈ Finset.range (m + 1), hypergeomMass (k + m + r) k m i *
        (((m : ℝ) - i) * Real.exp (t * i)) := by
    apply Finset.sum_pos'
    · intro i hi
      have hi' : (i : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_nonneg (hypergeomMass_nonneg _ _ _ _)
        (mul_nonneg (sub_nonneg.mpr hi') (le_of_lt (Real.exp_pos _)))
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      have hmass := hypergeomMass_pos_canonical k m r 0 hmk (by omega)
      have hm' : (0 : ℝ) < m := by exact_mod_cast hm
      simpa using mul_pos hmass hm'
  rw [hsum] at hp
  unfold hypergeomTiltMean
  exact (div_lt_iff₀ hg).mpr (by linarith)

/-- Tilted variance equals the actual expectation of the centered square. -/
theorem hypergeomTiltVariance_centered_square (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    hypergeomTiltExpectation N k m t
        (fun i => ((i : ℝ) - hypergeomTiltMean N k m t) ^ 2) =
      hypergeomTiltVariance N k m t := by
  let u := hypergeomTiltMean N k m t
  have hsum :
      (∑ i ∈ Finset.range (m + 1), hypergeomMass N k m i *
        (((i : ℝ) - u) ^ 2 * Real.exp (t * i))) =
      finiteTiltSecond (Finset.range (m + 1)) (hypergeomMass N k m)
          (fun i => (i : ℝ)) t -
        2 * u * finiteTiltFirst (Finset.range (m + 1)) (hypergeomMass N k m)
          (fun i => (i : ℝ)) t + u ^ 2 * hypergeomMGF N k m t := by
    simp only [finiteTiltSecond, finiteTiltFirst, hypergeomMGF, finiteMGF,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hg : hypergeomMGF N k m t ≠ 0 := ne_of_gt (hypergeomMGF_pos N k m hk hm t)
  unfold hypergeomTiltExpectation
  change (∑ i ∈ Finset.range (m + 1), hypergeomMass N k m i *
    (((i : ℝ) - u) ^ 2 * Real.exp (t * i))) / hypergeomMGF N k m t = _
  rw [hsum]
  dsimp [u, hypergeomTiltVariance, hypergeomTiltMean]
  field_simp [hg]
  ring

/-- Positive variance at every tilt follows from positive mass at zero and
a strictly positive tilted mean, without a root factorization hypothesis. -/
theorem hypergeomTiltVariance_pos (k m r : ℕ)
    (hmk : m ≤ k) (hm : 0 < m) (t : ℝ) :
    0 < hypergeomTiltVariance (k + m + r) k m t := by
  rw [← hypergeomTiltVariance_centered_square (k + m + r) k m
    (by omega) (by omega) t]
  unfold hypergeomTiltExpectation
  apply div_pos
  · apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (hypergeomMass_nonneg _ _ _ _) (by positivity)
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      have hu := hypergeomTiltMean_pos k m r hmk hm t
      have hmass := hypergeomMass_pos_canonical k m r 0 hmk (by omega)
      simpa using mul_pos hmass (sq_pos_of_pos hu)
  · exact hypergeomMGF_pos (k + m + r) k m (by omega) (by omega) t

/-- Both quadratic terms in the tilted balance have a positive denominator. -/
theorem hypergeomTiltMeanVariance_den_pos (k m r : ℕ)
    (hmk : m ≤ k) (hm : 0 < m) (t : ℝ) :
    0 < ((k : ℝ) - hypergeomTiltMean (k + m + r) k m t) *
      ((m : ℝ) - hypergeomTiltMean (k + m + r) k m t) +
      hypergeomTiltVariance (k + m + r) k m t := by
  have hu := hypergeomTiltMean_lt k m r hmk hm t
  have hv := hypergeomTiltVariance_pos k m r hmk hm t
  have hmk' : (m : ℝ) ≤ k := by exact_mod_cast hmk
  have hku : 0 < (k : ℝ) - hypergeomTiltMean (k + m + r) k m t := by linarith
  have hmu : 0 < (m : ℝ) - hypergeomTiltMean (k + m + r) k m t := by linarith
  exact add_pos (mul_pos hku hmu) hv

/-- The exact exponential-tilt ratio, with its denominator proved positive. -/
theorem hypergeomTiltExp_ratio (k m r : ℕ)
    (hmk : m ≤ k) (hm : 0 < m) (t : ℝ) :
    let u := hypergeomTiltMean (k + m + r) k m t
    let v := hypergeomTiltVariance (k + m + r) k m t
    Real.exp t = (u * (u + r) + v) /
      (((k : ℝ) - u) * ((m : ℝ) - u) + v) := by
  dsimp only
  apply (eq_div_iff (ne_of_gt (hypergeomTiltMeanVariance_den_pos k m r hmk hm t))).mpr
  exact (hypergeomTiltMeanVariance_balance k m r hmk t).symm

/-- The variance used by the recurrence is precisely log-MGF curvature. -/
theorem hypergeomLogMGF_second_deriv_eq_variance (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    deriv (deriv (fun s => Real.log (hypergeomMGF N k m s))) t =
      hypergeomTiltVariance N k m t := by
  have hfirst : deriv (fun s => Real.log (hypergeomMGF N k m s)) =
      hypergeomTiltMean N k m := by
    funext s
    exact (finiteLogMGF_hasDerivAt (Finset.range (m + 1))
      (hypergeomMass N k m) (fun i => (i : ℝ))
      (fun i _ => hypergeomMass_nonneg N k m i)
      (hypergeomMass_total N k m hk hm) s).deriv
  rw [hfirst]
  exact (hypergeomTiltMean_hasDerivAt N k m hk hm t).deriv

end ExactHoeffding
