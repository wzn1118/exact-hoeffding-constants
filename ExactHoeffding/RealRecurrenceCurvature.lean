import ExactHoeffding.CanonicalCurvature
import ExactHoeffding.CurvatureNonnegative
import ExactHoeffding.StrictUniformLaplace

/-! # Sharp curvature for positive real-parameter recurrence laws

The coefficients are arbitrary positive normalized finite weights satisfying
the hypergeometric adjacent recurrence with real marks and remainder.
-/

namespace ExactHoeffding

structure RealRecurrenceLaw where
  degree : ℕ
  marks : ℝ
  remainder : ℝ
  mass : ℕ → ℝ
  marks_ge : (degree : ℝ) ≤ marks
  remainder_nonneg : 0 ≤ remainder
  mass_pos : ∀ i, i ≤ degree → 0 < mass i
  mass_total : ∑ i ∈ Finset.range (degree + 1), mass i = 1
  adjacent : ∀ i, i < degree →
    ((i : ℝ) + 1) * ((i : ℝ) + 1 + remainder) * mass (i + 1) =
      (marks - i) * ((degree : ℝ) - i) * mass i


noncomputable section

open Filter
open scoped Topology

def RealRecurrenceLaw.mgf (L : RealRecurrenceLaw) (t : ℝ) : ℝ :=
  finiteMGF (Finset.range (L.degree + 1)) L.mass (fun i => (i : ℝ)) t

def RealRecurrenceLaw.mean (L : RealRecurrenceLaw) (t : ℝ) : ℝ :=
  finiteTiltFirst (Finset.range (L.degree + 1)) L.mass (fun i => (i : ℝ)) t / L.mgf t

def RealRecurrenceLaw.variance (L : RealRecurrenceLaw) (t : ℝ) : ℝ :=
  finiteTiltSecond (Finset.range (L.degree + 1)) L.mass (fun i => (i : ℝ)) t / L.mgf t -
    (L.mean t) ^ 2

def RealRecurrenceLaw.expectation (L : RealRecurrenceLaw) (t : ℝ) (g : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (L.degree + 1), L.mass i * (g i * Real.exp (t * i))) / L.mgf t

theorem RealRecurrenceLaw.mass_nonneg (L : RealRecurrenceLaw) (i : ℕ) (hi : i ∈ Finset.range (L.degree + 1)) :
    0 ≤ L.mass i := (L.mass_pos i (by have := Finset.mem_range.mp hi; omega)).le

theorem RealRecurrenceLaw.mgf_pos (L : RealRecurrenceLaw) (t : ℝ) : 0 < L.mgf t :=
  finiteMGF_pos_of_normalized _ _ _ L.mass_nonneg L.mass_total t

theorem RealRecurrenceLaw.tiltedAdjacent (L : RealRecurrenceLaw) (i : ℕ)
    (hi : i < L.degree) (t : ℝ) :
    L.mass (i + 1) * (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + L.remainder) *
      Real.exp (t * ((i + 1 : ℕ) : ℝ))) =
    Real.exp t * (L.mass i * ((L.marks - i) * ((L.degree : ℝ) - i) * Real.exp (t * i))) := by
  have h := L.adjacent i hi
  push_cast
  rw [show t * ((i : ℝ) + 1) = t * i + t by ring, Real.exp_add]
  calc
    _ = (((i : ℝ) + 1) * ((i : ℝ) + 1 + L.remainder) * L.mass (i + 1)) *
      Real.exp (t * i) * Real.exp t := by ring
    _ = ((L.marks - i) * ((L.degree : ℝ) - i) * L.mass i) *
      Real.exp (t * i) * Real.exp t := by rw [h]
    _ = _ := by ring

theorem RealRecurrenceLaw.tiltedBalance (L : RealRecurrenceLaw) (t : ℝ) :
    (∑ i ∈ Finset.range (L.degree + 1), L.mass i *
      ((i : ℝ) * ((i : ℝ) + L.remainder) * Real.exp (t * i))) =
    Real.exp t * (∑ i ∈ Finset.range (L.degree + 1),
      L.mass i *
        ((L.marks - i) * ((L.degree : ℝ) - i) * Real.exp (t * i))) := by
  calc
    _ = ∑ i ∈ Finset.range L.degree, L.mass (i + 1) *
        (((i + 1 : ℕ) : ℝ) * (((i + 1 : ℕ) : ℝ) + L.remainder) *
          Real.exp (t * ((i + 1 : ℕ) : ℝ))) := by
      rw [Finset.sum_range_succ']
      simp
    _ = Real.exp t * (∑ i ∈ Finset.range L.degree,
        L.mass i *
          ((L.marks - i) * ((L.degree : ℝ) - i) * Real.exp (t * i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact L.tiltedAdjacent i (Finset.mem_range.mp hi) t
    _ = _ := by rw [Finset.sum_range_succ]; simp

/-- The exact normalized adjacent-mass expectation identity. -/
theorem RealRecurrenceLaw.expectationBalance (L : RealRecurrenceLaw) (t : ℝ) :
    L.expectation t (fun i => (i : ℝ) * (i + L.remainder)) =
      Real.exp t * L.expectation t
        (fun i => (L.marks - i) * ((L.degree : ℝ) - i)) := by
  unfold RealRecurrenceLaw.expectation
  rw [L.tiltedBalance t]
  ring

/-- The same finite recurrence written using the three raw tilted moments. -/
theorem RealRecurrenceLaw.momentsBalance (L : RealRecurrenceLaw) (t : ℝ) :
    finiteTiltSecond (Finset.range (L.degree + 1)) (L.mass)
        (fun i => (i : ℝ)) t +
      L.remainder * finiteTiltFirst (Finset.range (L.degree + 1))
        (L.mass) (fun i => (i : ℝ)) t =
    Real.exp t *
      (finiteTiltSecond (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t -
        (L.marks + L.degree) * finiteTiltFirst (Finset.range (L.degree + 1))
          (L.mass) (fun i => (i : ℝ)) t +
        L.marks * L.degree * L.mgf t) := by
  have hl :
      (∑ i ∈ Finset.range (L.degree + 1), L.mass i *
        ((i : ℝ) * ((i : ℝ) + L.remainder) * Real.exp (t * i))) =
      finiteTiltSecond (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t +
        L.remainder * finiteTiltFirst (Finset.range (L.degree + 1))
          (L.mass) (fun i => (i : ℝ)) t := by
    simp only [finiteTiltSecond, finiteTiltFirst, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hr :
      (∑ i ∈ Finset.range (L.degree + 1), L.mass i *
        ((L.marks - i) * ((L.degree : ℝ) - i) * Real.exp (t * i))) =
      finiteTiltSecond (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t -
        (L.marks + L.degree) * finiteTiltFirst (Finset.range (L.degree + 1))
          (L.mass) (fun i => (i : ℝ)) t +
        L.marks * L.degree * L.mgf t := by
    simp only [finiteTiltSecond, finiteTiltFirst, RealRecurrenceLaw.mgf, finiteMGF,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [← hl, ← hr]
  exact L.tiltedBalance t


theorem RealRecurrenceLaw.mean_hasDerivAt (L : RealRecurrenceLaw) (t : ℝ) :
    HasDerivAt (L.mean) (L.variance t) t := by
  have hg : L.mgf t ≠ 0 := ne_of_gt (L.mgf_pos t)
  have heq : L.variance t =
      (finiteTiltSecond (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t * L.mgf t -
        finiteTiltFirst (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t *
        finiteTiltFirst (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t) / (L.mgf t) ^ 2 := by
    unfold RealRecurrenceLaw.variance RealRecurrenceLaw.mean
    field_simp [hg]
  rw [heq]
  exact finiteTiltedMean_hasDerivAt (Finset.range (L.degree + 1))
    (L.mass) (fun i => (i : ℝ))
    L.mass_nonneg
    L.mass_total t

/-- The adjacent recurrence as a mean-variance identity, with no division
by a quadratic coefficient or by `exp t - 1`. -/
theorem RealRecurrenceLaw.meanVarianceBalance (L : RealRecurrenceLaw) (t : ℝ) :
    L.mean t *
        (L.mean t + L.remainder) +
      L.variance t =
    Real.exp t *
      ((L.marks - L.mean t) *
        ((L.degree : ℝ) - L.mean t) +
        L.variance t) := by
  have hg : L.mgf t ≠ 0 :=
    ne_of_gt (L.mgf_pos t)
  have h := congrArg (fun x : ℝ => x / L.mgf t)
    (RealRecurrenceLaw.momentsBalance L t)
  simp only [add_div, sub_div, mul_div_assoc, div_self hg] at h
  unfold RealRecurrenceLaw.variance RealRecurrenceLaw.mean
  nlinarith only [h]

theorem RealRecurrenceLaw.variance_differentiableAt (L : RealRecurrenceLaw) (t : ℝ) :
    DifferentiableAt ℝ (L.variance) t := by
  have hg := (finiteMGF_hasDerivAt (Finset.range (L.degree + 1))
    (L.mass) (fun i => (i : ℝ)) t).differentiableAt
  have hs := finiteTiltSecond_differentiableAt (Finset.range (L.degree + 1))
    (L.mass) (fun i => (i : ℝ)) t
  have hu := (RealRecurrenceLaw.mean_hasDerivAt L t).differentiableAt
  exact (hs.div hg (ne_of_gt (L.mgf_pos t))).sub (hu.pow 2)

/-- Differentiating the genuine adjacent balance once, keeping the equation
valid also at zero tilt and at variance stationary points. -/
theorem RealRecurrenceLaw.varianceDifferentialBalance (L : RealRecurrenceLaw) (t : ℝ) :
    let u := L.mean t
    let v := L.variance t
    let w := deriv (L.variance) t
    (2 * u + L.remainder) * v + w =
      Real.exp t * ((L.marks - u) * ((L.degree : ℝ) - u) + v) +
        Real.exp t * ((2 * u - L.marks - L.degree) * v + w) := by
  dsimp only
  let U := L.mean
  let V := L.variance
  have hu : HasDerivAt U (V t) t :=
    RealRecurrenceLaw.mean_hasDerivAt L t
  have hv : HasDerivAt V (deriv V t) t :=
    (RealRecurrenceLaw.variance_differentiableAt L t).hasDerivAt
  have hl : HasDerivAt (fun s => U s * (U s + L.remainder) + V s)
      ((2 * U t + L.remainder) * V t + deriv V t) t := by
    exact ((hu.mul (hu.add_const L.remainder)).add hv).congr_deriv (by ring)
  have hk := ((hasDerivAt_const t L.marks).sub hu)
  have hm := ((hasDerivAt_const t (L.degree : ℝ)).sub hu)
  have hr : HasDerivAt
      (fun s => Real.exp s * ((L.marks - U s) * ((L.degree : ℝ) - U s) + V s))
      (Real.exp t * ((L.marks - U t) * ((L.degree : ℝ) - U t) + V t) +
        Real.exp t * ((2 * U t - L.marks - L.degree) * V t + deriv V t)) t := by
    exact ((Real.hasDerivAt_exp t).mul ((hk.mul hm).add hv)).congr_deriv (by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
      ring)
  have heq : (fun s => U s * (U s + L.remainder) + V s) =
      (fun s => Real.exp s * ((L.marks - U s) * ((L.degree : ℝ) - U s) + V s)) := by
    funext s
    exact RealRecurrenceLaw.meanVarianceBalance L s
  rw [heq] at hl
  exact hl.unique hr

/-- The stationary derivative equation needed by the algebraic curvature
certificate; its only extra hypothesis is actual derivative vanishing. -/
theorem RealRecurrenceLaw.varianceStationaryBalance (L : RealRecurrenceLaw) (t : ℝ)
    (hw : deriv (L.variance) t = 0) :
    let u := L.mean t
    let v := L.variance t
    Real.exp t * ((L.marks - u) * ((L.degree : ℝ) - u) -
      v * (L.marks + L.degree - 2 * u - 1)) = v * (L.remainder + 2 * u) := by
  have h := RealRecurrenceLaw.varianceDifferentialBalance L t
  dsimp only at h ⊢
  rw [hw] at h
  nlinarith only [h]

/-- Eliminating the exponential tilt gives the denominator-free variance ODE.
Here the differentiated variance is with respect to the original tilt `t`. -/
theorem RealRecurrenceLaw.varianceCurveIdentity (L : RealRecurrenceLaw) (t : ℝ) :
    let u := L.mean t
    let v := L.variance t
    let w := deriv (L.variance) t
    let A := u * (u + L.remainder)
    let C := (L.marks - u) * ((L.degree : ℝ) - u)
    (C - A) * w =
      -(L.marks + L.degree + L.remainder - 1) * v ^ 2 +
        (A + C - (2 * u + L.remainder) * C + (2 * u - L.marks - L.degree) * A) * v + A * C := by
  have h₀ := RealRecurrenceLaw.meanVarianceBalance L t
  have h₁ := RealRecurrenceLaw.varianceDifferentialBalance L t
  dsimp only at h₁ ⊢
  let u := L.mean t
  let v := L.variance t
  let w := deriv (L.variance) t
  change u * (u + L.remainder) + v =
    Real.exp t * ((L.marks - u) * ((L.degree : ℝ) - u) + v) at h₀
  change (2 * u + L.remainder) * v + w =
    Real.exp t * ((L.marks - u) * ((L.degree : ℝ) - u) + v) +
      Real.exp t * ((2 * u - L.marks - L.degree) * v + w) at h₁
  change ((L.marks - u) * ((L.degree : ℝ) - u) - u * (u + L.remainder)) * w = _
  linear_combination
    ((L.marks - u) * ((L.degree : ℝ) - u) + v) * h₁ -
      ((L.marks - u) * ((L.degree : ℝ) - u) + v +
        (2 * u - L.marks - L.degree) * v + w) * h₀

theorem RealRecurrenceLaw.mean_pos (L : RealRecurrenceLaw) (hm : 0 < L.degree)
    (t : ℝ) : 0 < L.mean t := by
  apply div_pos
  · unfold finiteTiltFirst
    apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (L.mass_nonneg i hi) (by positivity)
    · refine ⟨1, Finset.mem_range.mpr (by omega), ?_⟩
      have hmass := L.mass_pos 1 (by omega)
      simpa using mul_pos hmass (Real.exp_pos t)
  · exact L.mgf_pos t

/-- A nondegenerate canonical tilted mean stays strictly below its support maximum. -/
theorem RealRecurrenceLaw.mean_lt (L : RealRecurrenceLaw) (hm : 0 < L.degree)
    (t : ℝ) : L.mean t < (L.degree : ℝ) := by
  have hg := L.mgf_pos t
  have hsum :
      (∑ i ∈ Finset.range (L.degree + 1), L.mass i *
        (((L.degree : ℝ) - i) * Real.exp (t * i))) =
      (L.degree : ℝ) * L.mgf t -
        finiteTiltFirst (Finset.range (L.degree + 1))
          (L.mass) (fun i => (i : ℝ)) t := by
    simp only [RealRecurrenceLaw.mgf, finiteMGF, finiteTiltFirst, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hp : 0 <
      ∑ i ∈ Finset.range (L.degree + 1), L.mass i *
        (((L.degree : ℝ) - i) * Real.exp (t * i)) := by
    apply Finset.sum_pos'
    · intro i hi
      have hi' : (i : ℝ) ≤ L.degree := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_nonneg (L.mass_nonneg i hi)
        (mul_nonneg (sub_nonneg.mpr hi') (le_of_lt (Real.exp_pos _)))
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      have hmass := L.mass_pos 0 (by omega)
      have hm' : (0 : ℝ) < L.degree := by exact_mod_cast hm
      simpa using mul_pos hmass hm'
  rw [hsum] at hp
  unfold RealRecurrenceLaw.mean
  exact (div_lt_iff₀ hg).mpr (by linarith)

/-- Tilted variance equals the actual expectation of the centered square. -/
theorem RealRecurrenceLaw.varianceCenteredSquare (L : RealRecurrenceLaw) (t : ℝ) :
    L.expectation t
        (fun i => ((i : ℝ) - L.mean t) ^ 2) =
      L.variance t := by
  let u := L.mean t
  have hsum :
      (∑ i ∈ Finset.range (L.degree + 1), L.mass i *
        (((i : ℝ) - u) ^ 2 * Real.exp (t * i))) =
      finiteTiltSecond (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t -
        2 * u * finiteTiltFirst (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t + u ^ 2 * L.mgf t := by
    simp only [finiteTiltSecond, finiteTiltFirst, RealRecurrenceLaw.mgf, finiteMGF,
      Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hg : L.mgf t ≠ 0 := ne_of_gt (L.mgf_pos t)
  unfold RealRecurrenceLaw.expectation
  change (∑ i ∈ Finset.range (L.degree + 1), L.mass i *
    (((i : ℝ) - u) ^ 2 * Real.exp (t * i))) / L.mgf t = _
  rw [hsum]
  dsimp [u, RealRecurrenceLaw.variance, RealRecurrenceLaw.mean]
  field_simp [hg]
  ring

/-- Positive variance at every tilt follows from positive mass at zero and
a strictly positive tilted mean, without a root factorization hypothesis. -/
theorem RealRecurrenceLaw.variance_pos (L : RealRecurrenceLaw) (hm : 0 < L.degree) (t : ℝ) :
    0 < L.variance t := by
  rw [← RealRecurrenceLaw.varianceCenteredSquare L t]
  unfold RealRecurrenceLaw.expectation
  apply div_pos
  · apply Finset.sum_pos'
    · intro i hi
      exact mul_nonneg (L.mass_nonneg i hi) (by positivity)
    · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      have hu := RealRecurrenceLaw.mean_pos L hm t
      have hmass := L.mass_pos 0 (by omega)
      simpa using mul_pos hmass (sq_pos_of_pos hu)
  · exact L.mgf_pos t


noncomputable def RealRecurrenceLaw.up (L : RealRecurrenceLaw) (t : ℝ) (i : ℕ) : ℝ :=
  ((i : ℝ) + 1) * L.mass (i + 1) *
    Real.exp (t * ((i + 1 : ℕ) : ℝ))

noncomputable def RealRecurrenceLaw.down (L : RealRecurrenceLaw) (t : ℝ) (i : ℕ) : ℝ :=
  ((L.degree : ℝ) - i) * L.mass i * Real.exp (t * i)

theorem RealRecurrenceLaw.upDownBalance (L : RealRecurrenceLaw) (i : ℕ)
    (hi : i < L.degree) (t : ℝ) :
    ((i : ℝ) + 1 + L.remainder) * RealRecurrenceLaw.up L t i =
      Real.exp t * (L.marks - i) * RealRecurrenceLaw.down L t i := by
  have h := L.tiltedAdjacent i hi t
  push_cast at h
  unfold RealRecurrenceLaw.up RealRecurrenceLaw.down
  push_cast
  nlinarith only [h]

theorem RealRecurrenceLaw.down_nonneg (L : RealRecurrenceLaw) (i : ℕ) (hi : i ≤ L.degree) (t : ℝ) :
    0 ≤ RealRecurrenceLaw.down L t i := by
  have hi' : (i : ℝ) ≤ L.degree := by exact_mod_cast hi
  unfold RealRecurrenceLaw.down
  exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hi')
    (L.mass_pos i hi).le) (le_of_lt (Real.exp_pos _))

/-- The exact cross-product identity for the tilted upward and downward weights. -/
theorem RealRecurrenceLaw.upDownCross (L : RealRecurrenceLaw) (i j : ℕ)
    (hi : i < L.degree) (hj : j < L.degree) (t : ℝ) :
    ((i : ℝ) + 1 + L.remainder) * ((j : ℝ) + 1 + L.remainder) *
      (RealRecurrenceLaw.up L t i * RealRecurrenceLaw.down L t j -
        RealRecurrenceLaw.up L t j * RealRecurrenceLaw.down L t i) =
      Real.exp t * (L.marks + L.remainder + 1) * ((j : ℝ) - i) *
        RealRecurrenceLaw.down L t i * RealRecurrenceLaw.down L t j := by
  have hᵢ := RealRecurrenceLaw.upDownBalance L i hi t
  have hⱼ := RealRecurrenceLaw.upDownBalance L j hj t
  linear_combination
    (((j : ℝ) + 1 + L.remainder) * RealRecurrenceLaw.down L t j) * hᵢ -
      (((i : ℝ) + 1 + L.remainder) * RealRecurrenceLaw.down L t i) * hⱼ

theorem RealRecurrenceLaw.upDownCrossOrder (L : RealRecurrenceLaw) (i j : ℕ)
    (hi : i < L.degree) (hj : j < L.degree) (t : ℝ) :
    ((i : ℝ) - j) *
      (RealRecurrenceLaw.up L t i * RealRecurrenceLaw.down L t j -
        RealRecurrenceLaw.up L t j * RealRecurrenceLaw.down L t i) ≤ 0 := by
  have h := RealRecurrenceLaw.upDownCross L i j hi hj t
  have hbᵢ := RealRecurrenceLaw.down_nonneg L i (Nat.le_of_lt hi) t
  have hbⱼ := RealRecurrenceLaw.down_nonneg L j (Nat.le_of_lt hj) t
  have hmarks : 0 ≤ L.marks := (Nat.cast_nonneg L.degree).trans L.marks_ge
  have hr := L.remainder_nonneg
  have hc : 0 ≤ Real.exp t * (L.marks + L.remainder + 1) *
      RealRecurrenceLaw.down L t i * RealRecurrenceLaw.down L t j := by positivity
  have hden : 0 < ((i : ℝ) + 1 + L.remainder) * ((j : ℝ) + 1 + L.remainder) := by positivity
  have hprod : ((i : ℝ) + 1 + L.remainder) * ((j : ℝ) + 1 + L.remainder) *
      (((i : ℝ) - j) *
        (RealRecurrenceLaw.up L t i * RealRecurrenceLaw.down L t j -
          RealRecurrenceLaw.up L t j * RealRecurrenceLaw.down L t i)) =
      -(Real.exp t * (L.marks + L.remainder + 1) *
        RealRecurrenceLaw.down L t i * RealRecurrenceLaw.down L t j) *
          ((i : ℝ) - j) ^ 2 := by
    linear_combination ((i : ℝ) - j) * h
  have hnonpos : ((i : ℝ) + 1 + L.remainder) * ((j : ℝ) + 1 + L.remainder) *
      (((i : ℝ) - j) *
        (RealRecurrenceLaw.up L t i * RealRecurrenceLaw.down L t j -
          RealRecurrenceLaw.up L t j * RealRecurrenceLaw.down L t i)) ≤ 0 := by
    rw [hprod]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg _)
  by_contra hpositive
  have hpos := mul_pos hden (lt_of_not_ge hpositive)
  linarith

theorem RealRecurrenceLaw.upSum (L : RealRecurrenceLaw) (t : ℝ) :
    (∑ i ∈ Finset.range L.degree, RealRecurrenceLaw.up L t i) =
      finiteTiltFirst (Finset.range (L.degree + 1)) (L.mass)
        (fun i => (i : ℝ)) t := by
  unfold finiteTiltFirst
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  unfold RealRecurrenceLaw.up
  push_cast
  ring

theorem RealRecurrenceLaw.upFirst (L : RealRecurrenceLaw) (t : ℝ) :
    (∑ i ∈ Finset.range L.degree, (i : ℝ) * RealRecurrenceLaw.up L t i) =
      finiteTiltSecond (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t -
        finiteTiltFirst (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t := by
  simp only [finiteTiltSecond, finiteTiltFirst, ← Finset.sum_sub_distrib]
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero,
    Real.exp_zero, zero_mul, sub_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  unfold RealRecurrenceLaw.up
  push_cast
  ring

theorem RealRecurrenceLaw.downSum (L : RealRecurrenceLaw) (t : ℝ) :
    (∑ i ∈ Finset.range L.degree, RealRecurrenceLaw.down L t i) =
      (L.degree : ℝ) * L.mgf t -
        finiteTiltFirst (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t := by
  calc
    _ = ∑ i ∈ Finset.range (L.degree + 1), RealRecurrenceLaw.down L t i := by
      rw [Finset.sum_range_succ]
      simp [RealRecurrenceLaw.down]
    _ = _ := by
      simp only [RealRecurrenceLaw.mgf, finiteMGF, finiteTiltFirst,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      unfold RealRecurrenceLaw.down
      ring

theorem RealRecurrenceLaw.downFirst (L : RealRecurrenceLaw) (t : ℝ) :
    (∑ i ∈ Finset.range L.degree, (i : ℝ) * RealRecurrenceLaw.down L t i) =
      (L.degree : ℝ) * finiteTiltFirst (Finset.range (L.degree + 1))
          (L.mass) (fun i => (i : ℝ)) t -
        finiteTiltSecond (Finset.range (L.degree + 1)) (L.mass)
          (fun i => (i : ℝ)) t := by
  calc
    _ = ∑ i ∈ Finset.range (L.degree + 1), (i : ℝ) * RealRecurrenceLaw.down L t i := by
      rw [Finset.sum_range_succ]
      simp [RealRecurrenceLaw.down]
    _ = _ := by
      simp only [finiteTiltSecond, finiteTiltFirst,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      unfold RealRecurrenceLaw.down
      ring

/-- The actual tilted variance obeys the degree-`L.degree` mean-variance bound,
proved directly from adjacent hypergeometric counts. -/
theorem RealRecurrenceLaw.varianceAdmissible (L : RealRecurrenceLaw) (hm : 0 < L.degree) (t : ℝ) :
    L.variance t ≤
      L.mean t *
        ((L.degree : ℝ) - L.mean t) / L.degree := by
  have h := cross_sum_order (Finset.range L.degree) (fun i => (i : ℝ))
    (RealRecurrenceLaw.up L t) (RealRecurrenceLaw.down L t) (by
      intro i hi j hj
      exact RealRecurrenceLaw.upDownCrossOrder L i j
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) t)
  rw [RealRecurrenceLaw.upFirst, RealRecurrenceLaw.downSum,
    RealRecurrenceLaw.downFirst, RealRecurrenceLaw.upSum] at h
  have hg := L.mgf_pos t
  have hm' : (0 : ℝ) < L.degree := by exact_mod_cast hm
  apply (le_div_iff₀ hm').mpr
  unfold RealRecurrenceLaw.variance RealRecurrenceLaw.mean
  apply (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hg)).mp
  field_simp [ne_of_gt hg]
  nlinarith only [h]

theorem RealRecurrenceLaw.expectation_tendsto_atTop (L : RealRecurrenceLaw) (g : ℕ → ℝ) :
    Tendsto (fun t => L.expectation t g) atTop (𝓝 (g L.degree)) := by
  have hi : L.degree ∈ Finset.range (L.degree + 1) := Finset.mem_range.mpr (by omega)
  have h := finite_tilted_expectation_tendsto_atTop (Finset.range (L.degree + 1))
    L.mass (fun i => (i : ℝ)) g L.degree hi (L.mass_pos L.degree le_rfl).ne' (by
      intro i hi him
      exact_mod_cast (show i < L.degree by have := Finset.mem_range.mp hi; omega))
  simpa only [RealRecurrenceLaw.expectation, RealRecurrenceLaw.mgf, finiteMGF,
    mul_assoc] using h

theorem RealRecurrenceLaw.expectation_tendsto_atBot (L : RealRecurrenceLaw) (g : ℕ → ℝ) :
    Tendsto (fun t => L.expectation t g) atBot (𝓝 (g 0)) := by
  have hi : 0 ∈ Finset.range (L.degree + 1) := Finset.mem_range.mpr (by omega)
  have h := finite_tilted_expectation_tendsto_atBot (Finset.range (L.degree + 1))
    L.mass (fun i => (i : ℝ)) g 0 hi (L.mass_pos 0 (by omega)).ne' (by
      intro i hi hi0
      exact_mod_cast (show 0 < i by omega))
  simpa only [RealRecurrenceLaw.expectation, RealRecurrenceLaw.mgf, finiteMGF,
    mul_assoc] using h

theorem RealRecurrenceLaw.variance_tendsto_atTop (L : RealRecurrenceLaw) :
    Tendsto L.variance atTop (𝓝 0) := by
  have h2 := L.expectation_tendsto_atTop (fun i => (i : ℝ) ^ 2)
  have h1 := L.expectation_tendsto_atTop (fun i => (i : ℝ))
  have h := h2.sub (h1.pow 2)
  rw [sub_self] at h
  convert h using 1
  ext t
  rfl

theorem RealRecurrenceLaw.variance_tendsto_atBot (L : RealRecurrenceLaw) :
    Tendsto L.variance atBot (𝓝 0) := by
  have h2 := L.expectation_tendsto_atBot (fun i => (i : ℝ) ^ 2)
  have h1 := L.expectation_tendsto_atBot (fun i => (i : ℝ))
  have h := h2.sub (h1.pow 2)
  simp only [Nat.cast_zero, zero_pow (by omega : 2 ≠ 0), sub_self] at h
  convert h using 1
  ext t
  rfl

theorem RealRecurrenceLaw.variance_stationary_sharp (L : RealRecurrenceLaw)
    (hm : 3 ≤ L.degree) (t : ℝ) (hw : deriv L.variance t = 0) :
    L.variance t ≤
      (L.degree : ℝ) * (L.marks + L.remainder) /
        (4 * (L.marks + L.degree + L.remainder - 1)) := by
  let u := L.mean t
  let v := L.variance t
  have hbal := L.meanVarianceBalance t
  have hstat := L.varianceStationaryBalance t hw
  have hpoly : stationaryPolynomial (L.degree : ℝ) L.marks L.remainder u v = 0 := by
    apply stationary_elimination (L.degree : ℝ) L.marks L.remainder u v (Real.exp t)
    · dsimp [u,v] at *
      nlinarith only [hbal]
    · dsimp only at hstat
      change Real.exp t * stationaryDen (L.degree : ℝ) L.marks u v =
        v * (L.remainder + 2 * u)
      unfold stationaryDen
      convert hstat using 1 <;> ring
  have hh : 0 ≤ L.marks - (L.degree : ℝ) := sub_nonneg.mpr L.marks_ge
  have hj : (3 : ℝ) ≤ L.degree := by exact_mod_cast hm
  have hsum : (L.degree : ℝ) + (L.marks - L.degree) = L.marks := by ring
  have hpoly' : stationaryPolynomial (L.degree : ℝ)
      ((L.degree : ℝ) + (L.marks - L.degree)) L.remainder u v = 0 := by
    rw [hsum]
    exact hpoly
  have hb := admissible_stationary_sharp_bound (L.degree : ℝ)
    (L.marks - L.degree) L.remainder u v hj hh L.remainder_nonneg
    (L.mean_pos (by omega) t) (L.mean_lt (by omega) t)
    (L.variance_pos (by omega) t) (L.varianceAdmissible (by omega) t) hpoly'
  convert hb using 1 <;> ring

/-- The sharp all-tilt curvature bound holds for actual positive recurrence
laws with real marks and remainder, for every support degree at least three. -/
theorem RealRecurrenceLaw.variance_sharp (L : RealRecurrenceLaw) (hm : 3 ≤ L.degree) (t : ℝ) :
    L.variance t ≤
      (L.degree : ℝ) * (L.marks + L.remainder) /
        (4 * (L.marks + L.degree + L.remainder - 1)) := by
  have hmc : (3 : ℝ) ≤ L.degree := by exact_mod_cast hm
  have hkc := L.marks_ge
  have hr := L.remainder_nonneg
  have hd : 0 < L.marks + L.degree + L.remainder - 1 := by linarith
  have hn : 0 < L.marks + L.remainder := by linarith
  have hB : 0 < (L.degree : ℝ) * (L.marks + L.remainder) /
      (4 * (L.marks + L.degree + L.remainder - 1)) := by positivity
  exact global_bound_of_stationary_bound
    (continuous_iff_continuousAt.mpr (fun t => (L.variance_differentiableAt t).continuousAt))
    hB L.variance_tendsto_atBot L.variance_tendsto_atTop
    (fun t ht => L.variance_stationary_sharp hm t ht) t

theorem RealRecurrenceLaw.down_pos (L : RealRecurrenceLaw) (i : ℕ) (hi : i<L.degree) (t : ℝ) :
    0<RealRecurrenceLaw.down L t i := by
  unfold RealRecurrenceLaw.down
  have hiR : (i:ℝ)<L.degree := by exact_mod_cast hi
  exact mul_pos (mul_pos (sub_pos.mpr hiR)
    (L.mass_pos i hi.le)) (Real.exp_pos _)

/-- The actual mean-variance inequality is strict as soon as the support
contains at least three points. The strictness follows from two adjacent
tilted mass ratios, independently of a root factorization. -/
theorem RealRecurrenceLaw.varianceAdmissibleStrict (L : RealRecurrenceLaw) (hm : 2≤L.degree) (t : ℝ) :
    L.variance t<
      L.mean t*
        ((L.degree:ℝ)-L.mean t)/(L.degree:ℝ) := by
  have hc := RealRecurrenceLaw.upDownCross L 0 1 (by omega) (by omega) t
  have h0 := RealRecurrenceLaw.down_pos L 0 (by omega) t
  have h1 := RealRecurrenceLaw.down_pos L 1 (by omega) t
  have hmarks : 0 ≤ L.marks := (Nat.cast_nonneg L.degree).trans L.marks_ge
  have hr := L.remainder_nonneg
  have hprod : 0<Real.exp t*(L.marks+L.remainder+1)*
      RealRecurrenceLaw.down L t 0*RealRecurrenceLaw.down L t 1 := by positivity
  norm_num only [Nat.cast_zero,Nat.cast_one,zero_add,sub_zero] at hc
  have hden : 0<(1+L.remainder)*(1+1+L.remainder) := by positivity
  have hdiff : 0<RealRecurrenceLaw.up L t 0*RealRecurrenceLaw.down L t 1-
      RealRecurrenceLaw.up L t 1*RealRecurrenceLaw.down L t 0 := by
    nlinarith only [hc,hprod,hden]
  have h := cross_sum_strict_order (Finset.range L.degree) (fun i => (i:ℝ))
    (RealRecurrenceLaw.up L t) (RealRecurrenceLaw.down L t)
    (by
      intro i hi j hj
      exact RealRecurrenceLaw.upDownCrossOrder L i j
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) t)
    0 1 (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega))
    (by simpa only [Nat.cast_zero,Nat.cast_one,zero_sub,neg_mul,one_mul] using neg_neg_of_pos hdiff)
  rw [RealRecurrenceLaw.upFirst,RealRecurrenceLaw.downSum,RealRecurrenceLaw.downFirst,RealRecurrenceLaw.upSum] at h
  have hg := L.mgf_pos t
  have hmR : (0:ℝ)<L.degree := by exact_mod_cast (show 0<L.degree by omega)
  apply (lt_div_iff₀ hmR).2
  unfold RealRecurrenceLaw.variance RealRecurrenceLaw.mean
  apply (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos hg)).mp
  field_simp [ne_of_gt hg]
  nlinarith only [h]

end
end ExactHoeffding
