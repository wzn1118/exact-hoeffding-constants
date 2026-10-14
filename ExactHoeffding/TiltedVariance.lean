import ExactHoeffding.MomentGenerating

/-!
# Exact tilted variance for finite distributions

No analytic curvature bounds are assumed here. We first establish strict
positivity of a normalized finite Laplace transform and then prove its first
and second logarithmic derivatives from first principles.
-/

namespace ExactHoeffding

/-- Normalized nonnegative finite weights have a strictly positive
exponential moment for every real tilt. -/
theorem finiteMGF_pos_of_normalized {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weights i)
    (hs : ∑ i ∈ s, weights i = 1) (t : ℝ) :
    0 < finiteMGF s weights values t := by
  have hexists : ∃ i ∈ s, 0 < weights i := by
    by_contra hn
    push_neg at hn
    have hz : ∀ i ∈ s, weights i = 0 := by
      intro i hi
      exact le_antisymm (hn i hi) (hw i hi)
    have hs0 : (∑ i ∈ s, weights i) = 0 := Finset.sum_eq_zero hz
    linarith
  unfold finiteMGF
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (hw i hi) (le_of_lt (Real.exp_pos _))
  · obtain ⟨i, hi, hp⟩ := hexists
    exact ⟨i, hi, mul_pos hp (Real.exp_pos _)⟩

/-- The first logarithmic derivative is the tilted mean. -/
theorem finiteLogMGF_hasDerivAt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weights i)
    (hs : ∑ i ∈ s, weights i = 1) (t : ℝ) :
    HasDerivAt (fun u => Real.log (finiteMGF s weights values u))
      (finiteTiltFirst s weights values t / finiteMGF s weights values t) t := by
  exact (finiteMGF_hasDerivAt s weights values t).log
    (ne_of_gt (finiteMGF_pos_of_normalized s weights values hw hs t))

/-- The tilted mean derivative is the normalized second centered moment,
expressed as a rational function of raw moments. -/
theorem finiteTiltedMean_hasDerivAt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weights i)
    (hs : ∑ i ∈ s, weights i = 1) (t : ℝ) :
    HasDerivAt
      (fun u => finiteTiltFirst s weights values u / finiteMGF s weights values u)
      ((finiteTiltSecond s weights values t * finiteMGF s weights values t -
        finiteTiltFirst s weights values t * finiteTiltFirst s weights values t) /
        (finiteMGF s weights values t) ^ 2) t := by
  exact (finiteTiltFirst_hasDerivAt s weights values t).div
    (finiteMGF_hasDerivAt s weights values t)
    (ne_of_gt (finiteMGF_pos_of_normalized s weights values hw hs t))

/-- The precise second derivative of a logarithmic moment-generating function. -/
theorem finiteLogMGF_second_deriv {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (weights values : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ weights i)
    (hs : ∑ i ∈ s, weights i = 1) (t : ℝ) :
    deriv (deriv (fun u => Real.log (finiteMGF s weights values u))) t =
      (finiteTiltSecond s weights values t * finiteMGF s weights values t -
        finiteTiltFirst s weights values t * finiteTiltFirst s weights values t) /
        (finiteMGF s weights values t) ^ 2 := by
  have hfirst :
      (fun u => deriv (fun v => Real.log (finiteMGF s weights values v)) u) =
      (fun u => finiteTiltFirst s weights values u / finiteMGF s weights values u) := by
    funext u
    exact (finiteLogMGF_hasDerivAt s weights values hw hs u).deriv
  rw [hfirst]
  exact (finiteTiltedMean_hasDerivAt s weights values hw hs t).deriv

/-- The exact hypergeometric tilted-variance formula for all valid finite
population/sample parameters and every real tilt. -/
theorem hypergeomLogMGF_second_deriv (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    deriv (deriv (fun u => Real.log (hypergeomMGF N k m u))) t =
      (finiteTiltSecond (Finset.range (m + 1)) (hypergeomMass N k m)
          (fun i => (i : ℝ)) t * hypergeomMGF N k m t -
        finiteTiltFirst (Finset.range (m + 1)) (hypergeomMass N k m)
          (fun i => (i : ℝ)) t *
        finiteTiltFirst (Finset.range (m + 1)) (hypergeomMass N k m)
          (fun i => (i : ℝ)) t) /
        (hypergeomMGF N k m t) ^ 2 := by
  simpa only [hypergeomMGF] using
    (finiteLogMGF_second_deriv (Finset.range (m + 1))
      (hypergeomMass N k m) (fun i => (i : ℝ))
      (fun i _ => hypergeomMass_nonneg N k m i)
      (hypergeomMass_total N k m hk hm) t)

end ExactHoeffding
