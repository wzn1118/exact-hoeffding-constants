import ExactHoeffding.FiniteSupportEndpointEnvelope

/-!
# Chernoff tails from the finite-support Legendre rate

The only probabilistic input is the finite weighted Markov inequality.  Once
that input is supplied, the inverse tilted mean identifies the optimizing
nonnegative (respectively nonpositive) tilt and gives the exact exponential
rate without assuming the target tail bound.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- Upper-tail Chernoff optimization at an interior target. -/
theorem finiteSupport_upper_tail_of_markov
    (D : FiniteSupportTiltCurve) (tail : ℝ → ℝ)
    (hmark : ∀ (t : ℝ), 0 ≤ t →
      tail D.mu ≤ Real.exp (-t * D.mu + D.logMGF t)) :
    tail D.mu ≤ Real.exp (-finiteSupportLegendreRate D D.mu) := by
  have hinv : finiteSupportMeanInverse D D.mu = 0 := by
    exact ((finiteSupportMeanInverse_unique D D.hlomu D.hmuhi (t := 0)).1
      (by simpa [D.mean_zero])).symm
  have hrate : finiteSupportLegendreRate D D.mu = 0 := by
    rw [finiteSupportLegendreRate_at_mean D D.hlomu D.hmuhi, hinv,
      D.logMGF_zero]
    simp
  rw [hrate]
  simpa [D.logMGF_zero] using hmark 0 le_rfl

/-- Upper-tail Chernoff optimization at every interior target above the mean. -/
theorem finiteSupport_upper_tail_of_markov_interior
    (D : FiniteSupportTiltCurve) (tail : ℝ → ℝ) {v : ℝ}
    (hvmu : D.mu ≤ v) (hvhi : v < D.hi)
    (hmark : ∀ (t : ℝ), 0 ≤ t →
      tail v ≤ Real.exp (-t * v + D.logMGF t)) :
    tail v ≤ Real.exp (-finiteSupportLegendreRate D v) := by
  by_cases hv : v = D.mu
  · subst v
    have hinv : finiteSupportMeanInverse D D.mu = 0 := by
      exact ((finiteSupportMeanInverse_unique D D.hlomu D.hmuhi (t := 0)).1
        (by simpa [D.mean_zero])).symm
    have hrate : finiteSupportLegendreRate D D.mu = 0 := by
      rw [finiteSupportLegendreRate_at_mean D D.hlomu D.hmuhi, hinv,
        D.logMGF_zero]
      simp
    rw [hrate]
    simpa [D.logMGF_zero] using hmark 0 le_rfl
  · have hvmu' : D.mu < v := lt_of_le_of_ne hvmu (Ne.symm hv)
    let t : ℝ := finiteSupportMeanInverse D v
    have htmean : D.mean t = v := finiteSupportMeanInverse_spec D
      (lt_trans D.hlomu hvmu') hvhi
    have ht0 : 0 < t := by
      by_contra hnt
      have hle : t ≤ 0 := le_of_not_gt hnt
      have hmean : D.mean t ≤ D.mean 0 :=
        (strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos).monotone hle
      linarith [htmean, D.mean_zero, hvmu']
    have hrate := finiteSupportLegendreRate_at_mean D
      (lt_trans D.hlomu hvmu') hvhi
    rw [hrate]
    have hm := hmark t ht0.le
    convert hm using 1 <;> congr 1 <;> ring

/-- Lower-tail Chernoff optimization at an interior target below the mean. -/
theorem finiteSupport_lower_tail_of_markov_interior
    (D : FiniteSupportTiltCurve) (tail : ℝ → ℝ) {v : ℝ}
    (hvlo : D.lo < v) (hvmu : v ≤ D.mu)
    (hmark : ∀ (t : ℝ), t ≤ 0 →
      tail v ≤ Real.exp (-t * v + D.logMGF t)) :
    tail v ≤ Real.exp (-finiteSupportLegendreRate D v) := by
  by_cases hv : v = D.mu
  · subst v
    have hinv : finiteSupportMeanInverse D D.mu = 0 := by
      exact ((finiteSupportMeanInverse_unique D D.hlomu D.hmuhi (t := 0)).1
        (by simpa [D.mean_zero])).symm
    have hrate : finiteSupportLegendreRate D D.mu = 0 := by
      rw [finiteSupportLegendreRate_at_mean D D.hlomu D.hmuhi, hinv,
        D.logMGF_zero]
      simp
    rw [hrate]
    simpa [D.logMGF_zero] using hmark 0 le_rfl
  · have hvmu' : v < D.mu := lt_of_le_of_ne hvmu hv
    let t : ℝ := finiteSupportMeanInverse D v
    have htmean : D.mean t = v := finiteSupportMeanInverse_spec D
      hvlo (lt_trans hvmu' D.hmuhi)
    have ht0 : t < 0 := by
      by_contra hnt
      have hle : 0 ≤ t := le_of_not_gt hnt
      have hmean : D.mean 0 ≤ D.mean t :=
        (strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos).monotone hle
      linarith [htmean, D.mean_zero, hvmu']
    have hrate := finiteSupportLegendreRate_at_mean D
      hvlo (lt_trans hvmu' D.hmuhi)
    rw [hrate]
    have hm := hmark t ht0.le
    convert hm using 1 <;> congr 1 <;> ring

end
end ExactHoeffding
