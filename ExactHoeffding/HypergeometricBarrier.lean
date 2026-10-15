import ExactHoeffding.VarianceBarrierFlow
import ExactHoeffding.TiltedAdmissibilityDirect
import ExactHoeffding.HypergeometricEndpoints
import ExactHoeffding.ZeroTiltMoments
import ExactHoeffding.HypergeometricODEMargins

namespace ExactHoeffding

/-- The strict quadratic variance envelope for the actual hypergeometric
tilted law, in canonical margins. -/
theorem hypergeomTiltVariance_barrier_canonical (k m r : ℕ)
    (hm : 3≤m) (hmk : m≤k) (hk : k≤m+r) (hgap : m<k+r) :
    let N : ℝ := (k:ℝ)+m+r
    let d := 1-2*(k:ℝ)/N
    (∀t, hypergeomTiltVariance (k+m+r) k m t≤
      varianceBarrier N (m:ℝ) d
        (hypergeomTiltMean (k+m+r) k m t-(m:ℝ)*(k:ℝ)/N)) ∧
    (∀t, hypergeomTiltVariance (k+m+r) k m t=
      varianceBarrier N (m:ℝ) d
        (hypergeomTiltMean (k+m+r) k m t-(m:ℝ)*(k:ℝ)/N) ↔ t=0) := by
  let N : ℝ := (k:ℝ)+m+r
  let d := 1-2*(k:ℝ)/N
  have hmR : (3:ℝ)≤m := by exact_mod_cast hm
  have hmkR : (m:ℝ)≤k := by exact_mod_cast hmk
  have hkR : (k:ℝ)≤m+r := by exact_mod_cast hk
  have hgR : (m:ℝ)<k+r := by exact_mod_cast hgap
  have hN : 0<N := by dsimp [N]; have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hN1 : N-1≠0 := by dsimp [N]; have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hhalf : 2*(m:ℝ)<N := by dsimp [N]; linarith
  have hk2 : 2*(k:ℝ)≤N := by dsimp [N]; linarith
  have hmean : (m:ℝ)*(1-d)/2=(m:ℝ)*(k:ℝ)/N := by dsimp [d]; ring
  have hkiden : N*(1-d)/2=(k:ℝ) := by dsimp [d]; field_simp; ring
  have hd : 0≤d := by
    dsimp [d]
    exact sub_nonneg.mpr ((div_le_one hN).2 hk2)
  have hdelta : d≤barrierDelta N (m:ℝ) := by
    unfold barrierDelta
    dsimp [d]
    apply (le_div_iff₀ hN).2
    field_simp
    nlinarith only [hmkR]
  have hu0 : hypergeomTiltMean (k+m+r) k m 0=(m:ℝ)*(1-d)/2 := by
    rw [hypergeomTiltMean_zero (k+m+r) k m (by omega) (by omega),hmean]
    simp only [Nat.cast_add,N]
  have hv0 : hypergeomTiltVariance (k+m+r) k m 0=varianceBarrier N (m:ℝ) d 0 := by
    rw [hypergeomTiltVariance_zero (k+m+r) k m (by omega) (by omega)]
    rw [Nat.cast_sub (by omega : k≤k+m+r),Nat.cast_sub (by omega : m≤k+m+r)]
    simp only [Nat.cast_add]
    exact (varianceBarrier_center_success_fraction N (k:ℝ) (m:ℝ) (ne_of_gt hN) hN1).symm
  have hep := barrier_endpoints_positive N (k:ℝ) (m:ℝ) hmR hmkR hk2 hhalf
  have ho (t : ℝ) : riccatiF N (N*(1-d)/2) (m:ℝ)
      (hypergeomTiltMean (k+m+r) k m t) (hypergeomTiltVariance (k+m+r) k m t)+
      N*(hypergeomTiltMean (k+m+r) k m t-(m:ℝ)*(1-d)/2)*
      deriv (hypergeomTiltVariance (k+m+r) k m) t=0 := by
    have h := hypergeomTiltVariance_centered_curve_identity (k+m+r) k m
      hmk (by omega) (by omega) t
    dsimp only at h
    rw [hkiden,hmean]
    simpa only [Nat.cast_add,N] using h
  have heL : -(m:ℝ)*(1-d)/2=-(m:ℝ)*(k:ℝ)/N := by dsimp [d]; ring
  have hb := variance_barrier_of_riccati_flow N (m:ℝ) d
    (hypergeomTiltMean (k+m+r) k m) (hypergeomTiltVariance (k+m+r) k m)
    hmR hhalf hd hdelta
    (hypergeomTiltMean_hasDerivAt (k+m+r) k m (by omega) (by omega))
    (hypergeomTiltVariance_differentiableAt (k+m+r) k m (by omega) (by omega))
    (hypergeomTiltVariance_pos k m r hmk (by omega))
    (hypergeomTiltVariance_admissible k m r hmk (by omega)) hu0 hv0
    (hypergeomTiltMean_tendsto_atBot k m r hmk)
    (hypergeomTiltMean_tendsto_atTop k m r hmk)
    (hypergeomTiltVariance_tendsto_atBot k m r hmk)
    (hypergeomTiltVariance_tendsto_atTop k m r hmk)
    (by rw [heL]; exact hep.1) (by rw [hmean]; exact hep.2) ho
  simpa only [hmean] using hb

end ExactHoeffding
