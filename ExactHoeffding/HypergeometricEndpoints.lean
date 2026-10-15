import ExactHoeffding.HypergeometricODE
import ExactHoeffding.TiltedEndpoints

open Filter
open scoped Topology

namespace ExactHoeffding

theorem hypergeomTiltExpectation_tendsto_atTop (k m r : ℕ)
    (hmk : m≤k) (g : ℕ→ℝ) :
    Tendsto (fun t => hypergeomTiltExpectation (k+m+r) k m t g)
      atTop (𝓝 (g m)) := by
  have hm : m∈Finset.range (m+1) := Finset.mem_range.mpr (by omega)
  have hw := ne_of_gt (hypergeomMass_pos_canonical k m r m hmk le_rfl)
  have h := finite_tilted_expectation_tendsto_atTop (Finset.range (m+1))
    (hypergeomMass (k+m+r) k m) (fun i => (i:ℝ)) g m hm hw (by
      intro i hi him
      exact_mod_cast (show i<m by have := Finset.mem_range.mp hi; omega))
  simpa only [hypergeomTiltExpectation,hypergeomMGF,finiteMGF,mul_assoc] using h

theorem hypergeomTiltExpectation_tendsto_atBot (k m r : ℕ)
    (hmk : m≤k) (g : ℕ→ℝ) :
    Tendsto (fun t => hypergeomTiltExpectation (k+m+r) k m t g)
      atBot (𝓝 (g 0)) := by
  have h0 : 0∈Finset.range (m+1) := Finset.mem_range.mpr (by omega)
  have hw := ne_of_gt (hypergeomMass_pos_canonical k m r 0 hmk (by omega))
  have h := finite_tilted_expectation_tendsto_atBot (Finset.range (m+1))
    (hypergeomMass (k+m+r) k m) (fun i => (i:ℝ)) g 0 h0 hw (by
      intro i hi hi0
      exact_mod_cast (show 0 < i by omega))
  simpa only [hypergeomTiltExpectation,hypergeomMGF,finiteMGF,mul_assoc] using h

theorem hypergeomTiltMean_tendsto_atTop (k m r : ℕ) (hmk : m≤k) :
    Tendsto (hypergeomTiltMean (k+m+r) k m) atTop (𝓝 (m:ℝ)) := by
  exact hypergeomTiltExpectation_tendsto_atTop k m r hmk (fun i => (i:ℝ))

theorem hypergeomTiltMean_tendsto_atBot (k m r : ℕ) (hmk : m≤k) :
    Tendsto (hypergeomTiltMean (k+m+r) k m) atBot (𝓝 0) := by
  have h := hypergeomTiltExpectation_tendsto_atBot k m r hmk (fun i => (i:ℝ))
  simp only [Nat.cast_zero] at h
  convert h using 1
  ext t
  rfl

theorem hypergeomTiltVariance_tendsto_atTop (k m r : ℕ) (hmk : m≤k) :
    Tendsto (hypergeomTiltVariance (k+m+r) k m) atTop (𝓝 0) := by
  have h2 := hypergeomTiltExpectation_tendsto_atTop k m r hmk (fun i => (i:ℝ)^2)
  have h1 := hypergeomTiltMean_tendsto_atTop k m r hmk
  have h := h2.sub (h1.pow 2)
  rw [sub_self] at h
  convert h using 1
  ext t
  rfl

theorem hypergeomTiltVariance_tendsto_atBot (k m r : ℕ) (hmk : m≤k) :
    Tendsto (hypergeomTiltVariance (k+m+r) k m) atBot (𝓝 0) := by
  have h2 := hypergeomTiltExpectation_tendsto_atBot k m r hmk (fun i => (i:ℝ)^2)
  have h1 := hypergeomTiltMean_tendsto_atBot k m r hmk
  have h := h2.sub (h1.pow 2)
  simp only [Nat.cast_zero,zero_pow (by decide : 2≠0),sub_self] at h
  convert h using 1
  ext t
  rfl

end ExactHoeffding
