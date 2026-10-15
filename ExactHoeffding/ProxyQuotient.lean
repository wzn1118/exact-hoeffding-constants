import ExactHoeffding.VarianceOptimality
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Order.Field

open Filter Set
open scoped Topology

namespace ExactHoeffding
noncomputable section

def hypergeomProxyQuotient (N k m : ℕ) : ℝ→ℝ :=
  Function.update (fun t => 2*hypergeomCenteredLogMGF N k m t/t^2) 0
    (hypergeomTiltVariance N k m 0)

theorem hypergeomProxyQuotient_continuous (N k m : ℕ) (hk : k≤N) (hm : m≤N) :
    Continuous (hypergeomProxyQuotient N k m) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t=0
  · subst t
    apply continuousAt_update_same.mpr
    have h := (hypergeom_centered_quadratic_limit N k m hk hm).const_mul 2
    convert h using 1
    · ext t
      ring
    · congr 1
      ring
  · apply (continuousAt_update_of_ne ht).2
    exact (continuousAt_const.mul (hypergeomCenteredLogMGF_hasDerivAt N k m hk hm t).continuousAt).div
      (continuousAt_id.pow 2) (pow_ne_zero 2 ht)

theorem hypergeomCenteredLogMGF_linear_bound (k m r : ℕ) (hmk : m≤k) (hm : 0<m) (t : ℝ) :
    |hypergeomCenteredLogMGF (k+m+r) k m t|≤(m:ℝ)*|t| := by
  let N := k+m+r
  let μ : ℝ := (m:ℝ)*(k:ℝ)/(N:ℝ)
  have hmu : 0<μ ∧ μ<(m:ℝ) := by
    dsimp [μ]
    rw [← hypergeomTiltMean_zero N k m (by dsimp [N]; omega) (by dsimp [N]; omega)]
    exact ⟨hypergeomTiltMean_pos k m r hmk hm 0,hypergeomTiltMean_lt k m r hmk hm 0⟩
  have hd (s : ℝ) := hypergeomCenteredLogMGF_hasDerivAt N k m
    (by dsimp [N]; omega) (by dsimp [N]; omega) s
  have hbound (s : ℝ) : ‖deriv (hypergeomCenteredLogMGF N k m) s‖≤(m:ℝ) := by
    rw [(hd s).deriv,Real.norm_eq_abs]
    apply abs_le.mpr
    have hpos := hypergeomTiltMean_pos k m r hmk hm s
    have hlt := hypergeomTiltMean_lt k m r hmk hm s
    change -(m:ℝ)≤hypergeomTiltMean N k m s-μ ∧ hypergeomTiltMean N k m s-μ≤(m:ℝ)
    constructor <;> linarith [hmu.1,hmu.2]
  have h := (convex_univ : Convex ℝ (Set.univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun s _ => (hd s).differentiableAt) (fun s _ => hbound s)
    (Set.mem_univ (0:ℝ)) (Set.mem_univ t)
  rw [hypergeomCenteredLogMGF_zero N k m (by dsimp [N]; omega) (by dsimp [N]; omega),
    sub_zero,sub_zero,Real.norm_eq_abs,Real.norm_eq_abs] at h
  exact h

theorem hypergeomProxyQuotient_abs_bound (k m r : ℕ) (hmk : m≤k) (hm : 0<m)
    (t : ℝ) (ht : t≠0) :
    |hypergeomProxyQuotient (k+m+r) k m t|≤2*(m:ℝ)/|t| := by
  have h := hypergeomCenteredLogMGF_linear_bound k m r hmk hm t
  unfold hypergeomProxyQuotient
  rw [Function.update_of_ne ht,abs_div,abs_mul,abs_pow]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (div_le_iff₀ (sq_pos_of_ne_zero (abs_ne_zero.mpr ht))).2
  have ha : 0 < |t| := abs_pos.mpr ht
  have he : (2*(m:ℝ)/|t|)*|t|^2=2*(m:ℝ)*|t| := by field_simp
  rw [he]
  linarith

theorem hypergeomProxyQuotient_tendsto_atTop (k m r : ℕ) (hmk : m≤k) (hm : 0<m) :
    Tendsto (hypergeomProxyQuotient (k+m+r) k m) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun t => abs_nonneg _))
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    exact hypergeomProxyQuotient_abs_bound k m r hmk hm t (ne_of_gt ht)
  · exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => 2*(m:ℝ)) atTop (𝓝 (2*(m:ℝ)))).div_atTop
      tendsto_abs_atTop_atTop

theorem hypergeomProxyQuotient_tendsto_atBot (k m r : ℕ) (hmk : m≤k) (hm : 0<m) :
    Tendsto (hypergeomProxyQuotient (k+m+r) k m) atBot (𝓝 0) := by
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall (fun t => abs_nonneg _))
  · filter_upwards [eventually_lt_atBot (0:ℝ)] with t ht
    exact hypergeomProxyQuotient_abs_bound k m r hmk hm t (ne_of_lt ht)
  · exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => 2*(m:ℝ)) atBot (𝓝 (2*(m:ℝ)))).div_atTop
      tendsto_abs_atBot_atTop

end
end ExactHoeffding
