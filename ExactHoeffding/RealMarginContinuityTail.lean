import ExactHoeffding.RealMarginActualProxy
import ExactHoeffding.ActualProxyTail

/-! # Continuity and global tilt tails for the actual real-margin law -/

namespace ExactHoeffding
noncomputable section
open Filter Finset
open scoped Topology

/-- Joint analyticity holds on the whole balanced tilt axis, including its
removable origin. -/
theorem realMarginProxy_joint_analytic_axis (N m : ℕ) (hN : 5 ≤ N)
    (hm : 2*m ≤ N) (t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => realMarginProxy N m u.1 u.2) (0,t) := by
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  by_cases ht : t = 0
  · subst t; exact realMarginProxy_joint_analytic N m hden
  have hmass (i : ℕ) : AnalyticAt ℝ
      (fun u : ℝ × ℝ => realMarginMass m (1/(N:ℝ)) ((1-u.1)/2) i) (0,t) := by
    exact (realMarginMass_joint_analytic m i (1/(N:ℝ),(1-(0:ℝ))/2) hden).comp_of_eq
      (analyticAt_const.prod ((analyticAt_const.sub analyticAt_fst).div_const)) rfl
  have hmgf : AnalyticAt ℝ (fun u : ℝ × ℝ => finiteMGF (range (m+1))
      (realMarginMass m (1/(N:ℝ)) ((1-u.1)/2)) (fun i => (i:ℝ)) u.2) (0,t) := by
    unfold finiteMGF
    apply Finset.analyticAt_fun_sum
    intro i hi
    exact (hmass i).mul (analyticAt_rexp.comp ((analyticAt_snd.mul analyticAt_const) :
      AnalyticAt ℝ (fun u : ℝ×ℝ => u.2*(i:ℝ)) (0,t)))
  obtain ⟨hw,hs⟩ := realMarginMass_near_balanced_probability N m (by omega) hm 0 (by
    simp only [abs_zero]
    have : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
    positivity)
  have hpos := finiteMGF_pos_of_normalized (range (m+1))
    (realMarginMass m (1/(N:ℝ)) ((1-0)/2)) (fun i => (i:ℝ)) hw hs t
  have hlog : AnalyticAt ℝ (fun u : ℝ×ℝ => Real.log (finiteMGF (range (m+1))
      (realMarginMass m (1/(N:ℝ)) ((1-u.1)/2)) (fun i=>(i:ℝ)) u.2)) (0,t) :=
    (analyticAt_log hpos).comp_of_eq hmgf rfl
  have hmean : AnalyticAt ℝ (fun u : ℝ × ℝ => (m:ℝ)*((1-u.1)/2)) (0,t) :=
    analyticAt_const.mul ((analyticAt_const.sub analyticAt_fst).div_const)
  have hquot : AnalyticAt ℝ (fun u : ℝ × ℝ =>
      2*realMarginCenteredLogMGF N m u.1 u.2/u.2^2) (0,t) := by
    exact (analyticAt_const.mul (hlog.sub (hmean.mul analyticAt_snd))).div
      (analyticAt_snd.pow 2) (pow_ne_zero 2 ht)
  apply hquot.congr
  filter_upwards [(continuousAt_snd : ContinuousAt (fun u : ℝ × ℝ => u.2) (0,t)).eventually_ne ht]
    with u hu
  exact (realMarginProxy_eq_quotient N m u.1 u.2 hden hu).symm

/-- The actual finite support controls every large tilt, uniformly over a
fixed nonzero interval of real success margins. -/
theorem realMarginProxy_tail_bound (N m : ℕ) (hN : 5 ≤ N) (hm : 2*m ≤ N)
    (d t : ℝ) (hd : |d| < 1/(N:ℝ)) (ht : t ≠ 0) :
    realMarginProxy N m d t ≤ 4*(m:ℝ)/|t| := by
  obtain ⟨hw,hs⟩ := realMarginMass_near_balanced_probability N m (by omega) hm d hd
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have hbound := finiteMGF_le_exp_abs_bound (range (m+1))
    (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) (fun i => (i:ℝ)) m t hw hs (by
      intro i hi
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (i:ℝ))]
      exact_mod_cast (show i≤m from Nat.le_of_lt_succ (mem_range.mp hi)))
  have hpos := finiteMGF_pos_of_normalized (range (m+1))
    (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) (fun i => (i:ℝ)) hw hs t
  have hlog := (Real.log_le_iff_le_exp hpos).mpr hbound
  have hNr : (5:ℝ)≤N := by exact_mod_cast hN
  have hd1 : |d| ≤ 1 := by
    have : 1/(N:ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    exact hd.le.trans this
  have hmu : |(m:ℝ)*((1-d)/2)| ≤ m := by
    rw [abs_le] at hd1 ⊢
    constructor <;> nlinarith [show (0:ℝ)≤m by positivity]
  have hshift : -((m:ℝ)*((1-d)/2)*t) ≤ |t| *(m:ℝ) := by
    calc
      -((m:ℝ)*((1-d)/2)*t) ≤ |(m:ℝ)*((1-d)/2)*t| := neg_le_abs _
      _ = |(m:ℝ)*((1-d)/2)| *|t| := abs_mul _ _
      _ ≤ |t| *(m:ℝ) := by nlinarith [abs_nonneg t]
  rw [realMarginProxy_eq_quotient N m d t hden ht]
  have hc : realMarginCenteredLogMGF N m d t ≤ 2*|t| *(m:ℝ) := by
    unfold realMarginCenteredLogMGF
    linarith
  calc
    2*realMarginCenteredLogMGF N m d t/t^2 ≤ 2*(2*|t| *(m:ℝ))/t^2 :=
      div_le_div_of_nonneg_right (by linarith) (sq_nonneg t)
    _ = 4*(m:ℝ)/|t| := by rw [← sq_abs t]; field_simp; ring

end
end ExactHoeffding
