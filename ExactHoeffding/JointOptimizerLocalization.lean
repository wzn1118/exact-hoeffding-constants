import ExactHoeffding.JointParameterSymmetry
import Mathlib.Analysis.Convex.Deriv

/-! # Uniform global localization for the actual real-margin proxy -/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

/-- The real-margin coefficients are strictly positive and normalized on a
full two-parameter neighborhood of the balanced infinite-population law. -/
theorem realMarginMass_eventually_positive (m : ℕ) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      scaledFalling 1 p.1 m ≠ 0 ∧ |p.2| < 1 ∧
      (∀ i ∈ Finset.range (m+1), 0 < realMarginMass m p.1 (jointSuccessFraction p.2) i) := by
  have hden : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), scaledFalling 1 p.1 m ≠ 0 :=
    (rescaledPopulationDenom_joint_analytic m (0, 0)).continuousAt.eventually_ne (by simp)
  have hd : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), |p.2| < 1 :=
    continuousAt_snd.abs.eventually_lt continuousAt_const (by norm_num)
  have hmass : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      ∀ i ∈ Finset.range (m+1), 0 < realMarginMass m p.1 (jointSuccessFraction p.2) i := by
    apply (Finset.range (m+1)).eventually_all.mpr
    intro i hi
    have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have ha : AnalyticAt ℝ (fun p : ℝ × ℝ =>
        realMarginMass m p.1 (jointSuccessFraction p.2) i) (0, 0) :=
      (realMarginMass_joint_analytic m i (0, (1/2 : ℝ)) (by simp)).comp_of_eq
        (f := fun p : ℝ × ℝ => (p.1, jointSuccessFraction p.2))
        (analyticAt_fst.prod ((analyticAt_const.sub analyticAt_snd).div_const)) (by
          simp [jointSuccessFraction])
    have hzero : 0 < realMarginMass m 0 (jointSuccessFraction 0) i := by
      apply realMarginMass_pos m 0 _ _ _ (by simp) i him
      · intro j hj
        norm_num [jointSuccessFraction]
      · intro j hj
        norm_num [jointSuccessFraction]
    exact continuousAt_const.eventually_lt ha.continuousAt hzero
  filter_upwards [hden, hd, hmass] with p hp hd hm
  exact ⟨hp, hd, hm⟩

/-- Joint analyticity holds along the entire limiting tilt axis, including
its removable origin. -/
theorem jointProxyObjective_analytic_axis (m : ℕ) (t : ℝ) :
    AnalyticAt ℝ (jointProxyObjective m) ((0, 0), t) := by
  by_cases hm0 : m=0
  · subst m
    have hz : jointProxyObjective 0 = (fun _ : (ℝ × ℝ) × ℝ => (0 : ℝ)) := by
      funext u
      simp [jointProxyObjective, jointProxyExtension, jointMGFSlope,
        jointMGFQuadratic, jointMean, jointSuccessFraction]
    rw [hz]
    exact analyticAt_const
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  by_cases ht : t=0
  · subst t
    exact jointProxyObjective_analytic m
  have hM : AnalyticAt ℝ (fun u : (ℝ × ℝ) × ℝ =>
      jointMGF m u.1.1 u.1.2 u.2) ((0, 0), t) :=
    (jointMGF_analytic m 0 t).comp_of_eq
      (f := fun u : (ℝ × ℝ) × ℝ => (u.1.1, (u.1.2, u.2)))
      ((analyticAt_fst.comp analyticAt_fst).prod
        ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)) rfl
  have hpos : 0 < jointMGF m 0 0 t := by
    rw [jointMGF_at_zero]
    simp only [jointSuccessFraction]
    positivity
  have hmean : AnalyticAt ℝ (fun u : (ℝ × ℝ) × ℝ =>
      jointMean m u.1.1 u.1.2) ((0, 0), t) := by
    unfold jointMean jointSuccessFraction
    exact analyticAt_const.mul ((analyticAt_const.sub
      (analyticAt_snd.comp analyticAt_fst)).div_const)
  have hquot : AnalyticAt ℝ (fun u : (ℝ × ℝ) × ℝ =>
      2*(Real.log (jointMGF m u.1.1 u.1.2 u.2)-jointMean m u.1.1 u.1.2*u.2)/u.2^2)
      ((0, 0), t) := by
    have hlog : AnalyticAt ℝ (fun u : (ℝ × ℝ) × ℝ =>
        Real.log (jointMGF m u.1.1 u.1.2 u.2)) ((0, 0), t) :=
      (analyticAt_log hpos).comp_of_eq hM rfl
    exact (analyticAt_const.mul (hlog.sub
      (hmean.mul analyticAt_snd))).div (analyticAt_snd.pow 2) (pow_ne_zero 2 ht)
  apply hquot.congr
  filter_upwards [(continuousAt_snd : ContinuousAt
    (fun u : (ℝ × ℝ) × ℝ => u.2) ((0, 0), t)).eventually_ne ht] with u hu
  exact (jointProxyExtension_eq_quotient m hm u.1.1 u.1.2 u.2 hu).symm

theorem jointProxyExtension_compact_gap (m : ℕ) (hm : 0 < m)
    (K : Set ℝ) (hK : IsCompact K) (hzero : ∀ t ∈ K, t ≠ 0) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), ∀ t ∈ K,
      jointProxyExtension m p.1 p.2 t < jointProxyExtension m p.1 p.2 0 := by
  apply hK.eventually_forall_of_forall_eventually
  intro t ht
  have hbase : ContinuousAt (fun u : (ℝ × ℝ) × ℝ =>
      jointProxyExtension m u.1.1 u.1.2 0) ((0, 0), t) :=
    (jointProxyObjective_analytic_axis m 0).continuousAt.comp_of_eq
      (f := fun u : (ℝ × ℝ) × ℝ => (u.1, (0 : ℝ)))
      (continuousAt_fst.prodMk continuousAt_const) rfl
  apply (jointProxyObjective_analytic_axis m t).continuousAt.eventually_lt hbase
  change jointProxyExtension m 0 0 t < jointProxyExtension m 0 0 0
  rw [jointProxyExtension_balanced_axis]
  exact rescaledProxyExtension_limit_strict m hm 0 t (hzero t ht)

/-- The same support tail bound applies to every nearby real probability
law, uniformly in both independent parameters. -/
theorem jointProxyExtension_eventually_tail_bound (m : ℕ) (hm : 1 ≤ m) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), ∀ t : ℝ, t ≠ 0 →
      jointProxyExtension m p.1 p.2 t ≤ 2*(m : ℝ)/|t| := by
  filter_upwards [realMarginMass_eventually_positive m] with p hp
  intro t ht
  let w := realMarginMass m p.1 (jointSuccessFraction p.2)
  let μ := jointMean m p.1 p.2
  have hw : ∀ i ∈ Finset.range (m+1), 0 ≤ w i := fun i hi => (hp.2.2 i hi).le
  have hs : ∑ i ∈ Finset.range (m+1), w i = 1 := realMarginMass_sum m _ _ hp.1
  have hμ0 : 0 ≤ μ := by
    dsimp [μ, jointMean, jointSuccessFraction]
    have hd := (abs_lt.mp hp.2.1).2
    positivity
  have hμm : μ ≤ m := by
    dsimp [μ, jointMean, jointSuccessFraction]
    have hd := (abs_lt.mp hp.2.1).1
    nlinarith [show (0 : ℝ) ≤ m by positivity]
  have hb : ∀ i ∈ Finset.range (m+1), |(i : ℝ)-μ| ≤ m := by
    intro i hi
    have hi0 : (0 : ℝ) ≤ i := by positivity
    have him : (i : ℝ) ≤ m := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hshift : finiteMGF (Finset.range (m+1)) w (fun i => (i : ℝ)-μ) t =
      Real.exp (t*(-μ))*jointMGF m p.1 p.2 t := by
    rw [jointMGF_realMargin m p.1 p.2 t hp.1]
    simpa only [sub_eq_add_neg] using
      finiteMGF_shift (Finset.range (m+1)) w (fun i : ℕ => (i : ℝ)) t (-μ)
  have hMpos : 0 < jointMGF m p.1 p.2 t := by
    rw [jointMGF_realMargin m p.1 p.2 t hp.1]
    exact finiteMGF_pos_of_normalized _ _ _ hw hs t
  have hlog : Real.log (finiteMGF (Finset.range (m+1)) w (fun i => (i : ℝ)-μ) t) =
      Real.log (jointMGF m p.1 p.2 t)-μ*t := by
    rw [hshift, Real.log_mul (Real.exp_ne_zero _) hMpos.ne', Real.log_exp]
    ring
  rw [jointProxyExtension_eq_quotient m hm p.1 p.2 t ht, ← hlog]
  exact finite_logMGF_proxy_tail_bound _ w _ m t hw hs hb ht

/-- Every global competitor outside a prescribed tilt neighborhood is
strictly worse than zero, uniformly in a full neighborhood of `(e,d)=(0,0)`. -/
theorem jointProxyExtension_eventually_outside_lt_zero
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0), ∀ t : ℝ, δ ≤ |t| →
      jointProxyExtension m p.1 p.2 t < jointProxyExtension m p.1 p.2 0 := by
  let K : Set ℝ := Icc (-16) 16 ∩ {t : ℝ | δ ≤ |t|}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hzero : ∀ t ∈ K, t ≠ 0 := by
    intro t ht hz
    have h := ht.2
    simp only [mem_ofPred_eq, hz, abs_zero] at h
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hbase : ContinuousAt (fun p : ℝ × ℝ => jointProxyExtension m p.1 p.2 0) (0, 0) :=
    (jointProxyObjective_analytic m).continuousAt.comp_of_eq
      (f := fun p : ℝ × ℝ => (p, (0 : ℝ)))
      (continuousAt_id.prodMk continuousAt_const) rfl
  have hbasepos : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      (m : ℝ)/8 < jointProxyExtension m p.1 p.2 0 := by
    apply continuousAt_const.eventually_lt hbase
    rw [jointProxyExtension_balanced_axis, rescaledProxyExtension_at_zero]
    linarith
  filter_upwards [jointProxyExtension_compact_gap m hm K hK hzero,
    jointProxyExtension_eventually_tail_bound m hm, hbasepos] with p hgap htail hbasep
  intro t htδ
  by_cases ht16 : |t| ≤ 16
  · exact hgap t ⟨abs_le.mp ht16, htδ⟩
  · have habs : 16 < |t| := lt_of_not_ge ht16
    have ht : t ≠ 0 := by
      intro hz
      simp only [hz, abs_zero] at habs
      linarith
    have hsmall : 2*(m : ℝ)/|t| ≤ (m : ℝ)/8 := by
      apply (div_le_iff₀ (by linarith : 0 < |t|)).mpr
      nlinarith
    exact lt_of_le_of_lt ((htail t ht).trans hsmall) hbasep

end

end ExactHoeffding
