import ExactHoeffding.JointFullAxisAnalytic

/-! # Actual probability neighborhoods and uniform tails along the full axis -/

namespace ExactHoeffding
noncomputable section
open Filter Set
open scoped Topology

theorem realMarginMass_eventually_positive_free_axis (m : ℕ) (d₀ : ℝ)
    (hd₀ : d₀ ∈ Ioo (-1 : ℝ) 1) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0, d₀),
      scaledFalling 1 p.1 m ≠ 0 ∧ |p.2| < 1 ∧
      (∀ i ∈ Finset.range (m+1), 0 < realMarginMass m p.1 (jointSuccessFraction p.2) i) := by
  have hden : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, d₀), scaledFalling 1 p.1 m ≠ 0 :=
    (rescaledPopulationDenom_joint_analytic m (0, d₀)).continuousAt.eventually_ne (by simp)
  have hd : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, d₀), |p.2| < 1 :=
    continuousAt_snd.abs.eventually_lt continuousAt_const (abs_lt.mpr hd₀)
  have hmass : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, d₀),
      ∀ i ∈ Finset.range (m+1), 0 < realMarginMass m p.1 (jointSuccessFraction p.2) i := by
    apply (Finset.range (m+1)).eventually_all.mpr
    intro i hi
    have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have ha : AnalyticAt ℝ (fun p : ℝ × ℝ =>
        realMarginMass m p.1 (jointSuccessFraction p.2) i) (0, d₀) :=
      (realMarginMass_joint_analytic m i (0, jointSuccessFraction d₀) (by simp)).comp_of_eq
        (f := fun p : ℝ × ℝ => (p.1, jointSuccessFraction p.2))
        (analyticAt_fst.prod ((analyticAt_const.sub analyticAt_snd).div_const)) (by
          simp [jointSuccessFraction])
    have hzero : 0 < realMarginMass m 0 (jointSuccessFraction d₀) i := by
      apply realMarginMass_pos m 0 _ _ _ (by simp) i him
      · intro j hj
        simp only [mul_zero, sub_zero]
        unfold jointSuccessFraction
        linarith [hd₀.1, hd₀.2]
      · intro j hj
        simp only [mul_zero, sub_zero]
        unfold jointSuccessFraction
        linarith [hd₀.1, hd₀.2]
    exact continuousAt_const.eventually_lt ha.continuousAt hzero
  filter_upwards [hden, hd, hmass] with p hp hd hm
  exact ⟨hp, hd, hm⟩

theorem jointProxyExtension_eventually_tail_bound_free_axis (m : ℕ) (hm : 1 ≤ m)
    (d₀ : ℝ) (hd₀ : d₀ ∈ Ioo (-1 : ℝ) 1) :
    ∀ᶠ p : ℝ × ℝ in 𝓝 (0, d₀), ∀ t : ℝ, t ≠ 0 →
      jointProxyExtension m p.1 p.2 t ≤ 2*(m : ℝ)/|t| := by
  filter_upwards [realMarginMass_eventually_positive_free_axis m d₀ hd₀] with p hp
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


end
end ExactHoeffding
