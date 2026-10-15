import ExactHoeffding.ActualProxyTail
import ExactHoeffding.RescaledCompactConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Localization of all actual globally maximizing tilts

The comparison outside each neighborhood of zero is proved, not assumed.
It uses a compact annulus and the population-uniform actual support tail.
This module does not yet assert uniqueness or an analytic critical branch.
-/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

theorem rescaledProxyExtension_compact_gap (m : ℕ) (hm : 0 < m) (s : ℝ)
    (K : Set ℝ) (hK : IsCompact K) (hzero : ∀ t ∈ K, t ≠ 0) :
    ∀ᶠ e in 𝓝 (0 : ℝ), ∀ t ∈ K,
      rescaledProxyExtension m s e t < rescaledProxyExtension m s e 0 := by
  apply hK.eventually_forall_of_forall_eventually
  intro t ht
  have hbase : ContinuousAt
      (fun u : ℝ × ℝ => rescaledProxyExtension m s u.1 0) (0, t) :=
    (rescaledProxyExtension_joint_continuous_axis m s 0).comp_of_eq
      (continuousAt_fst.prodMk continuousAt_const) rfl
  exact (rescaledProxyExtension_joint_continuous_axis m s t).eventually_lt hbase
    (rescaledProxyExtension_limit_strict m hm s t (hzero t ht))

/-- For sufficiently small inverse population, every actual competitor outside
`(-δ,δ)` is strictly worse than tilt zero. No maximizer is assumed here. -/
theorem actualHypergeomProxy_eventually_outside_lt_zero
    (m : ℕ) (hmpos : 0 < m) (s δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
      2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
      2 * (k : ℝ) + s = (N : ℝ) → ∀ t : ℝ, δ ≤ |t| →
        actualHypergeomProxy N k m t < actualHypergeomProxy N k m 0 := by
  let K : Set ℝ := Icc (-16) 16 ∩ {t : ℝ | δ ≤ |t|}
  have hK : IsCompact K :=
    isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  have hzero : ∀ t ∈ K, t ≠ 0 := by
    intro t ht htz
    have h := ht.2
    simp only [mem_ofPred_eq, htz, abs_zero] at h
    linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hinsert : ContinuousAt (fun e : ℝ => (e, (0 : ℝ))) 0 :=
    continuousAt_id.prodMk continuousAt_const
  have hbase : ContinuousAt (fun e : ℝ => rescaledProxyExtension m s e 0) 0 := by
    exact ContinuousAt.comp
      (f := fun e : ℝ => (e, (0 : ℝ)))
      (g := fun u : ℝ × ℝ => rescaledProxyExtension m s u.1 u.2)
      (x := (0 : ℝ)) (rescaledProxyExtension_joint_continuous_axis m s 0) hinsert
  have hbasepos : ∀ᶠ e in 𝓝 (0 : ℝ),
      (m : ℝ) / 8 < rescaledProxyExtension m s e 0 := by
    apply continuousAt_const.eventually_lt hbase
    rw [rescaledProxyExtension_at_zero]
    linarith
  filter_upwards [rescaledProxyExtension_compact_gap m hmpos s K hK hzero,
    hbasepos] with e hgap hbasee
  intro N k hN hk hm he hbalance t htδ
  have hbridge (u : ℝ) : rescaledProxyExtension m s e u =
      actualHypergeomProxy N k m u := by
    rw [he]
    exact rescaledProxyExtension_hypergeom N k m s u hN hk hm hmpos hbalance
  by_cases ht16 : |t| ≤ 16
  · rw [← hbridge t, ← hbridge 0]
    exact hgap t ⟨abs_le.mp ht16, htδ⟩
  · have habs : 16 < |t| := lt_of_not_ge ht16
    have ht : t ≠ 0 := by
      intro hz
      have habs0 : (16 : ℝ) < 0 := by simpa only [hz, abs_zero] using habs
      linarith
    have htail := actualHypergeomProxy_tail_bound N k m (by omega) hk hm t ht
    have hsmall : 2 * (m : ℝ) / |t| ≤ (m : ℝ) / 8 := by
      apply (div_le_iff₀ (by linarith : 0 < |t|)).mpr
      nlinarith
    rw [hbridge 0] at hbasee
    exact lt_of_le_of_lt (htail.trans hsmall) hbasee

/-- Along every admissible population sequence tending to infinity, all global
maximizers eventually lie in each prescribed neighborhood of zero. -/
theorem actualHypergeomProxy_global_maximizers_localize
    (m : ℕ) (hmpos : 0 < m) (s δ : ℝ) (hδ : 0 < δ)
    (K : ℕ → ℕ) (hvalid : ∀ᶠ N in atTop,
      K N ≤ N ∧ m ≤ N ∧ 2 * (K N : ℝ) + s = (N : ℝ)) :
    ∀ᶠ N in atTop, ∀ t : ℝ,
      (∀ u : ℝ, actualHypergeomProxy N (K N) m u ≤
        actualHypergeomProxy N (K N) m t) → |t| < δ := by
  have he : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [he.eventually
    (actualHypergeomProxy_eventually_outside_lt_zero m hmpos s δ hδ),
    hvalid, eventually_ge_atTop 2] with N hloc hv hN
  intro t hmax
  by_contra hnot
  have hlt := hloc N (K N) hN hv.1 hv.2.1 rfl hv.2.2 t (le_of_not_gt hnot)
  exact (not_lt_of_ge (hmax 0)) hlt

end

end ExactHoeffding
