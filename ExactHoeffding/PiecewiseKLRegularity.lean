import ExactHoeffding.PiecewiseKLComparison
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! # Regularity of the actual canonical stitched KL rate

The tangent correction matches values and slopes at each explicit switch.
Equality of the two variance envelopes matches the second derivatives.
-/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology ContDiff

private theorem hasDerivAt_ite_lt_contact {f g : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (hfg : f c = g c) :
    HasDerivAt (fun x => if x < c then f x else g x) d c := by
  have hl : HasDerivWithinAt (fun x => if x < c then f x else g x) d (Iio c) c := by
    apply hf.hasDerivWithinAt.congr
    · intro x hx
      exact if_pos hx
    · simpa only [lt_self_iff_false, if_false] using hfg.symm
  have hr : HasDerivWithinAt (fun x => if x < c then f x else g x) d (Ici c) c := by
    apply hg.hasDerivWithinAt.congr_of_mem
    · intro x hx
      exact if_neg (not_lt.mpr hx)
    · simp only [Set.mem_Ici, le_refl]
  have h := hl.union hr
  simpa only [Iio_union_Ici, hasDerivWithinAt_univ] using! h

private theorem hasDerivAt_ite_le_contact {f g : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c) (hfg : f c = g c) :
    HasDerivAt (fun x => if x ≤ c then f x else g x) d c := by
  have h := hasDerivAt_ite_lt_contact hf hg hfg
  apply h.congr_of_eventuallyEq
  exact Eventually.of_forall (fun x => by
    rcases lt_trichotomy x c with hx | rfl | hx
    · simp [hx, hx.le]
    · simp [hfg]
    · simp [not_le.mpr hx, not_lt.mpr hx.le])

/-- The slope of the tangent-corrected three-branch rate. -/
noncomputable def piecewiseKLSlope (sP sB : ℝ → ℝ) (rm rp v : ℝ) : ℝ :=
  if v < rm then sB v + sP rm - sB rm
  else if v ≤ rp then sP v
  else sB v + sP rp - sB rp

private theorem outerRate_hasDerivAt {IP IB sP sB : ℝ → ℝ} {c v : ℝ}
    (hB : HasDerivAt IB (sB v) v) :
    HasDerivAt (fun x => IB x + IP c - IB c + (x-c)*(sP c-sB c))
      (sB v+sP c-sB c) v := by
  have h := ((hB.add_const (IP c)).sub_const (IB c)).add
    (((hasDerivAt_id v).sub_const c).mul_const (sP c-sB c))
  apply h.congr_deriv
  simp only [one_mul]
  ring

/-- Matching the value and tangent slope makes the rate differentiable even
at either switching point; no derivative of the piecewise target is assumed. -/
theorem piecewiseKLRate_hasDerivAt {IP IB sP sB : ℝ → ℝ} {rm rp v : ℝ}
    (hroot : rm < rp) (hP : HasDerivAt IP (sP v) v)
    (hB : HasDerivAt IB (sB v) v) :
    HasDerivAt (piecewiseKLRate IP IB sP sB rm rp)
      (piecewiseKLSlope sP sB rm rp v) v := by
  by_cases hl : v < rm
  · have h := outerRate_hasDerivAt (IP := IP) (sP := sP) (c := rm) hB
    have heq : piecewiseKLRate IP IB sP sB rm rp =ᶠ[𝓝 v]
        (fun x => IB x + IP rm - IB rm + (x-rm)*(sP rm-sB rm)) := by
      filter_upwards [eventually_lt_nhds hl] with x hx
      exact piecewiseKLRate_eq_left hx
    simpa only [piecewiseKLSlope, if_pos hl] using! h.congr_of_eventuallyEq heq
  · by_cases hleft : v = rm
    · subst v
      have hout := outerRate_hasDerivAt (IP := IP) (sP := sP) (c := rm) hB
      have hout' : HasDerivAt
          (fun x => IB x + IP rm - IB rm + (x-rm)*(sP rm-sB rm)) (sP rm) rm := by
        convert hout using 1; ring
      have hval : (IB rm + IP rm - IB rm + (rm-rm)*(sP rm-sB rm)) = IP rm := by ring
      have h := hasDerivAt_ite_lt_contact hout' hP hval
      have heq : piecewiseKLRate IP IB sP sB rm rp =ᶠ[𝓝 rm]
          (fun x => if x < rm then
            IB x + IP rm - IB rm + (x-rm)*(sP rm-sB rm) else IP x) := by
        filter_upwards [eventually_lt_nhds hroot] with x hx
        simp only [piecewiseKLRate, if_pos hx.le]
      simpa only [piecewiseKLSlope, lt_self_iff_false, if_false, if_pos hroot.le]
        using! h.congr_of_eventuallyEq heq
    · have hvl : rm < v := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm hleft)
      by_cases hr : v < rp
      · have heq : piecewiseKLRate IP IB sP sB rm rp =ᶠ[𝓝 v] IP := by
          filter_upwards [eventually_gt_nhds hvl, eventually_lt_nhds hr] with x hxl hxr
          exact piecewiseKLRate_eq_central hxl.le hxr.le
        simpa only [piecewiseKLSlope, if_neg hl, if_pos hr.le]
          using! hP.congr_of_eventuallyEq heq
      · by_cases hright : v = rp
        · subst v
          have hout := outerRate_hasDerivAt (IP := IP) (sP := sP) (c := rp) hB
          have hout' : HasDerivAt
              (fun x => IB x + IP rp - IB rp + (x-rp)*(sP rp-sB rp)) (sP rp) rp := by
            convert hout using 1; ring
          have hval : IP rp = (IB rp + IP rp - IB rp + (rp-rp)*(sP rp-sB rp)) := by ring
          have h := hasDerivAt_ite_le_contact hP hout' hval
          have heq : piecewiseKLRate IP IB sP sB rm rp =ᶠ[𝓝 rp]
              (fun x => if x ≤ rp then IP x else
                IB x + IP rp - IB rp + (x-rp)*(sP rp-sB rp)) := by
            filter_upwards [eventually_gt_nhds hroot] with x hx
            simp only [piecewiseKLRate, if_neg (not_lt.mpr hx.le)]
          simpa only [piecewiseKLSlope, if_neg (not_lt.mpr hroot.le), le_refl, if_true]
            using! h.congr_of_eventuallyEq heq
        · have hrv : rp < v := lt_of_le_of_ne (le_of_not_gt hr) (Ne.symm hright)
          have h := outerRate_hasDerivAt (IP := IP) (sP := sP) (c := rp) hB
          have heq : piecewiseKLRate IP IB sP sB rm rp =ᶠ[𝓝 v]
              (fun x => IB x + IP rp - IB rp + (x-rp)*(sP rp-sB rp)) := by
            filter_upwards [eventually_gt_nhds hrv] with x hx
            exact piecewiseKLRate_eq_right hx hroot.le
          simpa only [piecewiseKLSlope, if_neg hl, if_neg (not_le.mpr hrv)]
            using! h.congr_of_eventuallyEq heq

private theorem outerSlope_hasDerivAt {sP sB dsB : ℝ → ℝ} {c v : ℝ}
    (hB : HasDerivAt sB (dsB v) v) :
    HasDerivAt (fun x => sB x+sP c-sB c) (dsB v) v := by
  exact (hB.add_const (sP c)).sub_const (sB c)

/-- The derivative of the stitched slope exists at both contacts precisely
when the two branch curvatures agree there. -/
theorem piecewiseKLSlope_hasDerivAt {sP sB dsP dsB : ℝ → ℝ} {rm rp v : ℝ}
    (hroot : rm < rp) (hP : HasDerivAt sP (dsP v) v)
    (hB : HasDerivAt sB (dsB v) v)
    (hm : dsP rm = dsB rm) (hp : dsP rp = dsB rp) :
    HasDerivAt (piecewiseKLSlope sP sB rm rp)
      (if v < rm then dsB v else if v ≤ rp then dsP v else dsB v) v := by
  by_cases hl : v < rm
  · have h := outerSlope_hasDerivAt (sP := sP) (c := rm) hB
    have heq : piecewiseKLSlope sP sB rm rp =ᶠ[𝓝 v]
        (fun x => sB x+sP rm-sB rm) := by
      filter_upwards [eventually_lt_nhds hl] with x hx
      simp only [piecewiseKLSlope, if_pos hx]
    simpa only [if_pos hl] using! h.congr_of_eventuallyEq heq
  · by_cases hleft : v = rm
    · subst v
      have hout := outerSlope_hasDerivAt (sP := sP) (c := rm) hB
      rw [← hm] at hout
      have hval : sB rm+sP rm-sB rm = sP rm := by ring
      have h := hasDerivAt_ite_lt_contact hout hP hval
      have heq : piecewiseKLSlope sP sB rm rp =ᶠ[𝓝 rm]
          (fun x => if x < rm then sB x+sP rm-sB rm else sP x) := by
        filter_upwards [eventually_lt_nhds hroot] with x hx
        simp only [piecewiseKLSlope, if_pos hx.le]
      simpa only [lt_self_iff_false, if_false, if_pos hroot.le]
        using! h.congr_of_eventuallyEq heq
    · have hvl : rm < v := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm hleft)
      by_cases hr : v < rp
      · have heq : piecewiseKLSlope sP sB rm rp =ᶠ[𝓝 v] sP := by
          filter_upwards [eventually_gt_nhds hvl, eventually_lt_nhds hr] with x hxl hxr
          simp only [piecewiseKLSlope, if_neg (not_lt.mpr hxl.le), if_pos hxr.le]
        simpa only [if_neg hl, if_pos hr.le] using! hP.congr_of_eventuallyEq heq
      · by_cases hright : v = rp
        · subst v
          have hout := outerSlope_hasDerivAt (sP := sP) (c := rp) hB
          rw [← hp] at hout
          have hval : sP rp = sB rp+sP rp-sB rp := by ring
          have h := hasDerivAt_ite_le_contact hP hout hval
          have heq : piecewiseKLSlope sP sB rm rp =ᶠ[𝓝 rp]
              (fun x => if x ≤ rp then sP x else sB x+sP rp-sB rp) := by
            filter_upwards [eventually_gt_nhds hroot] with x hx
            simp only [piecewiseKLSlope, if_neg (not_lt.mpr hx.le)]
          simpa only [if_neg (not_lt.mpr hroot.le), le_refl, if_true]
            using! h.congr_of_eventuallyEq heq
        · have hrv : rp < v := lt_of_le_of_ne (le_of_not_gt hr) (Ne.symm hright)
          have h := outerSlope_hasDerivAt (sP := sP) (c := rp) hB
          have heq : piecewiseKLSlope sP sB rm rp =ᶠ[𝓝 v]
              (fun x => sB x+sP rp-sB rp) := by
            filter_upwards [eventually_gt_nhds hrv] with x hx
            simp only [piecewiseKLSlope, if_neg (by linarith : ¬x<rm), if_neg (not_le.mpr hx)]
          simpa only [if_neg hl, if_neg (not_le.mpr hrv)]
            using! h.congr_of_eventuallyEq heq

/-- The explicit left switch is a true contact of the variance envelopes. -/
theorem klQuadraticEnvelope_eq_binomial_switchMinus {N k m : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    klQuadraticEnvelope N k m
      (varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)) =
    klBinomialEnvelope m
      (varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)) := by
  apply sub_eq_zero.mp
  rw [kl_variance_envelope_difference N k m _ (by linarith)]
  simpa only [varianceSwitchMinus, add_sub_cancel_left] using
    varianceEnvelopeDifference_at_root_minus (klSwitchC_pos N m hm hhalf)
      (klSwitchB_pos N k m hm hmk hk hhalf)

/-- The explicit right switch is a true contact of the variance envelopes. -/
theorem klQuadraticEnvelope_eq_binomial_switchPlus {N k m : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    klQuadraticEnvelope N k m
      (varianceSwitchPlus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)) =
    klBinomialEnvelope m
      (varianceSwitchPlus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)) := by
  apply sub_eq_zero.mp
  rw [kl_variance_envelope_difference N k m _ (by linarith)]
  simpa only [varianceSwitchPlus, add_sub_cancel_left] using
    varianceEnvelopeDifference_at_root_plus (klSwitchC_pos N m hm hhalf)
      (klSwitchB_pos N k m hm hmk hk hhalf)

/-- The explicit first derivative of the canonical rate. -/
noncomputable def canonicalPiecewiseSlope (N k m v : ℝ) : ℝ :=
  piecewiseKLSlope
    (scaledKLSlope (envelopeM N m) (k/N) (envelopeScale N m) (m*k/N))
    (binomialKLSlope m (k/N))
    (varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m))
    (varianceSwitchPlus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)) v

/-- The canonical rate has its explicit stitched first derivative throughout
its open support, including both exact switching points. -/
theorem canonicalPiecewiseRate_hasDerivAt {N k m v : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hv : v ∈ Ioo 0 m) :
    HasDerivAt (canonicalPiecewiseRate N k m) (canonicalPiecewiseSlope N k m v) v := by
  have hroots := kl_switching_points_full_domain N k m hm hmk hk hhalf
  have hN : 0 < N := by linarith
  have hm0 : 0 < m := by linarith
  have hM := envelopeM_positive N m hm hhalf
  have ha : 0 < envelopeScale N m := div_pos (by linarith) (by linarith)
  have hp : 0 < k/N := div_pos (by linarith) hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith)
  exact piecewiseKLRate_hasDerivAt (lt_trans hroots.2.1 hroots.2.2.1)
    (scaledKLRate_hasDerivAt hM ha hp hp1
      (scaledKL_argument_mem_Ioo hm hmk hk hhalf hv.1.le hv.2.le))
    (binomialKLRate_hasDerivAt hm0 hp hp1 hv.1 hv.2)

/-- Both second-derivative branches agree at the switches. The second
 derivative is the reciprocal of the smaller actual variance envelope. -/
theorem canonicalPiecewiseSlope_hasDerivAt {N k m v : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hv : v ∈ Ioo 0 m) :
    HasDerivAt (canonicalPiecewiseSlope N k m)
      (1 / min (klQuadraticEnvelope N k m v) (klBinomialEnvelope m v)) v := by
  have hroots := kl_switching_points_full_domain N k m hm hmk hk hhalf
  have hN : 0 < N := by linarith
  have hm0 : 0 < m := by linarith
  have hp : 0 < k/N := div_pos (by linarith) hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith)
  have h := piecewiseKLSlope_hasDerivAt
    (dsP := fun u => 1 / klQuadraticEnvelope N k m u)
    (dsB := fun u => 1 / klBinomialEnvelope m u)
    (lt_trans hroots.2.1 hroots.2.2.1)
    (scaledKLSlope_hasDerivAt_canonical hm hmk hk hhalf hv.1.le hv.2.le)
    (binomialKLSlope_hasDerivAt hm0 hp hp1 hv.1 hv.2)
    (congrArg (fun x : ℝ => 1/x) (klQuadraticEnvelope_eq_binomial_switchMinus hm hmk hk hhalf))
    (congrArg (fun x : ℝ => 1/x) (klQuadraticEnvelope_eq_binomial_switchPlus hm hmk hk hhalf))
  convert h using 1
  · rfl
  · split_ifs with hl hr
    · rw [min_eq_right (klQuadraticEnvelope_gt_binomial_outside hm hmk hk hhalf (Or.inl hl)).le]
    · rw [min_eq_left ((kl_quadratic_envelope_le_binomial_iff N k m v hm hmk hk hhalf).2
        ⟨le_of_not_gt hl, hr⟩)]
    · rw [min_eq_right (klQuadraticEnvelope_gt_binomial_outside hm hmk hk hhalf
        (Or.inr (lt_of_not_ge hr))).le]

/-- The second derivative of the actual canonical rate on its complete open
support. In particular, this equality holds at both explicit splice points. -/
theorem canonicalPiecewiseRate_second_deriv {N k m v : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hv : v ∈ Ioo 0 m) :
    deriv (deriv (canonicalPiecewiseRate N k m)) v =
      1 / min (klQuadraticEnvelope N k m v) (klBinomialEnvelope m v) := by
  have heq : deriv (canonicalPiecewiseRate N k m) =ᶠ[𝓝 v] canonicalPiecewiseSlope N k m := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with u hu
    exact (canonicalPiecewiseRate_hasDerivAt hm hmk hk hhalf hu).deriv
  exact heq.deriv_eq.trans (canonicalPiecewiseSlope_hasDerivAt hm hmk hk hhalf hv).deriv

/-- The reciprocal-envelope curvature is continuous across the exact roots,
because the two positive polynomial envelopes meet there. -/
theorem canonicalPiecewiseCurvature_continuousOn {N k m : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    ContinuousOn (fun v => 1 / min (klQuadraticEnvelope N k m v)
      (klBinomialEnvelope m v)) (Ioo 0 m) := by
  have hP : Continuous (klQuadraticEnvelope N k m) := by
    unfold klQuadraticEnvelope varianceBarrier
    fun_prop
  have hB : Continuous (klBinomialEnvelope m) := by
    unfold klBinomialEnvelope
    fun_prop
  apply continuousOn_const.div (hP.min hB).continuousOn
  intro v hv
  apply ne_of_gt
  apply lt_min
  · exact klQuadraticEnvelope_pos hm hmk hk hhalf hv.1.le hv.2.le
  · unfold klBinomialEnvelope
    exact div_pos (mul_pos hv.1 (sub_pos.mpr hv.2)) (by linarith)

/-- The manuscript's stitched KL rate is twice continuously differentiable
on the whole open support, including both explicit switching points. -/
theorem canonicalPiecewiseRate_contDiffOn_two {N k m : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    ContDiffOn ℝ 2 (canonicalPiecewiseRate N k m) (Ioo 0 m) := by
  have hfirst : ∀ v ∈ Ioo 0 m, HasDerivAt (canonicalPiecewiseRate N k m)
      (canonicalPiecewiseSlope N k m v) v :=
    fun v hv => canonicalPiecewiseRate_hasDerivAt hm hmk hk hhalf hv
  have hslope : ∀ v ∈ Ioo 0 m, HasDerivAt (canonicalPiecewiseSlope N k m)
      (1 / min (klQuadraticEnvelope N k m v) (klBinomialEnvelope m v)) v :=
    fun v hv => canonicalPiecewiseSlope_hasDerivAt hm hmk hk hhalf hv
  have hsmooth : ContDiffOn ℝ 1 (canonicalPiecewiseSlope N k m) (Ioo 0 m) := by
    apply (contDiffOn_one_iff_derivWithin isOpen_Ioo.uniqueDiffOn).2
    refine ⟨fun v hv => (hslope v hv).differentiableAt.differentiableWithinAt, ?_⟩
    apply (canonicalPiecewiseCurvature_continuousOn hm hmk hk hhalf).congr
    intro v hv
    exact (hslope v hv).hasDerivWithinAt.derivWithin
      (isOpen_Ioo.uniqueDiffOn v hv)
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl,
    contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun v hv => (hfirst v hv).differentiableAt.differentiableWithinAt, ?_, ?_⟩
  · intro h
    norm_num at h
  · exact hsmooth.congr (fun v hv => (hfirst v hv).deriv)

end
end ExactHoeffding
