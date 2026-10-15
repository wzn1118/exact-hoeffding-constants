import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set
open scoped Topology

namespace ExactHoeffding

/-- An integrating factor propagates a scalar differential inequality in both
time directions from a zero initial value. -/
theorem linear_subsolution_comparison
    {h h' K q : ℝ → ℝ} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hc : ContinuousOn h (Icc a b)) (hqc : ContinuousOn q (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (hqd : ∀ x ∈ Ioo a b, HasDerivAt q (K x) x)
    (hi : ∀ x ∈ Ioo a b, h' x ≤ K x * h x) (hz : h c = 0) :
    (∀ x ∈ Icc a c, 0 ≤ h x) ∧ (∀ x ∈ Icc c b, h x ≤ 0) := by
  let g : ℝ → ℝ := fun x => Real.exp (-q x) * h x
  have hgc : ContinuousOn g (Icc a b) := hqc.neg.rexp.mul hc
  have hgd : ∀ x ∈ Ioo a b,
      HasDerivAt g (Real.exp (-q x) * (h' x - K x * h x)) x := by
    intro x hx
    have hcalc := (hqd x hx).neg.exp.mul (hd x hx)
    have heq : (Real.exp (-q x) * -(K x)) * h x + Real.exp (-q x) * h' x =
        Real.exp (-q x) * (h' x - K x * h x) := by ring
    exact hcalc.congr_deriv heq
  have hganti : AntitoneOn g (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hgc
      (fun x hx => (hgd x (by simpa only [interior_Icc, mem_Ioo] using hx)).hasDerivWithinAt)
      (fun x hx => mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (hi x (by simpa only [interior_Icc, mem_Ioo] using hx))))
  have hgz : g c = 0 := by simp [g, hz]
  constructor
  · intro x hx
    have hle := hganti ⟨hx.1, hx.2.trans hcb⟩ ⟨hac, hcb⟩ hx.2
    rw [hgz] at hle
    dsimp [g] at hle
    exact nonneg_of_mul_nonneg_right hle (Real.exp_pos _)
  · intro x hx
    have hle := hganti ⟨hac, hcb⟩ ⟨hac.trans hx.1, hx.2⟩ hx.1
    rw [hgz] at hle
    dsimp [g] at hle
    exact nonpos_of_mul_nonpos_right hle (Real.exp_pos _)

/-- Continuous coefficients supply the integrating factor through an interval
integral, so the comparison hypothesis contains no assumed comparison. -/
theorem linear_subsolution_comparison_of_continuous
    {h h' K : ℝ → ℝ} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (hc : ContinuousOn h (Icc a b)) (hK : Continuous K)
    (hd : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (hi : ∀ x ∈ Ioo a b, h' x ≤ K x * h x) (hz : h c = 0) :
    (∀ x ∈ Icc a c, 0 ≤ h x) ∧ (∀ x ∈ Icc c b, h x ≤ 0) := by
  let q : ℝ → ℝ := fun x => ∫ s in c..x, K s
  have hqd : ∀ x, HasDerivAt q (K x) x := fun x =>
    (hK.integral_hasStrictDerivAt c x).hasDerivAt
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun x => (hqd x).continuousAt
  exact linear_subsolution_comparison hac hcb hc hqc.continuousOn hd
    (fun x _ => hqd x) hi hz

/-- Comparison with a quadratic Riccati trajectory. The same differential
inequality yields opposite mean comparisons on opposite sides of the origin. -/
theorem quadratic_riccati_mean_comparison
    {y Y dy dY : ℝ → ℝ} {A B C a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (hyc : Continuous y) (hYc : Continuous Y)
    (hyd : ∀ x ∈ Ioo a b, HasDerivAt y (dy x) x)
    (hYd : ∀ x ∈ Ioo a b, HasDerivAt Y (dY x) x)
    (hsub : ∀ x ∈ Ioo a b, dy x ≤ A + B * y x - C * (y x)^2)
    (hsol : ∀ x ∈ Ioo a b, dY x = A + B * Y x - C * (Y x)^2)
    (hinit : y 0 = Y 0) :
    (∀ x ∈ Icc a 0, Y x ≤ y x) ∧ (∀ x ∈ Icc 0 b, y x ≤ Y x) := by
  have hK : Continuous (fun x => B - C * (y x + Y x)) :=
    continuous_const.sub (continuous_const.mul (hyc.add hYc))
  have hi : ∀ x ∈ Ioo a b,
      dy x - dY x ≤ (B - C * (y x + Y x)) * (y x - Y x) := by
    intro x hx
    rw [hsol x hx]
    nlinarith [hsub x hx]
  have hcmp := linear_subsolution_comparison_of_continuous ha hb
    (hyc.sub hYc).continuousOn hK (fun x hx => (hyd x hx).sub (hYd x hx))
    hi (sub_eq_zero.mpr hinit)
  exact ⟨fun x hx => sub_nonneg.mp (hcmp.1 x hx),
    fun x hx => sub_nonpos.mp (hcmp.2 x hx)⟩

/-- Integrating the two mean comparisons gives the same log-Laplace upper
bound on both sides of zero. -/
theorem log_laplace_le_of_mean_comparison
    {F G y Y : ℝ → ℝ} {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b)
    (hFc : ContinuousOn F (Icc a b)) (hGc : ContinuousOn G (Icc a b))
    (hFd : ∀ x ∈ Ioo a b, HasDerivAt F (y x) x)
    (hGd : ∀ x ∈ Ioo a b, HasDerivAt G (Y x) x)
    (hleft : ∀ x ∈ Icc a 0, Y x ≤ y x)
    (hright : ∀ x ∈ Icc 0 b, y x ≤ Y x)
    (hzero : F 0 = G 0) : ∀ x ∈ Icc a b, F x ≤ G x := by
  let H : ℝ → ℝ := fun x => F x - G x
  have hHc : ContinuousOn H (Icc a b) := hFc.sub hGc
  have hHz : H 0 = 0 := sub_eq_zero.mpr hzero
  have hmono : MonotoneOn H (Icc a 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a 0)
      (hHc.mono (Icc_subset_Icc le_rfl hb))
      (fun x hx => ((hFd x ⟨(show a < x ∧ x < 0 from by simpa only [interior_Icc, mem_Ioo] using hx).1,
        (show a < x ∧ x < 0 from by simpa only [interior_Icc, mem_Ioo] using hx).2.trans_le hb⟩).sub
        (hGd x ⟨(show a < x ∧ x < 0 from by simpa only [interior_Icc, mem_Ioo] using hx).1,
        (show a < x ∧ x < 0 from by simpa only [interior_Icc, mem_Ioo] using hx).2.trans_le hb⟩)).hasDerivWithinAt)
      (fun x hx => sub_nonneg.mpr (hleft x
        (Ioo_subset_Icc_self (by simpa only [interior_Icc, mem_Ioo] using hx))))
  have hanti : AntitoneOn H (Icc 0 b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 b)
      (hHc.mono (Icc_subset_Icc ha le_rfl))
      (fun x hx => ((hFd x ⟨ha.trans_lt
        (show 0 < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).1,
        (show 0 < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).2⟩).sub
        (hGd x ⟨ha.trans_lt
        (show 0 < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).1,
        (show 0 < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).2⟩)).hasDerivWithinAt)
      (fun x hx => sub_nonpos.mpr (hright x
        (Ioo_subset_Icc_self (by simpa only [interior_Icc, mem_Ioo] using hx))))
  intro x hx
  apply sub_nonpos.mp
  change H x ≤ 0
  rw [← hHz]
  rcases le_total x 0 with hx0 | hx0
  · exact hmono ⟨hx.1, hx0⟩ ⟨ha, le_rfl⟩ hx0
  · exact hanti ⟨le_rfl, hb⟩ ⟨hx0, hx.2⟩ hx0

/-- A strict scalar differential inequality away from the initial time gives
strict comparison at every other time, including interval endpoints. -/
theorem strict_linear_subsolution_comparison
    {h h' K q : ℝ → ℝ} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hc : ContinuousOn h (Icc a b)) (hqc : ContinuousOn q (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x)
    (hqd : ∀ x ∈ Ioo a b, HasDerivAt q (K x) x)
    (hi : ∀ x ∈ Ioo a b, x ≠ c → h' x < K x * h x) (hz : h c = 0) :
    (∀ x ∈ Ico a c, 0 < h x) ∧ (∀ x ∈ Ioc c b, h x < 0) := by
  let g : ℝ → ℝ := fun x => Real.exp (-q x) * h x
  have hgc : ContinuousOn g (Icc a b) := hqc.neg.rexp.mul hc
  have hgd : ∀ x ∈ Ioo a b,
      HasDerivAt g (Real.exp (-q x) * (h' x - K x * h x)) x := by
    intro x hx
    have hcalc := (hqd x hx).neg.exp.mul (hd x hx)
    have heq : (Real.exp (-q x) * -(K x)) * h x + Real.exp (-q x) * h' x =
        Real.exp (-q x) * (h' x - K x * h x) := by ring
    exact hcalc.congr_deriv heq
  have hgl : StrictAntiOn g (Icc a c) :=
    strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc a c)
      (hgc.mono (Icc_subset_Icc le_rfl hcb.le))
      (fun x hx => (hgd x ⟨(show a < x ∧ x < c from by simpa only [interior_Icc, mem_Ioo] using hx).1,
        (show a < x ∧ x < c from by simpa only [interior_Icc, mem_Ioo] using hx).2.trans hcb⟩).hasDerivWithinAt)
      (fun x hx => mul_neg_of_pos_of_neg (Real.exp_pos _)
        (sub_neg.mpr (hi x
          ⟨(show a < x ∧ x < c from by simpa only [interior_Icc, mem_Ioo] using hx).1,
          (show a < x ∧ x < c from by simpa only [interior_Icc, mem_Ioo] using hx).2.trans hcb⟩
          (ne_of_lt (show a < x ∧ x < c from by simpa only [interior_Icc, mem_Ioo] using hx).2))))
  have hgr : StrictAntiOn g (Icc c b) :=
    strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc c b)
      (hgc.mono (Icc_subset_Icc hac.le le_rfl))
      (fun x hx => (hgd x ⟨hac.trans
        (show c < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).1,
        (show c < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).2⟩).hasDerivWithinAt)
      (fun x hx => mul_neg_of_pos_of_neg (Real.exp_pos _)
        (sub_neg.mpr (hi x
          ⟨hac.trans (show c < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).1,
          (show c < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).2⟩
          (ne_of_gt (show c < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).1))))
  have hgz : g c = 0 := by simp [g, hz]
  constructor
  · intro x hx
    have hlt := hgl ⟨hx.1, hx.2.le⟩ ⟨hac.le, le_rfl⟩ hx.2
    rw [hgz] at hlt
    dsimp [g] at hlt
    exact pos_of_mul_pos_right hlt (Real.exp_pos _).le
  · intro x hx
    have hlt := hgr ⟨le_rfl, hcb.le⟩ ⟨hx.1.le, hx.2⟩ hx.1
    rw [hgz] at hlt
    dsimp [g] at hlt
    exact neg_of_mul_neg_right hlt (Real.exp_pos _).le

/-- Strict quadratic Riccati comparison away from zero. -/
theorem strict_quadratic_riccati_mean_comparison
    {y Y dy dY : ℝ → ℝ} {A B C a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hyc : Continuous y) (hYc : Continuous Y)
    (hyd : ∀ x ∈ Ioo a b, HasDerivAt y (dy x) x)
    (hYd : ∀ x ∈ Ioo a b, HasDerivAt Y (dY x) x)
    (hsub : ∀ x ∈ Ioo a b, x ≠ 0 → dy x < A + B * y x - C * (y x)^2)
    (hsol : ∀ x ∈ Ioo a b, dY x = A + B * Y x - C * (Y x)^2)
    (hinit : y 0 = Y 0) :
    (∀ x ∈ Ico a 0, Y x < y x) ∧ (∀ x ∈ Ioc 0 b, y x < Y x) := by
  let K : ℝ → ℝ := fun x => B - C * (y x + Y x)
  have hK : Continuous K := continuous_const.sub (continuous_const.mul (hyc.add hYc))
  let q : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, K s
  have hqd : ∀ x, HasDerivAt q (K x) x := fun x =>
    (hK.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun x => (hqd x).continuousAt
  have hi : ∀ x ∈ Ioo a b, x ≠ 0 →
      dy x - dY x < K x * (y x - Y x) := by
    intro x hx hx0
    rw [hsol x hx]
    dsimp [K]
    nlinarith [hsub x hx hx0]
  have hcmp := strict_linear_subsolution_comparison ha hb
    (hyc.sub hYc).continuousOn hqc.continuousOn
    (fun x hx => (hyd x hx).sub (hYd x hx)) (fun x _ => hqd x)
    hi (sub_eq_zero.mpr hinit)
  exact ⟨fun x hx => sub_pos.mp (hcmp.1 x hx),
    fun x hx => sub_neg.mp (hcmp.2 x hx)⟩

/-- Strict mean comparison makes the two-sided log-Laplace bound strict at
every nonzero argument. -/
theorem log_laplace_lt_of_strict_mean_comparison
    {F G y Y : ℝ → ℝ} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hFc : ContinuousOn F (Icc a b)) (hGc : ContinuousOn G (Icc a b))
    (hFd : ∀ x ∈ Ioo a b, HasDerivAt F (y x) x)
    (hGd : ∀ x ∈ Ioo a b, HasDerivAt G (Y x) x)
    (hleft : ∀ x ∈ Ioo a 0, Y x < y x)
    (hright : ∀ x ∈ Ioo 0 b, y x < Y x)
    (hzero : F 0 = G 0) : ∀ x ∈ Icc a b, x ≠ 0 → F x < G x := by
  let H : ℝ → ℝ := fun x => F x - G x
  have hHc : ContinuousOn H (Icc a b) := hFc.sub hGc
  have hHz : H 0 = 0 := sub_eq_zero.mpr hzero
  have hmono : StrictMonoOn H (Icc a 0) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc a 0)
      (hHc.mono (Icc_subset_Icc le_rfl hb.le))
      (fun x hx => ((hFd x ⟨(show a < x ∧ x < 0 from by simpa only [interior_Icc, mem_Ioo] using hx).1,
        (show a < x ∧ x < 0 from by simpa only [interior_Icc, mem_Ioo] using hx).2.trans hb⟩).sub
        (hGd x ⟨(show a < x ∧ x < 0 from by simpa only [interior_Icc, mem_Ioo] using hx).1,
        (show a < x ∧ x < 0 from by simpa only [interior_Icc, mem_Ioo] using hx).2.trans hb⟩)).hasDerivWithinAt)
      (fun x hx => sub_pos.mpr (hleft x (by simpa only [interior_Icc, mem_Ioo] using hx)))
  have hanti : StrictAntiOn H (Icc 0 b) :=
    strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 b)
      (hHc.mono (Icc_subset_Icc ha.le le_rfl))
      (fun x hx => ((hFd x ⟨ha.trans
        (show 0 < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).1,
        (show 0 < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).2⟩).sub
        (hGd x ⟨ha.trans
        (show 0 < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).1,
        (show 0 < x ∧ x < b from by simpa only [interior_Icc, mem_Ioo] using hx).2⟩)).hasDerivWithinAt)
      (fun x hx => sub_neg.mpr (hright x (by simpa only [interior_Icc, mem_Ioo] using hx)))
  intro x hx hx0
  apply sub_neg.mp
  change H x < 0
  rw [← hHz]
  rcases lt_or_gt_of_ne hx0 with hx0 | hx0
  · exact hmono ⟨hx.1, hx0.le⟩ ⟨ha.le, le_rfl⟩ hx0
  · exact hanti ⟨le_rfl, hb.le⟩ ⟨hx0.le, hx.2⟩ hx0

/-- A quadratic bound on the derivative of a centered tilted mean, together
with the matching Riccati solution, bounds its log-Laplace primitive. -/
theorem quadratic_riccati_log_laplace_domination
    {F G y Y dy dY : ℝ → ℝ} {A B C : ℝ}
    (hyc : Continuous y) (hYc : Continuous Y)
    (hyd : ∀ x, HasDerivAt y (dy x) x)
    (hYd : ∀ x, HasDerivAt Y (dY x) x)
    (hFd : ∀ x, HasDerivAt F (y x) x)
    (hGd : ∀ x, HasDerivAt G (Y x) x)
    (hsub : ∀ x, dy x ≤ A + B * y x - C * (y x)^2)
    (hsol : ∀ x, dY x = A + B * Y x - C * (Y x)^2)
    (hinit : y 0 = Y 0) (hzero : F 0 = G 0) : ∀ x, F x ≤ G x := by
  intro x
  let a := min x 0
  let b := max x 0
  have ha : a ≤ 0 := min_le_right _ _
  have hb : 0 ≤ b := le_max_right _ _
  have hcmp := quadratic_riccati_mean_comparison ha hb hyc hYc
    (fun t _ => hyd t) (fun t _ => hYd t) (fun t _ => hsub t)
    (fun t _ => hsol t) hinit
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hFd t).continuousAt
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun t => (hGd t).continuousAt
  exact log_laplace_le_of_mean_comparison ha hb hFc.continuousOn hGc.continuousOn
    (fun t _ => hFd t) (fun t _ => hGd t) hcmp.1 hcmp.2 hzero x
    ⟨min_le_left _ _, le_max_left _ _⟩

/-- Strict quadratic Riccati comparison gives strict log-Laplace domination
at every nonzero argument on the entire real line. -/
theorem strict_quadratic_riccati_log_laplace_domination
    {F G y Y dy dY : ℝ → ℝ} {A B C : ℝ}
    (hyc : Continuous y) (hYc : Continuous Y)
    (hyd : ∀ x, HasDerivAt y (dy x) x)
    (hYd : ∀ x, HasDerivAt Y (dY x) x)
    (hFd : ∀ x, HasDerivAt F (y x) x)
    (hGd : ∀ x, HasDerivAt G (Y x) x)
    (hsub : ∀ x, x ≠ 0 → dy x < A + B * y x - C * (y x)^2)
    (hsol : ∀ x, dY x = A + B * Y x - C * (Y x)^2)
    (hinit : y 0 = Y 0) (hzero : F 0 = G 0) : ∀ x, x ≠ 0 → F x < G x := by
  intro x hx0
  let a := min x 0 - 1
  let b := max x 0 + 1
  have ha : a < 0 := by dsimp [a]; linarith [min_le_right x 0]
  have hb : 0 < b := by dsimp [b]; linarith [le_max_right x 0]
  have hcmp := strict_quadratic_riccati_mean_comparison ha hb hyc hYc
    (fun t _ => hyd t) (fun t _ => hYd t) (fun t _ => hsub t)
    (fun t _ => hsol t) hinit
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun t => (hFd t).continuousAt
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun t => (hGd t).continuousAt
  have hax : a ≤ x := by dsimp [a]; linarith [min_le_left x 0]
  have hxb : x ≤ b := by dsimp [b]; linarith [le_max_left x 0]
  exact log_laplace_lt_of_strict_mean_comparison ha hb hFc.continuousOn hGc.continuousOn
    (fun t _ => hFd t) (fun t _ => hGd t)
    (fun t ht => hcmp.1 t ⟨ht.1.le, ht.2⟩)
    (fun t ht => hcmp.2 t ⟨ht.1, ht.2.le⟩) hzero x ⟨hax, hxb⟩ hx0


end ExactHoeffding
