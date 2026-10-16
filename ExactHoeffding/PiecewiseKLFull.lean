import ExactHoeffding.PiecewiseKLEndToEnd
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set
open scoped Topology

namespace ExactHoeffding
noncomputable section

/-- Riccati comparison on a right-hand interval when the initial values are
ordered rather than equal. -/
theorem quadratic_riccati_mean_comparison_right_initial_le
    {y Y dy dY : ℝ → ℝ} {A B C b : ℝ} (hb : 0 ≤ b)
    (hyc : Continuous y) (hYc : Continuous Y)
    (hyd : ∀ x ∈ Ioo 0 b, HasDerivAt y (dy x) x)
    (hYd : ∀ x ∈ Ioo 0 b, HasDerivAt Y (dY x) x)
    (hsub : ∀ x ∈ Ioo 0 b, dy x ≤ A + B * y x - C * (y x)^2)
    (hsol : ∀ x ∈ Ioo 0 b, dY x = A + B * Y x - C * (Y x)^2)
    (hinit : y 0 ≤ Y 0) :
    ∀ x ∈ Icc 0 b, y x ≤ Y x := by
  let h : ℝ → ℝ := fun x => y x - Y x
  have hcont : Continuous h := hyc.sub hYc
  have hderiv : ∀ x ∈ Ioo 0 b, HasDerivAt h (dy x - dY x) x := by
    intro x hx
    exact (hyd x hx).sub (hYd x hx)
  have hK : Continuous (fun x => B - C * (y x + Y x)) :=
    continuous_const.sub (continuous_const.mul (hyc.add hYc))
  have hi : ∀ x ∈ Ioo 0 b,
      dy x - dY x ≤ (B - C * (y x + Y x)) * (y x - Y x) := by
    intro x hx
    rw [hsol x hx]
    nlinarith [hsub x hx]
  let q : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, (B - C * (y s + Y s))
  have hqd : ∀ x, HasDerivAt q (B - C * (y x + Y x)) x := fun x =>
    ((hK.integral_hasStrictDerivAt 0 x).hasDerivAt)
  have hqc : Continuous q := continuous_iff_continuousAt.mpr fun x => (hqd x).continuousAt
  let g : ℝ → ℝ := fun x => Real.exp (-q x) * h x
  have hgd : ∀ x ∈ Ioo 0 b,
      HasDerivAt g (Real.exp (-q x) * ((dy x - dY x) -
        (B - C * (y x + Y x)) * (y x - Y x))) x := by
    intro x hx
    have hcalc := (hqd x).neg.exp.mul (hderiv x hx)
    have heq : (Real.exp (-q x) * -(B - C * (y x + Y x))) * h x +
        Real.exp (-q x) * (dy x - dY x) =
        Real.exp (-q x) * ((dy x - dY x) -
          (B - C * (y x + Y x)) * (y x - Y x)) := by
      dsimp [h]
      ring
    exact hcalc.congr_deriv heq
  have hgc : ContinuousOn g (Icc 0 b) := hqc.neg.rexp.mul hcont |>.continuousOn
  have hganti : AntitoneOn g (Icc 0 b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 b) hgc
      (fun x hx => (hgd x (by simpa only [interior_Icc, mem_Ioo] using hx)).hasDerivWithinAt)
      (fun x hx => mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (hi x (by simpa only [interior_Icc, mem_Ioo] using hx))))
  intro x hx
  have hle := hganti ⟨le_rfl, hb⟩ hx hx.1
  have hg0 : g 0 ≤ 0 := by
    dsimp [g, h]
    simp [q]
    linarith
  have hgx : g x ≤ 0 := hle.trans hg0
  dsimp [g] at hgx
  have hpos : 0 < Real.exp (-q x) := Real.exp_pos _
  have hneg : h x * Real.exp (-q x) ≤ 0 := by simpa [mul_comm] using hgx
  have hh : h x ≤ 0 := nonpos_of_mul_nonpos_left hneg hpos
  dsimp [h] at hh
  linarith

/-- Integrating a right-hand mean comparison with an ordered initial value. -/
theorem log_laplace_le_right_initial_le
    {F G y Y : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hFc : Continuous F) (hGc : Continuous G)
    (hFd : ∀ x ∈ Ioo 0 b, HasDerivAt F (y x) x)
    (hGd : ∀ x ∈ Ioo 0 b, HasDerivAt G (Y x) x)
    (hright : ∀ x ∈ Icc 0 b, y x ≤ Y x)
    (hzero : F 0 ≤ G 0) : ∀ x ∈ Icc 0 b, F x ≤ G x := by
  let H : ℝ → ℝ := fun x => F x - G x
  have hHc : ContinuousOn H (Icc 0 b) := (hFc.sub hGc).continuousOn
  have hanti : AntitoneOn H (Icc 0 b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 b) hHc
      (fun x hx => ((hFd x (by simpa only [interior_Icc, mem_Ioo] using hx)).sub
        (hGd x (by simpa only [interior_Icc, mem_Ioo] using hx))).hasDerivWithinAt)
      (fun x hx => sub_nonpos.mpr (hright x
        (Ioo_subset_Icc_self (by simpa only [interior_Icc, mem_Ioo] using hx))))
  intro x hx
  have hle := hanti ⟨le_rfl, hb⟩ hx hx.1
  have hz : H 0 ≤ 0 := sub_nonpos.mpr hzero
  have hHx : H x ≤ 0 := hle.trans hz
  dsimp [H] at hHx
  linarith

lemma scaledBernoulliMean_at_fenchel
    {M p a x : ℝ} (hM : 0 < M) (ha : 0 < a)
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1) :
    scaledBernoulliMean M p a (bernoulliFenchelTilt p x / a) = M / a * (x-p) := by
  have he : Real.exp (a * (bernoulliFenchelTilt p x / a)) =
      (x * (1-p)) / (p * (1-x)) := by
    rw [show a * (bernoulliFenchelTilt p x / a) = bernoulliFenchelTilt p x by field_simp]
    exact Real.exp_log (div_pos (mul_pos hx (sub_pos.mpr hp1))
      (mul_pos hp (sub_pos.mpr hx1)))
  unfold scaledBernoulliMean scaledBernoulliDenom
  rw [he]
  field_simp [ne_of_gt hM, ne_of_gt ha, ne_of_gt hp,
    ne_of_gt (sub_pos.mpr hp1), ne_of_gt hx, ne_of_gt (sub_pos.mpr hx1)]
  ring

lemma scaledBernoulliLogLaplace_at_fenchel
    {M p a x : ℝ} (hM : 0 < M) (ha : 0 < a)
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1) :
    scaledBernoulliLogLaplace M p a (bernoulliFenchelTilt p x / a) =
      (bernoulliFenchelTilt p x / a) * (M / a * (x-p)) -
        (M / a^2) * bernoulliKL p x := by
  have he' : Real.exp (bernoulliFenchelTilt p x) =
      (x * (1-p)) / (p * (1-x)) := by
    exact Real.exp_log (div_pos (mul_pos hx (sub_pos.mpr hp1))
      (mul_pos hp (sub_pos.mpr hx1)))
  unfold scaledBernoulliLogLaplace scaledBernoulliDenom
  rw [show a * (bernoulliFenchelTilt p x / a) = bernoulliFenchelTilt p x by field_simp]
  rw [he']
  have hid := bernoulli_fenchel_identity p x hp hp1 hx hx1
  have hlog : Real.log ((1-p) + p * ((x * (1-p)) / (p * (1-x)))) =
      Real.log (1-p) - Real.log (1-x) := by
    rw [show (1-p) + p * ((x * (1-p)) / (p * (1-x))) = (1-p)/(1-x) by
      field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr hx1)]; ring]
    exact Real.log_div (ne_of_gt (sub_pos.mpr hp1)) (ne_of_gt (sub_pos.mpr hx1))
  rw [hlog]
  have hlog_mgf : Real.log (bernoulliMGF p (bernoulliFenchelTilt p x)) =
      Real.log (1-p) - Real.log (1-x) := by
    rw [bernoulli_mgf_at_fenchel_tilt p x hp hp1 hx hx1]
    exact Real.log_div (ne_of_gt (sub_pos.mpr hp1)) (ne_of_gt (sub_pos.mpr hx1))
  unfold bernoulliCenteredLogMGF at hid
  rw [hlog_mgf] at hid
  field_simp [ne_of_gt hM, ne_of_gt ha, ne_of_gt hp,
    ne_of_gt (sub_pos.mpr hp1), ne_of_gt hx, ne_of_gt (sub_pos.mpr hx1)] at *
  ring_nf at *
  linarith

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

lemma envelope_scaled_mark_lt_one {N m : ℝ} (hm : 3 ≤ m) (hhalf : 2*m < N) :
    envelopeScale N m * m / envelopeM N m < 1 := by
  have hN : 0 < N := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hN2 : 0 < N-2 := by linarith
  have hNm : 0 < N-m := by linarith
  have hM : 0 < envelopeM N m := envelopeM_positive N m hm hhalf
  have ha : 0 < envelopeScale N m := by
    unfold envelopeScale
    positivity
  unfold envelopeScale envelopeM
  field_simp [ne_of_gt hN1, ne_of_gt hN2, ne_of_gt hNm]
  have hid : (N-2)*(N-m) - (N-2*m)*(N-1) = N*(m-1) := by ring
  rw [show (N-2)*(N-m) = (N-2*m)*(N-1) + N*(m-1) by linarith]
  have hm1 : 0 < m-1 := by linarith
  have hNm2 : 0 < N-2 := by linarith
  have hprod : 0 < N*(m-1) := mul_pos hN hm1
  have hprod2 : 0 < (N-2)*(N-m) := mul_pos hNm2 hNm
  nlinarith

lemma bernoulliFenchelTilt_strictMono {p x z : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1)
    (hz : 0 < z) (hz1 : z < 1) (hxz : x < z) :
    bernoulliFenchelTilt p x < bernoulliFenchelTilt p z := by
  unfold bernoulliFenchelTilt
  apply Real.strictMonoOn_log
  · exact div_pos (mul_pos hx (sub_pos.mpr hp1))
      (mul_pos hp (sub_pos.mpr hx1))
  · exact div_pos (mul_pos hz (sub_pos.mpr hp1))
      (mul_pos hp (sub_pos.mpr hz1))
  · apply (div_lt_div_iff₀ (mul_pos hp (sub_pos.mpr hx1))
      (mul_pos hp (sub_pos.mpr hz1))).2
    field_simp [ne_of_gt hp, ne_of_gt (sub_pos.mpr hx1), ne_of_gt (sub_pos.mpr hz1)]
    nlinarith

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- A quadratic-envelope trajectory can be followed by a translated Bernoulli
trajectory after a contact point.  This is the analytic outer-branch bridge. -/
theorem stitched_right_loglaplace_increment
    {F y V : ℝ → ℝ} {M p a L q τP τB yR : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hL : 0 < L) (hq : 0 < q) (hq1 : q < 1)
    (hp : 0 < p) (hp1 : p < 1)
    (hFcont : Continuous F) (hycont : Continuous y)
    (hVd : ∀ t : ℝ, HasDerivAt y (V t) t)
    (hFd : ∀ t : ℝ, HasDerivAt F (y t) t)
    (hF0 : F 0 = 0) (hy0 : y 0 = 0)
    (hFglobal : ∀ t : ℝ, F t ≤ scaledBernoulliLogLaplace M p a t)
    (hPbound : ∀ t : ℝ,
      V t ≤ M*p*(1-p) + a*(1-2*p)*y t - a^2/M*(y t)^2)
    (hBbound : ∀ t : ℝ,
      V t ≤ L*q*(1-q) + (1-2*q)*y t - (y t)^2/L)
    (hτP : 0 ≤ τP) (hτB : 0 ≤ τB)
    (hPcontact : scaledBernoulliMean M p a τP = yR)
    (hBcontact : scaledBernoulliMean L q 1 τB = yR) :
    ∀ s : ℝ, 0 ≤ s →
      F (τP+s) ≤ F τP +
        (scaledBernoulliLogLaplace L q 1 (τB+s) -
          scaledBernoulliLogLaplace L q 1 τB) := by
  let YP : ℝ → ℝ := scaledBernoulliMean M p a
  have hYPc : Continuous YP := scaledBernoulliMean_continuous
    (ne_of_gt hM) (ne_of_gt ha) hp hp1
  have hYPd : ∀ t ∈ Ioo 0 τP, HasDerivAt YP
      (M*p*(1-p) + a*(1-2*p)*YP t - a^2/M*(YP t)^2) t := by
    intro t ht
    exact scaledBernoulliMean_hasDerivAt (ne_of_gt hM) (ne_of_gt ha) hp hp1 t
  have hyP := quadratic_riccati_mean_comparison (a := 0) (b := τP)
    (le_rfl) hτP hycont hYPc
    (fun t ht => hVd t) hYPd (fun t ht => hPbound t)
    (fun t ht => rfl) (by simpa [YP] using hy0)
  have hycontact : y τP ≤ yR := by
    have h := hyP.2 τP ⟨hτP, le_rfl⟩
    simpa [YP, hPcontact] using h
  have houter : ∀ b : ℝ, 0 ≤ b → ∀ z ∈ Icc 0 b,
      F (τP+z) - F τP ≤
        scaledBernoulliLogLaplace L q 1 (τB+z) -
          scaledBernoulliLogLaplace L q 1 τB := by
    intro b hb z hz
    let YB : ℝ → ℝ := (scaledBernoulliMean L q 1) ∘ (fun s : ℝ => τB+s)
    have hbaseB : Continuous (scaledBernoulliMean L q 1) :=
      scaledBernoulliMean_continuous (ne_of_gt hL) one_ne_zero hq hq1
    have hYBc : Continuous YB := by
      exact hbaseB.comp (continuous_const.add continuous_id)
    have hYBd : ∀ s : ℝ, HasDerivAt YB
        (L*q*(1-q) + (1-2*q)*YB s - (YB s)^2/L) s := by
      intro s
      have hh := scaledBernoulliMean_hasDerivAt (M := L) (p := q) (a := (1:ℝ))
        (ne_of_gt hL) one_ne_zero hq hq1 (τB+s)
      have hc := hh.comp s (hasDerivAt_const s τB |>.add (hasDerivAt_id s))
      simpa [YB, Function.comp_def, div_eq_mul_inv, mul_comm] using hc
    let yS : ℝ → ℝ := y ∘ (fun s : ℝ => τP+s)
    have hySc : Continuous yS := hycont.comp (continuous_const.add continuous_id)
    have hySd : ∀ s : ℝ, HasDerivAt yS (V (τP+s)) s := by
      intro s
      have hc := (hVd (τP+s)).comp s
        (hasDerivAt_const s τP |>.add (hasDerivAt_id s))
      simpa [yS, Function.comp_def] using hc
    have hyB := quadratic_riccati_mean_comparison_right_initial_le
      (A := L*q*(1-q)) (B := 1-2*q) (C := 1/L) (b := b) hb
      hySc hYBc
      (fun z hz => hySd z) (fun z hz => hYBd z)
      (fun z hz => by
        simpa [yS, div_eq_mul_inv, mul_comm] using hBbound (τP+z))
      (fun z hz => by
        simpa [div_eq_mul_inv, mul_comm] using hYBd z)
      (by simpa [yS, YB, hBcontact] using hycontact)
    let FS : ℝ → ℝ := (F ∘ (fun s : ℝ => τP+s)) - (fun _ : ℝ => F τP)
    let GS : ℝ → ℝ := (scaledBernoulliLogLaplace L q 1 ∘ (fun s : ℝ => τB+s)) -
      (fun _ : ℝ => scaledBernoulliLogLaplace L q 1 τB)
    have hFSc : Continuous FS := (hFcont.comp (continuous_const.add continuous_id)).sub continuous_const
    have hGSc : Continuous GS :=
      (scaledBernoulliLogLaplace_continuous one_ne_zero hq hq1).comp
        (continuous_const.add continuous_id) |>.sub continuous_const
    have hFSd : ∀ s ∈ Ioo 0 b, HasDerivAt FS (yS s) s := by
      intro s hs
      have hc := (hFd (τP+s)).comp s
        (hasDerivAt_const s τP |>.add (hasDerivAt_id s))
      change HasDerivAt FS (y (τP+s)) s
      simpa [FS, Function.comp_def] using (hc.sub (hasDerivAt_const s (F τP)))
    have hGSd : ∀ s ∈ Ioo 0 b, HasDerivAt GS (YB s) s := by
      intro s hs
      have hc := (scaledBernoulliLogLaplace_hasDerivAt
        (M := L) (p := q) (a := (1:ℝ)) one_ne_zero hq hq1 (τB+s)).comp s
        (hasDerivAt_const s τB |>.add (hasDerivAt_id s))
      change HasDerivAt GS (scaledBernoulliMean L q 1 (τB+s)) s
      simpa [GS, Function.comp_def] using (hc.sub (hasDerivAt_const s
        (scaledBernoulliLogLaplace L q 1 τB)))
    have hzero : FS 0 ≤ GS 0 := by simp [FS, GS]
    have hlog := log_laplace_le_right_initial_le (b := b) hb hFSc hGSc
      hFSd hGSd (fun z hz => by exact hyB z hz) hzero
    simpa [FS, GS] using hlog z hz
  intro s hs
  have houter' := houter s hs s ⟨hs, le_rfl⟩
  linarith


theorem stitched_right_loglaplace_bound
    {F y V : ℝ → ℝ} {M p a L q τP τB yR : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hL : 0 < L) (hq : 0 < q) (hq1 : q < 1)
    (hp : 0 < p) (hp1 : p < 1)
    (hFcont : Continuous F) (hycont : Continuous y)
    (hVd : ∀ t : ℝ, HasDerivAt y (V t) t)
    (hFd : ∀ t : ℝ, HasDerivAt F (y t) t)
    (hF0 : F 0 = 0) (hy0 : y 0 = 0)
    (hFglobal : ∀ t : ℝ, F t ≤ scaledBernoulliLogLaplace M p a t)
    (hPbound : ∀ t : ℝ,
      V t ≤ M*p*(1-p) + a*(1-2*p)*y t - a^2/M*(y t)^2)
    (hBbound : ∀ t : ℝ,
      V t ≤ L*q*(1-q) + (1-2*q)*y t - (y t)^2/L)
    (hτP : 0 ≤ τP) (hτB : 0 ≤ τB)
    (hPcontact : scaledBernoulliMean M p a τP = yR)
    (hBcontact : scaledBernoulliMean L q 1 τB = yR) :
    ∀ s : ℝ, 0 ≤ s →
      F (τP+s) ≤ scaledBernoulliLogLaplace M p a τP +
        (scaledBernoulliLogLaplace L q 1 (τB+s) -
          scaledBernoulliLogLaplace L q 1 τB) := by
  let YP : ℝ → ℝ := scaledBernoulliMean M p a
  have hYPc : Continuous YP := scaledBernoulliMean_continuous
    (ne_of_gt hM) (ne_of_gt ha) hp hp1
  have hYPd : ∀ t ∈ Ioo 0 τP, HasDerivAt YP
      (M*p*(1-p) + a*(1-2*p)*YP t - a^2/M*(YP t)^2) t := by
    intro t ht
    exact scaledBernoulliMean_hasDerivAt (ne_of_gt hM) (ne_of_gt ha) hp hp1 t
  have hyP := quadratic_riccati_mean_comparison (a := 0) (b := τP)
    (le_rfl) hτP hycont hYPc
    (fun t ht => hVd t) hYPd (fun t ht => hPbound t)
    (fun t ht => rfl) (by simpa [YP] using hy0)
  have hycontact : y τP ≤ yR := by
    have h := hyP.2 τP ⟨hτP, le_rfl⟩
    simpa [YP, hPcontact] using h
  have houter : ∀ b : ℝ, 0 ≤ b → ∀ z ∈ Icc 0 b,
      F (τP+z) - F τP ≤
        scaledBernoulliLogLaplace L q 1 (τB+z) -
          scaledBernoulliLogLaplace L q 1 τB := by
    intro b hb z hz
    let YB : ℝ → ℝ := (scaledBernoulliMean L q 1) ∘ (fun s : ℝ => τB+s)
    have hbaseB : Continuous (scaledBernoulliMean L q 1) :=
      scaledBernoulliMean_continuous (ne_of_gt hL) one_ne_zero hq hq1
    have hYBc : Continuous YB := by
      exact hbaseB.comp (continuous_const.add continuous_id)
    have hYBd : ∀ s : ℝ, HasDerivAt YB
        (L*q*(1-q) + (1-2*q)*YB s - (YB s)^2/L) s := by
      intro s
      have hh := scaledBernoulliMean_hasDerivAt (M := L) (p := q) (a := (1:ℝ))
        (ne_of_gt hL) one_ne_zero hq hq1 (τB+s)
      have hc := hh.comp s (hasDerivAt_const s τB |>.add (hasDerivAt_id s))
      simpa [YB, Function.comp_def, div_eq_mul_inv, mul_comm] using hc
    let yS : ℝ → ℝ := y ∘ (fun s : ℝ => τP+s)
    have hySc : Continuous yS := hycont.comp (continuous_const.add continuous_id)
    have hySd : ∀ s : ℝ, HasDerivAt yS (V (τP+s)) s := by
      intro s
      have hc := (hVd (τP+s)).comp s
        (hasDerivAt_const s τP |>.add (hasDerivAt_id s))
      simpa [yS, Function.comp_def] using hc
    have hyB := quadratic_riccati_mean_comparison_right_initial_le
      (A := L*q*(1-q)) (B := 1-2*q) (C := 1/L) (b := b) hb
      hySc hYBc
      (fun z hz => hySd z) (fun z hz => hYBd z)
      (fun z hz => by
        simpa [yS, div_eq_mul_inv, mul_comm] using hBbound (τP+z))
      (fun z hz => by
        simpa [div_eq_mul_inv, mul_comm] using hYBd z)
      (by simpa [yS, YB, hBcontact] using hycontact)
    let FS : ℝ → ℝ := (F ∘ (fun s : ℝ => τP+s)) - (fun _ : ℝ => F τP)
    let GS : ℝ → ℝ := (scaledBernoulliLogLaplace L q 1 ∘ (fun s : ℝ => τB+s)) -
      (fun _ : ℝ => scaledBernoulliLogLaplace L q 1 τB)
    have hFSc : Continuous FS := (hFcont.comp (continuous_const.add continuous_id)).sub continuous_const
    have hGSc : Continuous GS :=
      (scaledBernoulliLogLaplace_continuous one_ne_zero hq hq1).comp
        (continuous_const.add continuous_id) |>.sub continuous_const
    have hFSd : ∀ s ∈ Ioo 0 b, HasDerivAt FS (yS s) s := by
      intro s hs
      have hc := (hFd (τP+s)).comp s
        (hasDerivAt_const s τP |>.add (hasDerivAt_id s))
      change HasDerivAt FS (y (τP+s)) s
      simpa [FS, Function.comp_def] using (hc.sub (hasDerivAt_const s (F τP)))
    have hGSd : ∀ s ∈ Ioo 0 b, HasDerivAt GS (YB s) s := by
      intro s hs
      have hc := (scaledBernoulliLogLaplace_hasDerivAt
        (M := L) (p := q) (a := (1:ℝ)) one_ne_zero hq hq1 (τB+s)).comp s
        (hasDerivAt_const s τB |>.add (hasDerivAt_id s))
      change HasDerivAt GS (scaledBernoulliMean L q 1 (τB+s)) s
      simpa [GS, Function.comp_def] using (hc.sub (hasDerivAt_const s
        (scaledBernoulliLogLaplace L q 1 τB)))
    have hzero : FS 0 ≤ GS 0 := by simp [FS, GS]
    have hlog := log_laplace_le_right_initial_le (b := b) hb hFSc hGSc
      hFSd hGSd (fun z hz => by exact hyB z hz) hzero
    simpa [FS, GS] using hlog z hz
  intro s hs
  have hP0 : F τP ≤ scaledBernoulliLogLaplace M p a τP := hFglobal τP
  have houter' := houter s hs s ⟨hs, le_rfl⟩
  linarith

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

noncomputable def canonicalQuadraticRate (N k m u : ℝ) : ℝ :=
  envelopeM N m / envelopeScale N m ^ 2 *
    bernoulliKL (k/N)
      ((k/N) + envelopeScale N m * (u - m*k/N) / envelopeM N m)

noncomputable def canonicalBinomialRate (m p u : ℝ) : ℝ :=
  m * bernoulliKL p (u/m)

noncomputable def canonicalQuadraticSlope (N k m u : ℝ) : ℝ :=
  bernoulliFenchelTilt (k/N)
      ((k/N) + envelopeScale N m * (u - m*k/N) / envelopeM N m) /
    envelopeScale N m

noncomputable def canonicalBinomialSlope (m p u : ℝ) : ℝ :=
  bernoulliFenchelTilt p (u/m)

lemma stitched_right_exponent_identity
    {M a m p μ rp v : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hm : 0 < m)
    (hp : 0 < p) (hp1 : p < 1)
    (hμ : μ = m*p)
    (hrp0 : 0 < rp) (hrpm : rp < m) (hrpv : rp < v) (hvm : v < m)
    (hθ0 : 0 < p + a*(rp-μ)/M)
    (hθ1 : p + a*(rp-μ)/M < 1) :
    let θ := p + a*(rp-μ)/M
    let τP := bernoulliFenchelTilt p θ / a
    let τB := bernoulliFenchelTilt p (rp/m)
    let τv := bernoulliFenchelTilt p (v/m)
    (τP+τv-τB)*(v-μ) -
        (scaledBernoulliLogLaplace M p a τP +
          (scaledBernoulliLogLaplace m p 1 τv -
            scaledBernoulliLogLaplace m p 1 τB)) =
      m * bernoulliKL p (v/m) + M/a^2 * bernoulliKL p θ -
        m * bernoulliKL p (rp/m) +
        (v-rp) *
          (bernoulliFenchelTilt p θ / a - bernoulliFenchelTilt p (rp/m)) := by
  dsimp
  have hv0 : 0 < v := lt_trans hrp0 hrpv
  have hxrp0 : 0 < rp/m := div_pos hrp0 hm
  have hxrp1 : rp/m < 1 := (div_lt_one hm).2 hrpm
  have hxv0 : 0 < v/m := div_pos hv0 hm
  have hxv1 : v/m < 1 := (div_lt_one hm).2 hvm
  have hxvroot : rp/m < v/m := by
    apply (div_lt_div_iff₀ hm hm).2
    exact mul_lt_mul_of_pos_right hrpv hm
  have hθ := scaledBernoulliLogLaplace_at_fenchel hM ha hp hp1 hθ0 hθ1
  have hθscale : M / a * ((p + a*(rp-μ)/M)-p) = rp-μ := by
    field_simp [ne_of_gt hM, ne_of_gt ha]
    ring
  have hBroot := scaledBernoulliLogLaplace_at_fenchel hm one_pos hp hp1 hxrp0 hxrp1
  have hBv := scaledBernoulliLogLaplace_at_fenchel hm one_pos hp hp1 hxv0 hxv1
  have hBroot' : scaledBernoulliLogLaplace m p 1
      (bernoulliFenchelTilt p (rp/m)) =
      bernoulliFenchelTilt p (rp/m) * (rp-μ) - m * bernoulliKL p (rp/m) := by
    calc
      _ = bernoulliFenchelTilt p (rp/m) * (m*(rp/m-p)) -
          m * bernoulliKL p (rp/m) := by simpa [div_eq_mul_inv] using hBroot
      _ = bernoulliFenchelTilt p (rp/m) * (rp-μ) -
          m * bernoulliKL p (rp/m) := by rw [hμ]; field_simp [ne_of_gt hm]
  have hBv' : scaledBernoulliLogLaplace m p 1
      (bernoulliFenchelTilt p (v/m)) =
      bernoulliFenchelTilt p (v/m) * (v-μ) - m * bernoulliKL p (v/m) := by
    calc
      _ = bernoulliFenchelTilt p (v/m) * (m*(v/m-p)) -
          m * bernoulliKL p (v/m) := by simpa [div_eq_mul_inv] using hBv
      _ = bernoulliFenchelTilt p (v/m) * (v-μ) -
          m * bernoulliKL p (v/m) := by rw [hμ]; field_simp [ne_of_gt hm]
  have hP' : scaledBernoulliLogLaplace M p a
      (bernoulliFenchelTilt p (p + a*(rp-μ)/M) / a) =
      bernoulliFenchelTilt p (p + a*(rp-μ)/M) / a * (rp-μ) -
        M/a^2 * bernoulliKL p (p + a*(rp-μ)/M) := by
    rw [hθ]
    rw [hθscale]
  rw [hP', hBv', hBroot']
  ring

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

noncomputable def canonicalPiecewiseRate (N k m v : ℝ) : ℝ :=
  piecewiseKLRate
    (fun u => envelopeM N m / envelopeScale N m ^ 2 *
      bernoulliKL (k/N) (k/N + envelopeScale N m * (u-m*k/N) / envelopeM N m))
    (fun u => m * bernoulliKL (k/N) (u/m))
    (fun u => bernoulliFenchelTilt (k/N)
      (k/N + envelopeScale N m * (u-m*k/N) / envelopeM N m) / envelopeScale N m)
    (fun u => bernoulliFenchelTilt (k/N) (u/m))
    (varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m))
    (varianceSwitchPlus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)) v

end
end ExactHoeffding


namespace ExactHoeffding
noncomputable section

noncomputable def scaledKLRate (M p a μ v : ℝ) : ℝ :=
  M / a^2 * bernoulliKL p (p+a*(v-μ)/M)
noncomputable def scaledKLSlope (M p a μ v : ℝ) : ℝ :=
  bernoulliFenchelTilt p (p+a*(v-μ)/M)/a
noncomputable def binomialKLRate (m p v : ℝ) : ℝ := m*bernoulliKL p (v/m)
noncomputable def binomialKLSlope (m p v : ℝ) : ℝ := bernoulliFenchelTilt p (v/m)
noncomputable def outerKLRate (M p a m μ c v : ℝ) : ℝ :=
  binomialKLRate m p v + scaledKLRate M p a μ c - binomialKLRate m p c +
    (v-c)*(scaledKLSlope M p a μ c - binomialKLSlope m p c)

lemma bernoulliFenchelTilt_mono {p x z : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1)
    (hz : 0 < z) (hz1 : z < 1) (hxz : x ≤ z) :
    bernoulliFenchelTilt p x ≤ bernoulliFenchelTilt p z := by
  rcases hxz.eq_or_lt with rfl | hlt
  · exact le_rfl
  · exact (bernoulliFenchelTilt_strictMono hp hp1 hx hx1 hz hz1 hlt).le

/-- A closed Fenchel certificate for a stitched right outer branch. -/
theorem stitched_right_fenchel_bound
    {F y V : ℝ → ℝ} {M p a m μ c v : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hm : 0 < m)
    (hp : 0 < p) (hp1 : p < 1) (hμ : μ = m*p)
    (hFc : Continuous F) (hyc : Continuous y)
    (hyd : ∀ t, HasDerivAt y (V t) t) (hFd : ∀ t, HasDerivAt F (y t) t)
    (hF0 : F 0 = 0) (hy0 : y 0 = 0)
    (hP : ∀ t, V t ≤ M*p*(1-p)+a*(1-2*p)*y t-a^2/M*(y t)^2)
    (hB : ∀ t, V t ≤ m*p*(1-p)+(1-2*p)*y t-(y t)^2/m)
    (hμc : μ < c) (hcm : c < m) (hcv : c ≤ v) (hvm : v < m)
    (hθ0 : 0 < p+a*(c-μ)/M) (hθ1 : p+a*(c-μ)/M < 1) :
    ∃ t : ℝ, 0 ≤ t ∧ outerKLRate M p a m μ c v ≤ t*(v-μ)-F t := by
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hc0 : 0 < c := hμ0.trans hμc
  have hv0 : 0 < v := hc0.trans_le hcv
  have hcx0 : 0 < c/m := div_pos hc0 hm
  have hcx1 : c/m < 1 := (div_lt_one hm).2 hcm
  have hvx0 : 0 < v/m := div_pos hv0 hm
  have hvx1 : v/m < 1 := (div_lt_one hm).2 hvm
  have hpc : p ≤ c/m := (le_div_iff₀ hm).2 (by rw [hμ] at hμc; nlinarith)
  have hθp : p ≤ p+a*(c-μ)/M := by
    have := div_pos (mul_pos ha (sub_pos.mpr hμc)) hM
    linarith
  let τP := bernoulliFenchelTilt p (p+a*(c-μ)/M)/a
  let τB := bernoulliFenchelTilt p (c/m)
  let τV := bernoulliFenchelTilt p (v/m)
  have htP : 0 ≤ τP := div_nonneg
    (canonical_fenchel_tilt_nonneg hp hp1 hθ0 hθ1 hθp) ha.le
  have htB : 0 ≤ τB := canonical_fenchel_tilt_nonneg hp hp1 hcx0 hcx1 hpc
  have hdiff : 0 ≤ τV-τB := by
    apply sub_nonneg.mpr
    apply bernoulliFenchelTilt_mono hp hp1 hcx0 hcx1 hvx0 hvx1
    exact div_le_div_of_nonneg_right hcv hm.le
  have hPcontact : scaledBernoulliMean M p a τP = c-μ := by
    dsimp [τP]
    rw [scaledBernoulliMean_at_fenchel hM ha hp hp1 hθ0 hθ1]
    field_simp [hM.ne', ha.ne']
    ring
  have hBcontact : scaledBernoulliMean m p 1 τB = c-μ := by
    have h := scaledBernoulliMean_at_fenchel hm one_pos hp hp1 hcx0 hcx1
    simp only [div_one] at h
    dsimp [τB]
    rw [h, hμ]
    field_simp [hm.ne']
  have hglobal := variance_bound_implies_scaled_bernoulli_laplace
    hM.ne' ha.ne' hp hp1 hyd hFd hP hy0 hF0
  have hbridge := stitched_right_loglaplace_bound hM ha hm hp hp1 hp hp1
    hFc hyc hyd hFd hF0 hy0 hglobal hP hB htP htB hPcontact hBcontact
    (τV-τB) hdiff
  have hid : (τP+τV-τB)*(v-μ) -
      (scaledBernoulliLogLaplace M p a τP +
        (scaledBernoulliLogLaplace m p 1 τV - scaledBernoulliLogLaplace m p 1 τB)) =
      outerKLRate M p a m μ c v := by
    by_cases hEq : c = v
    · subst v
      have hPval := scaledBernoulliLogLaplace_at_fenchel hM ha hp hp1 hθ0 hθ1
      have hscale : M/a*(p+a*(c-μ)/M-p) = c-μ := by
        field_simp [hM.ne', ha.ne']; ring
      rw [hscale] at hPval
      dsimp [τP,τV,τB,outerKLRate,scaledKLRate,scaledKLSlope,binomialKLRate,
        binomialKLSlope]
      rw [hPval]
      ring
    · have hlt : c < v := lt_of_le_of_ne hcv hEq
      simpa [τP,τV,τB,outerKLRate,scaledKLRate,scaledKLSlope,binomialKLRate,
        binomialKLSlope] using
        stitched_right_exponent_identity hM ha hm hp hp1 hμ hc0 hcm hlt hvm hθ0 hθ1
  refine ⟨τP+τV-τB, by linarith, ?_⟩
  have htarg : τP+(τV-τB) = τP+τV-τB := by ring
  have hbarg : τB+(τV-τB) = τV := by ring
  rw [htarg,hbarg] at hbridge
  linarith [hid]


theorem stitched_right_fenchel_strict
    {F y V : ℝ → ℝ} {M p a m μ c v : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hm : 0 < m)
    (hp : 0 < p) (hp1 : p < 1) (hμ : μ = m*p)
    (hFc : Continuous F) (hyc : Continuous y)
    (hyd : ∀ t, HasDerivAt y (V t) t) (hFd : ∀ t, HasDerivAt F (y t) t)
    (hF0 : F 0 = 0) (hy0 : y 0 = 0)
    (hP : ∀ t, V t ≤ M*p*(1-p)+a*(1-2*p)*y t-a^2/M*(y t)^2)
    (hB : ∀ t, V t ≤ m*p*(1-p)+(1-2*p)*y t-(y t)^2/m)
    (hFstrict : ∀ t, t ≠ 0 → F t < scaledBernoulliLogLaplace M p a t)
    (hμc : μ < c) (hcm : c < m) (hcv : c ≤ v) (hvm : v < m)
    (hθ0 : 0 < p+a*(c-μ)/M) (hθ1 : p+a*(c-μ)/M < 1) :
    ∃ t : ℝ, 0 ≤ t ∧ outerKLRate M p a m μ c v < t*(v-μ)-F t := by
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hc0 : 0 < c := hμ0.trans hμc
  have hv0 : 0 < v := hc0.trans_le hcv
  have hcx0 : 0 < c/m := div_pos hc0 hm
  have hcx1 : c/m < 1 := (div_lt_one hm).2 hcm
  have hvx0 : 0 < v/m := div_pos hv0 hm
  have hvx1 : v/m < 1 := (div_lt_one hm).2 hvm
  have hpc : p ≤ c/m := (le_div_iff₀ hm).2 (by rw [hμ] at hμc; nlinarith)
  have hθp : p ≤ p+a*(c-μ)/M := by
    have := div_pos (mul_pos ha (sub_pos.mpr hμc)) hM
    linarith
  let τP := bernoulliFenchelTilt p (p+a*(c-μ)/M)/a
  let τB := bernoulliFenchelTilt p (c/m)
  let τV := bernoulliFenchelTilt p (v/m)
  have htP : 0 ≤ τP := div_nonneg
    (canonical_fenchel_tilt_nonneg hp hp1 hθ0 hθ1 hθp) ha.le
  have htB : 0 ≤ τB := canonical_fenchel_tilt_nonneg hp hp1 hcx0 hcx1 hpc
  have hdiff : 0 ≤ τV-τB := by
    apply sub_nonneg.mpr
    apply bernoulliFenchelTilt_mono hp hp1 hcx0 hcx1 hvx0 hvx1
    exact div_le_div_of_nonneg_right hcv hm.le
  have hPcontact : scaledBernoulliMean M p a τP = c-μ := by
    dsimp [τP]
    rw [scaledBernoulliMean_at_fenchel hM ha hp hp1 hθ0 hθ1]
    field_simp [hM.ne', ha.ne']
    ring
  have hBcontact : scaledBernoulliMean m p 1 τB = c-μ := by
    have h := scaledBernoulliMean_at_fenchel hm one_pos hp hp1 hcx0 hcx1
    simp only [div_one] at h
    dsimp [τB]
    rw [h, hμ]
    field_simp [hm.ne']
  have hglobal := variance_bound_implies_scaled_bernoulli_laplace
    hM.ne' ha.ne' hp hp1 hyd hFd hP hy0 hF0
  have hbridge := stitched_right_loglaplace_increment hM ha hm hp hp1 hp hp1
    hFc hyc hyd hFd hF0 hy0 hglobal hP hB htP htB hPcontact hBcontact
    (τV-τB) hdiff
  have hid : (τP+τV-τB)*(v-μ) -
      (scaledBernoulliLogLaplace M p a τP +
        (scaledBernoulliLogLaplace m p 1 τV - scaledBernoulliLogLaplace m p 1 τB)) =
      outerKLRate M p a m μ c v := by
    by_cases hEq : c = v
    · subst v
      have hPval := scaledBernoulliLogLaplace_at_fenchel hM ha hp hp1 hθ0 hθ1
      have hscale : M/a*(p+a*(c-μ)/M-p) = c-μ := by
        field_simp [hM.ne', ha.ne']; ring
      rw [hscale] at hPval
      dsimp [τP,τV,τB,outerKLRate,scaledKLRate,scaledKLSlope,binomialKLRate,
        binomialKLSlope]
      rw [hPval]
      ring
    · have hlt : c < v := lt_of_le_of_ne hcv hEq
      simpa [τP,τV,τB,outerKLRate,scaledKLRate,scaledKLSlope,binomialKLRate,
        binomialKLSlope] using
        stitched_right_exponent_identity hM ha hm hp hp1 hμ hc0 hcm hlt hvm hθ0 hθ1
  refine ⟨τP+τV-τB, by linarith, ?_⟩
  have htarg : τP+(τV-τB) = τP+τV-τB := by ring
  have hbarg : τB+(τV-τB) = τV := by ring
  rw [htarg,hbarg] at hbridge
  have htPpos : 0 < τP := by
    apply div_pos _ ha
    have htilt := bernoulliFenchelTilt_strictMono hp hp1 hp hp1 hθ0 hθ1
      (by have := div_pos (mul_pos ha (sub_pos.mpr hμc)) hM; linarith)
    have hself : bernoulliFenchelTilt p p = 0 := by
      simp [bernoulliFenchelTilt,hp.ne',(sub_pos.mpr hp1).ne']
    simpa [hself] using htilt
  have hgap := hFstrict τP htPpos.ne'
  linarith [hid]


theorem stitched_right_fenchel_contact_gap
    {F y V : ℝ → ℝ} {M p a m μ c v : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hm : 0 < m)
    (hp : 0 < p) (hp1 : p < 1) (hμ : μ = m*p)
    (hFc : Continuous F) (hyc : Continuous y)
    (hyd : ∀ t, HasDerivAt y (V t) t) (hFd : ∀ t, HasDerivAt F (y t) t)
    (hF0 : F 0 = 0) (hy0 : y 0 = 0)
    (hP : ∀ t, V t ≤ M*p*(1-p)+a*(1-2*p)*y t-a^2/M*(y t)^2)
    (hB : ∀ t, V t ≤ m*p*(1-p)+(1-2*p)*y t-(y t)^2/m)
    (hFstrict : ∀ t, t ≠ 0 → F t < scaledBernoulliLogLaplace M p a t)
    (hμc : μ < c) (hcm : c < m) (hcv : c ≤ v) (hvm : v < m)
    (hθ0 : 0 < p+a*(c-μ)/M) (hθ1 : p+a*(c-μ)/M < 1) :
    ∃ t : ℝ, 0 ≤ t ∧ outerKLRate M p a m μ c v +
      (scaledBernoulliLogLaplace M p a
        (bernoulliFenchelTilt p (p+a*(c-μ)/M)/a)-
        F (bernoulliFenchelTilt p (p+a*(c-μ)/M)/a)) ≤ t*(v-μ)-F t := by
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hc0 : 0 < c := hμ0.trans hμc
  have hv0 : 0 < v := hc0.trans_le hcv
  have hcx0 : 0 < c/m := div_pos hc0 hm
  have hcx1 : c/m < 1 := (div_lt_one hm).2 hcm
  have hvx0 : 0 < v/m := div_pos hv0 hm
  have hvx1 : v/m < 1 := (div_lt_one hm).2 hvm
  have hpc : p ≤ c/m := (le_div_iff₀ hm).2 (by rw [hμ] at hμc; nlinarith)
  have hθp : p ≤ p+a*(c-μ)/M := by
    have := div_pos (mul_pos ha (sub_pos.mpr hμc)) hM
    linarith
  let τP := bernoulliFenchelTilt p (p+a*(c-μ)/M)/a
  let τB := bernoulliFenchelTilt p (c/m)
  let τV := bernoulliFenchelTilt p (v/m)
  have htP : 0 ≤ τP := div_nonneg
    (canonical_fenchel_tilt_nonneg hp hp1 hθ0 hθ1 hθp) ha.le
  have htB : 0 ≤ τB := canonical_fenchel_tilt_nonneg hp hp1 hcx0 hcx1 hpc
  have hdiff : 0 ≤ τV-τB := by
    apply sub_nonneg.mpr
    apply bernoulliFenchelTilt_mono hp hp1 hcx0 hcx1 hvx0 hvx1
    exact div_le_div_of_nonneg_right hcv hm.le
  have hPcontact : scaledBernoulliMean M p a τP = c-μ := by
    dsimp [τP]
    rw [scaledBernoulliMean_at_fenchel hM ha hp hp1 hθ0 hθ1]
    field_simp [hM.ne', ha.ne']
    ring
  have hBcontact : scaledBernoulliMean m p 1 τB = c-μ := by
    have h := scaledBernoulliMean_at_fenchel hm one_pos hp hp1 hcx0 hcx1
    simp only [div_one] at h
    dsimp [τB]
    rw [h, hμ]
    field_simp [hm.ne']
  have hglobal := variance_bound_implies_scaled_bernoulli_laplace
    hM.ne' ha.ne' hp hp1 hyd hFd hP hy0 hF0
  have hbridge := stitched_right_loglaplace_increment hM ha hm hp hp1 hp hp1
    hFc hyc hyd hFd hF0 hy0 hglobal hP hB htP htB hPcontact hBcontact
    (τV-τB) hdiff
  have hid : (τP+τV-τB)*(v-μ) -
      (scaledBernoulliLogLaplace M p a τP +
        (scaledBernoulliLogLaplace m p 1 τV - scaledBernoulliLogLaplace m p 1 τB)) =
      outerKLRate M p a m μ c v := by
    by_cases hEq : c = v
    · subst v
      have hPval := scaledBernoulliLogLaplace_at_fenchel hM ha hp hp1 hθ0 hθ1
      have hscale : M/a*(p+a*(c-μ)/M-p) = c-μ := by
        field_simp [hM.ne', ha.ne']; ring
      rw [hscale] at hPval
      dsimp [τP,τV,τB,outerKLRate,scaledKLRate,scaledKLSlope,binomialKLRate,
        binomialKLSlope]
      rw [hPval]
      ring
    · have hlt : c < v := lt_of_le_of_ne hcv hEq
      simpa [τP,τV,τB,outerKLRate,scaledKLRate,scaledKLSlope,binomialKLRate,
        binomialKLSlope] using
        stitched_right_exponent_identity hM ha hm hp hp1 hμ hc0 hcm hlt hvm hθ0 hθ1
  refine ⟨τP+τV-τB, by linarith, ?_⟩
  have htarg : τP+(τV-τB) = τP+τV-τB := by ring
  have hbarg : τB+(τV-τB) = τV := by ring
  rw [htarg,hbarg] at hbridge
  change outerKLRate M p a m μ c v +
    (scaledBernoulliLogLaplace M p a τP - F τP) ≤ _
  linarith [hid]

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- Both Riccati subsolution inequalities for the actual hypergeometric law,
in the original population coordinates. -/
theorem hypergeom_kl_riccati_data (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    let p : ℝ := (k:ℝ)/(N:ℝ)
    let M := envelopeM (N:ℝ) (m:ℝ)
    let a := envelopeScale (N:ℝ) (m:ℝ)
    let μ : ℝ := (m:ℝ)*p
    let y : ℝ → ℝ := fun t => hypergeomTiltMean N k m t-μ
    (∀ t, hypergeomTiltVariance N k m t ≤
      M*p*(1-p)+a*(1-2*p)*y t-a^2/M*(y t)^2) ∧
    (∀ t, hypergeomTiltVariance N k m t ≤
      (m:ℝ)*p*(1-p)+(1-2*p)*y t-(y t)^2/(m:ℝ)) := by
  let r := N-(k+m)
  have hsum : k+m+r = N := by dsimp [r]; omega
  have hreal : (k:ℝ)+(m:ℝ)+(r:ℝ) = (N:ℝ) := by exact_mod_cast hsum
  have hbar := (hypergeomTiltVariance_barrier_canonical k m r hm hmk
    (by dsimp [r]; omega) (by dsimp [r]; omega)).1
  have hbin := canonical_hypergeom_variance_le_binomial_envelope k m r hm hmk
    (by dsimp [r]; omega)
  rw [hsum] at hbar hbin
  dsimp only at hbar hbin ⊢
  rw [hreal] at hbar
  constructor
  · intro t
    convert hbar t using 1 <;> dsimp [varianceBarrier] <;> ring
  · intro t
    convert hbin t using 1 <;> field_simp <;> ring

lemma scaledKL_argument_mem_Ioo
    {N k m v : ℝ} (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N)
    (hhalf : 2*m < N) (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    0 < k/N + envelopeScale N m*(v-m*k/N)/envelopeM N m ∧
    k/N + envelopeScale N m*(v-m*k/N)/envelopeM N m < 1 := by
  have hN : 0 < N := by linarith
  have hM := envelopeM_positive N m hm hhalf
  have ha : 0 < envelopeScale N m := div_pos (by linarith) (by linarith)
  have hp : 0 < k/N := div_pos (by linarith) hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith)
  have ham := envelope_scaled_mark_lt_one hm hhalf
  have ham' : envelopeScale N m*m < envelopeM N m := by
    simpa using (div_lt_iff₀ hM).1 ham
  have h0 : 0 < k/N*(envelopeM N m-envelopeScale N m*m) := by positivity
  have h1 : 0 < (1-k/N)*(envelopeM N m-envelopeScale N m*m) := by positivity
  have hlow : 0 ≤ envelopeScale N m*v := mul_nonneg ha.le hv0
  have hhigh : 0 ≤ envelopeScale N m*(m-v) := mul_nonneg ha.le (sub_nonneg.mpr hvm)
  have hid : (k/N + envelopeScale N m*(v-m*k/N)/envelopeM N m)*envelopeM N m =
      (k/N)*(envelopeM N m-envelopeScale N m*m)+envelopeScale N m*v := by
    field_simp [hM.ne']
    ring
  have hid' : envelopeM N m -
      (k/N + envelopeScale N m*(v-m*k/N)/envelopeM N m)*envelopeM N m =
      (1-k/N)*(envelopeM N m-envelopeScale N m*m)+envelopeScale N m*(m-v) := by
    field_simp [hM.ne']
    ring
  constructor <;> nlinarith

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- Finite exponential Markov applied to a closed Fenchel certificate. -/
theorem hypergeom_upper_tail_of_fenchel (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (v R t : ℝ) (ht : 0 ≤ t)
    (hR : R ≤ t*(v-(m:ℝ)*(k:ℝ)/(N:ℝ))-hypergeomCenteredLogMGF N k m t) :
    (∑ i ∈ Finset.range (m+1), if v ≤ (i:ℝ) then hypergeomMass N k m i else 0) ≤
      Real.exp (-R) := by
  have hmark := finite_markov_exp_bound (Finset.range (m+1)) (hypergeomMass N k m)
    (fun i => (i:ℝ)-(k:ℝ)*(m:ℝ)/(N:ℝ)) (fun i => v ≤ (i:ℝ))
    (fun i hi => hypergeomMass_nonneg N k m i) t
    (v-(m:ℝ)*(k:ℝ)/(N:ℝ)) ht (fun i hi hev => by simpa [mul_comm] using sub_le_sub_right hev ((k:ℝ)*(m:ℝ)/(N:ℝ)))
  change _ ≤ Real.exp _ * centeredHypergeomMGF N k m t at hmark
  rw [centeredHypergeomMGF_eq_exp_log N k m hk hm t, ← Real.exp_add] at hmark
  exact hmark.trans (Real.exp_le_exp.mpr (by nlinarith [hR]))

/-- The full actual-law right outer-tail bound; all contact conditions follow
from the population domain and the supported cut point. -/
theorem hypergeom_upper_tail_outer_kl (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (c v : ℝ) (hμc : (m:ℝ)*(k:ℝ)/(N:ℝ) < c) (hcm : c < m)
    (hcv : c ≤ v) (hvm : v < m) :
    (∑ i ∈ Finset.range (m+1), if v ≤ (i:ℝ) then hypergeomMass N k m i else 0) ≤
      Real.exp (-outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m)
        m ((m:ℝ)*(k:ℝ)/N) c v) := by
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hp : 0 < (k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/(N:ℝ) < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hmu0 : (0:ℝ) < (m:ℝ)*(k:ℝ)/N := div_pos (mul_pos (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast (show 0 < k by omega))) hN
  have hc0 : 0 < c := hmu0.trans hμc
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hc0.le hcm.le
  have hdata := hypergeom_kl_riccati_data N k m hm hmk hk hhalf
  let μ : ℝ := (m:ℝ)*((k:ℝ)/(N:ℝ))
  have hμid : μ = (m:ℝ)*(k:ℝ)/(N:ℝ) := by dsimp [μ]; ring
  have hFc : Continuous (hypergeomCenteredLogMGF N k m) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t).continuousAt
  have hyc : Continuous (fun t => hypergeomTiltMean N k m t-μ) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).continuousAt).sub continuous_const
  have hFd : ∀ t, HasDerivAt (hypergeomCenteredLogMGF N k m)
      (hypergeomTiltMean N k m t-μ) t := by
    intro t
    rw [hμid]
    exact hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t
  obtain ⟨t,ht,hR⟩ := stitched_right_fenchel_bound
    (M := envelopeM N m) (p := (k:ℝ)/N) (a := envelopeScale N m)
    (m := (m:ℝ)) (μ := μ) (c := c) (v := v)
    (envelopeM_positive N m hmR hhR)
    (div_pos (by linarith : 0 < (N:ℝ)-2*(m:ℝ)) (by linarith : 0 < (N:ℝ)-2))
    (by positivity) hp hp1 rfl hFc hyc
    (fun t => (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).sub_const μ)
    hFd (hypergeomCenteredLogMGF_zero N k m (by omega) (by omega))
    (by rw [hypergeomTiltMean_zero N k m (by omega) (by omega),hμid]; ring)
    hdata.1 hdata.2 (by simpa [hμid] using hμc) hcm hcv hvm
    (by simpa [hμid] using hθ.1) (by simpa [hμid] using hθ.2)
  rw [hμid] at hR
  exact hypergeom_upper_tail_of_fenchel N k m (by omega) (by omega) v _ t ht hR

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The explicit right switching root in the full original parameter domain. -/
theorem hypergeom_upper_tail_piecewise_right (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ)
    (hv : varianceSwitchPlus ((m:ℝ)*k/N) (klSwitchC N m)
      (klSwitchH N k m) (klSwitchB N k m) ≤ v) (hvm : v < m) :
    (∑ i ∈ Finset.range (m+1), if v ≤ (i:ℝ) then hypergeomMass N k m i else 0) ≤
      Real.exp (-canonicalPiecewiseRate N k m v) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hr := kl_switching_points_full_domain (N:ℝ) k m hmR hmkR hkR hhR
  let c := varianceSwitchPlus ((m:ℝ)*k/N) (klSwitchC N m)
    (klSwitchH N k m) (klSwitchB N k m)
  have hbound := hypergeom_upper_tail_outer_kl N k m hm hmk hk hhalf c v
    hr.2.2.1 hr.2.2.2 hv hvm
  have hroot : varianceSwitchMinus ((m:ℝ)*k/N) (klSwitchC N m)
      (klSwitchH N k m) (klSwitchB N k m) ≤ c := by dsimp [c]; linarith [hr.2.1,hr.2.2.1]
  have hid : canonicalPiecewiseRate N k m v =
      outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m)
        m ((m:ℝ)*k/N) c v := by
    rcases hv.eq_or_lt with heq | hlt
    · rw [← heq]
      dsimp [canonicalPiecewiseRate,c]
      rw [piecewiseKLRate_right_contact hroot]
      simp [outerKLRate,scaledKLRate,scaledKLSlope,binomialKLRate,binomialKLSlope,c]
    · unfold canonicalPiecewiseRate
      rw [piecewiseKLRate_eq_right hlt hroot]
      rfl
  rw [hid]
  exact hbound

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

lemma bernoulliKL_reflect (p x : ℝ) : bernoulliKL (1-p) (1-x) = bernoulliKL p x := by
  unfold bernoulliKL
  rw [show 1-(1-p) = p by ring, show 1-(1-x) = x by ring]
  ring

lemma bernoulliFenchelTilt_reflect {p x : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1) :
    bernoulliFenchelTilt (1-p) (1-x) = -bernoulliFenchelTilt p x := by
  unfold bernoulliFenchelTilt
  rw [show 1-(1-p) = p by ring, show 1-(1-x) = x by ring]
  have hid : (1-x)*p/((1-p)*x) = (x*(1-p)/(p*(1-x)))⁻¹ := by
    field_simp
  rw [hid,Real.log_inv]

lemma outerKLRate_reflect {M p a m μ c v : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hm : 0 < m)
    (hp : 0 < p) (hp1 : p < 1) (hc0 : 0 < c) (hcm : c < m)
    (hθ0 : 0 < p+a*(c-μ)/M) (hθ1 : p+a*(c-μ)/M < 1) :
    outerKLRate M (1-p) a m (m-μ) (m-c) (m-v) = outerKLRate M p a m μ c v := by
  have harg : 1-p+a*((m-c)-(m-μ))/M = 1-(p+a*(c-μ)/M) := by ring
  have hcarg : (m-c)/m = 1-c/m := by field_simp
  have hvarg : (m-v)/m = 1-v/m := by field_simp
  unfold outerKLRate scaledKLRate scaledKLSlope binomialKLRate binomialKLSlope
  rw [harg,hcarg,hvarg,bernoulliKL_reflect,bernoulliKL_reflect,bernoulliKL_reflect,
    bernoulliFenchelTilt_reflect hp hp1 hθ0 hθ1,
    bernoulliFenchelTilt_reflect hp hp1 (div_pos hc0 hm) ((div_lt_one hm).2 hcm)]
  ring

/-- The left outer Fenchel certificate follows by reflecting the mean and tilt
coordinates. -/
theorem stitched_left_fenchel_bound
    {F y V : ℝ → ℝ} {M p a m μ c v : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hm : 0 < m)
    (hp : 0 < p) (hp1 : p < 1) (hμ : μ = m*p)
    (hFc : Continuous F) (hyc : Continuous y)
    (hyd : ∀ t, HasDerivAt y (V t) t) (hFd : ∀ t, HasDerivAt F (y t) t)
    (hF0 : F 0 = 0) (hy0 : y 0 = 0)
    (hP : ∀ t, V t ≤ M*p*(1-p)+a*(1-2*p)*y t-a^2/M*(y t)^2)
    (hB : ∀ t, V t ≤ m*p*(1-p)+(1-2*p)*y t-(y t)^2/m)
    (hcμ : c < μ) (hc0 : 0 < c) (hvc : v ≤ c) (hv0 : 0 < v)
    (hθ0 : 0 < p+a*(c-μ)/M) (hθ1 : p+a*(c-μ)/M < 1) :
    ∃ t : ℝ, t ≤ 0 ∧ outerKLRate M p a m μ c v ≤ t*(v-μ)-F t := by
  let Fr : ℝ → ℝ := F ∘ Neg.neg
  let yr : ℝ → ℝ := -(y ∘ Neg.neg)
  let Vr : ℝ → ℝ := fun t => V (-t)
  have hFr : Continuous Fr := hFc.comp continuous_neg
  have hyr : Continuous yr := (hyc.comp continuous_neg).neg
  have hydr : ∀ t, HasDerivAt yr (Vr t) t := by
    intro t
    have h := ((hyd (-t)).comp t (hasDerivAt_neg t)).neg
    simpa [yr,Vr,Function.comp_def] using h
  have hFdr : ∀ t, HasDerivAt Fr (yr t) t := by
    intro t
    have h := (hFd (-t)).comp t (hasDerivAt_neg t)
    simpa [Fr,yr,Function.comp_def] using h
  have hPr : ∀ t, Vr t ≤ M*(1-p)*(1-(1-p))+a*(1-2*(1-p))*yr t-a^2/M*(yr t)^2 := by
    intro t
    convert hP (-t) using 1 <;> dsimp [Vr,yr] <;> ring
  have hBr : ∀ t, Vr t ≤ m*(1-p)*(1-(1-p))+(1-2*(1-p))*yr t-(yr t)^2/m := by
    intro t
    convert hB (-t) using 1 <;> dsimp [Vr,yr] <;> ring
  have harg : 1-p+a*((m-c)-(m-μ))/M = 1-(p+a*(c-μ)/M) := by ring
  have hθ0r : 0 < 1-p+a*((m-c)-(m-μ))/M := by rw [harg]; linarith
  have hθ1r : 1-p+a*((m-c)-(m-μ))/M < 1 := by rw [harg]; linarith
  obtain ⟨s,hs,hR⟩ := stitched_right_fenchel_bound hM ha hm
    (by linarith : 0 < 1-p) (by linarith : 1-p < 1)
    (by rw [hμ]; ring : m-μ = m*(1-p)) hFr hyr hydr hFdr
    (by simpa [Fr] using hF0) (by simp [yr,hy0]) hPr hBr
    (by linarith : m-μ < m-c) (by linarith : m-c < m)
    (by linarith : m-c ≤ m-v) (by linarith : m-v < m) hθ0r hθ1r
  have hcm : c < m := by rw [hμ] at hcμ; nlinarith
  rw [outerKLRate_reflect hM ha hm hp hp1 hc0 hcm hθ0 hθ1] at hR
  refine ⟨-s, by linarith, ?_⟩
  dsimp [Fr,Function.comp_def] at hR
  try simp only [neg_neg] at hR
  nlinarith [hR]

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

theorem hypergeom_lower_tail_of_fenchel (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (v R t : ℝ) (ht : t ≤ 0)
    (hR : R ≤ t*(v-(m:ℝ)*(k:ℝ)/(N:ℝ))-hypergeomCenteredLogMGF N k m t) :
    (∑ i ∈ Finset.range (m+1), if (i:ℝ) ≤ v then hypergeomMass N k m i else 0) ≤
      Real.exp (-R) := by
  have hmark := finite_markov_exp_bound (Finset.range (m+1)) (hypergeomMass N k m)
    (fun i => -((i:ℝ)-(k:ℝ)*(m:ℝ)/(N:ℝ))) (fun i => (i:ℝ) ≤ v)
    (fun i hi => hypergeomMass_nonneg N k m i) (-t)
    (-(v-(m:ℝ)*(k:ℝ)/(N:ℝ))) (by linarith)
    (fun i hi hev => by nlinarith [show (m:ℝ)*(k:ℝ)/(N:ℝ) = (k:ℝ)*(m:ℝ)/(N:ℝ) by ring])
  have hmgf : finiteMGF (Finset.range (m+1)) (hypergeomMass N k m)
      (fun i => -((i:ℝ)-(k:ℝ)*(m:ℝ)/(N:ℝ))) (-t) = centeredHypergeomMGF N k m t := by
    unfold finiteMGF centeredHypergeomMGF
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    ring
  rw [hmgf,centeredHypergeomMGF_eq_exp_log N k m hk hm t,← Real.exp_add] at hmark
  exact hmark.trans (Real.exp_le_exp.mpr (by nlinarith [hR]))

theorem hypergeom_lower_tail_outer_kl (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (c v : ℝ) (hcμ : c < (m:ℝ)*(k:ℝ)/(N:ℝ)) (hc0 : 0 < c)
    (hvc : v ≤ c) (hv0 : 0 < v) :
    (∑ i ∈ Finset.range (m+1), if (i:ℝ) ≤ v then hypergeomMass N k m i else 0) ≤
      Real.exp (-outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m)
        m ((m:ℝ)*(k:ℝ)/N) c v) := by
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hp : 0 < (k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/(N:ℝ) < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hcm : c < m := by
    have := mul_lt_mul_of_pos_left hp1 (by positivity : (0:ℝ)<m)
    rw [← mul_div_assoc] at this
    linarith
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hc0.le hcm.le
  have hdata := hypergeom_kl_riccati_data N k m hm hmk hk hhalf
  let μ : ℝ := (m:ℝ)*((k:ℝ)/(N:ℝ))
  have hμid : μ = (m:ℝ)*(k:ℝ)/(N:ℝ) := by dsimp [μ]; ring
  have hFc : Continuous (hypergeomCenteredLogMGF N k m) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t).continuousAt
  have hyc : Continuous (fun t => hypergeomTiltMean N k m t-μ) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).continuousAt).sub continuous_const
  have hFd : ∀ t, HasDerivAt (hypergeomCenteredLogMGF N k m)
      (hypergeomTiltMean N k m t-μ) t := by
    intro t
    rw [hμid]
    exact hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t
  obtain ⟨t,ht,hR⟩ := stitched_left_fenchel_bound
    (M := envelopeM N m) (p := (k:ℝ)/N) (a := envelopeScale N m)
    (m := (m:ℝ)) (μ := μ) (c := c) (v := v)
    (envelopeM_positive N m hmR hhR)
    (div_pos (by linarith : 0 < (N:ℝ)-2*(m:ℝ)) (by linarith : 0 < (N:ℝ)-2))
    (by positivity) hp hp1 rfl hFc hyc
    (fun t => (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).sub_const μ)
    hFd (hypergeomCenteredLogMGF_zero N k m (by omega) (by omega))
    (by rw [hypergeomTiltMean_zero N k m (by omega) (by omega),hμid]; ring)
    hdata.1 hdata.2 (by simpa [hμid] using hcμ) hc0 hvc hv0
    (by simpa [hμid] using hθ.1) (by simpa [hμid] using hθ.2)
  rw [hμid] at hR
  exact hypergeom_lower_tail_of_fenchel N k m (by omega) (by omega) v _ t ht hR

theorem hypergeom_lower_tail_piecewise_left (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ)
    (hv : v ≤ varianceSwitchMinus ((m:ℝ)*k/N) (klSwitchC N m)
      (klSwitchH N k m) (klSwitchB N k m)) (hv0 : 0 < v) :
    (∑ i ∈ Finset.range (m+1), if (i:ℝ) ≤ v then hypergeomMass N k m i else 0) ≤
      Real.exp (-canonicalPiecewiseRate N k m v) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hr := kl_switching_points_full_domain (N:ℝ) k m hmR hmkR hkR hhR
  let c := varianceSwitchMinus ((m:ℝ)*k/N) (klSwitchC N m)
    (klSwitchH N k m) (klSwitchB N k m)
  have hbound := hypergeom_lower_tail_outer_kl N k m hm hmk hk hhalf c v
    hr.2.1 hr.1 hv hv0
  have hroot : c ≤ varianceSwitchPlus ((m:ℝ)*k/N) (klSwitchC N m)
      (klSwitchH N k m) (klSwitchB N k m) := by dsimp [c]; linarith [hr.2.1,hr.2.2.1]
  have hid : canonicalPiecewiseRate N k m v =
      outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m)
        m ((m:ℝ)*k/N) c v := by
    rcases hv.eq_or_lt with heq | hlt
    · rw [heq]
      dsimp [canonicalPiecewiseRate,c]
      rw [piecewiseKLRate_left_contact hroot]
      simp [outerKLRate,scaledKLRate,scaledKLSlope,binomialKLRate,binomialKLSlope,c]
    · unfold canonicalPiecewiseRate
      rw [piecewiseKLRate_eq_left hlt]
      rfl
  rw [hid]
  exact hbound

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

theorem hypergeom_central_kl_fenchel (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    let μ : ℝ := (m:ℝ)*(k:ℝ)/N
    let θ := (k:ℝ)/N + envelopeScale N m*(v-μ)/envelopeM N m
    let t := bernoulliFenchelTilt ((k:ℝ)/N) θ / envelopeScale N m
    scaledKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) μ v ≤
      t*(v-μ)-hypergeomCenteredLogMGF N k m t := by
  dsimp only
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < (k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/(N:ℝ) < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hM := envelopeM_positive (N:ℝ) m hmR hhR
  have ha : 0 < envelopeScale N m := div_pos (by linarith) (by linarith)
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hv0 hvm
  have hval := scaledBernoulliLogLaplace_at_fenchel hM ha hp hp1 hθ.1 hθ.2
  have hscale : envelopeM N m/envelopeScale N m*
      ((k:ℝ)/N+envelopeScale N m*(v-(m:ℝ)*k/N)/envelopeM N m-(k:ℝ)/N) =
      v-(m:ℝ)*k/N := by field_simp [hM.ne',ha.ne']; ring
  rw [hscale] at hval
  have hglobal := (hypergeom_laplace_envelope N k m hm hmk hk hhalf).1
    (bernoulliFenchelTilt ((k:ℝ)/N)
      ((k:ℝ)/N+envelopeScale N m*(v-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m)
  dsimp [scaledKLRate]
  linarith [hval]

theorem hypergeom_upper_tail_piecewise_interior (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hμv : (m:ℝ)*(k:ℝ)/N ≤ v) (hvm : v < m) :
    (∑ i ∈ Finset.range (m+1), if v ≤ (i:ℝ) then hypergeomMass N k m i else 0) ≤
      Real.exp (-canonicalPiecewiseRate N k m v) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hr := kl_switching_points_full_domain (N:ℝ) k m hmR hmkR hkR hhR
  by_cases hv : varianceSwitchPlus ((m:ℝ)*k/N) (klSwitchC N m)
      (klSwitchH N k m) (klSwitchB N k m) ≤ v
  · exact hypergeom_upper_tail_piecewise_right N k m hm hmk hk hhalf v hv hvm
  have hv0 : 0 ≤ v := le_trans (by positivity) hμv
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hv0 hvm.le
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < (k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/(N:ℝ) < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have ha : 0 < envelopeScale N m := div_pos (by linarith) (by linarith)
  have hM := envelopeM_positive (N:ℝ) m hmR hhR
  let t := bernoulliFenchelTilt ((k:ℝ)/N)
    ((k:ℝ)/N+envelopeScale N m*(v-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m
  have ht : 0 ≤ t := by
    apply div_nonneg _ ha.le
    apply canonical_fenchel_tilt_nonneg hp hp1 hθ.1 hθ.2
    have : 0 ≤ envelopeScale N m*(v-(m:ℝ)*k/N)/envelopeM N m := by positivity
    linarith
  have hF := hypergeom_central_kl_fenchel N k m hm hmk hk hhalf v hv0 hvm.le
  have hbound := hypergeom_upper_tail_of_fenchel N k m (by omega) (by omega) v _ t ht hF
  have hid : canonicalPiecewiseRate N k m v =
      scaledKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) ((m:ℝ)*k/N) v := by
    unfold canonicalPiecewiseRate
    rw [piecewiseKLRate_eq_central (by linarith [hr.2.1]) (le_of_not_ge hv)]
    rfl
  rw [hid]
  exact hbound

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

theorem hypergeom_lower_tail_piecewise_interior (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hvμ : v ≤ (m:ℝ)*(k:ℝ)/N) (hv0 : 0 < v) :
    (∑ i ∈ Finset.range (m+1), if (i:ℝ) ≤ v then hypergeomMass N k m i else 0) ≤
      Real.exp (-canonicalPiecewiseRate N k m v) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hr := kl_switching_points_full_domain (N:ℝ) k m hmR hmkR hkR hhR
  by_cases hv : v ≤ varianceSwitchMinus ((m:ℝ)*k/N) (klSwitchC N m)
      (klSwitchH N k m) (klSwitchB N k m)
  · exact hypergeom_lower_tail_piecewise_left N k m hm hmk hk hhalf v hv hv0
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < (k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/(N:ℝ) < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hvm : v ≤ m := by
    have hmu := mul_lt_mul_of_pos_left hp1 (by positivity : (0:ℝ)<m)
    rw [← mul_div_assoc] at hmu
    nlinarith
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hv0.le hvm
  have ha : 0 < envelopeScale N m := div_pos (by linarith) (by linarith)
  have hM := envelopeM_positive (N:ℝ) m hmR hhR
  let θ := (k:ℝ)/N+envelopeScale N m*(v-(m:ℝ)*k/N)/envelopeM N m
  let t := bernoulliFenchelTilt ((k:ℝ)/N) θ / envelopeScale N m
  have ht : t ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ ha.le
    unfold bernoulliFenchelTilt
    apply Real.log_nonpos
    · exact (div_pos (mul_pos hθ.1 (by linarith)) (mul_pos hp (by linarith [hθ.2]))).le
    · apply (div_le_one (mul_pos hp (by dsimp [θ]; linarith [hθ.2]))).2
      have hθp : θ ≤ (k:ℝ)/N := by
        have : envelopeScale N m*(v-(m:ℝ)*k/N)/envelopeM N m ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hvμ)) hM.le
        dsimp [θ]
        linarith
      nlinarith
  have hF := hypergeom_central_kl_fenchel N k m hm hmk hk hhalf v hv0.le hvm
  have hbound := hypergeom_lower_tail_of_fenchel N k m (by omega) (by omega) v _ t ht hF
  have hid : canonicalPiecewiseRate N k m v =
      scaledKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) ((m:ℝ)*k/N) v := by
    unfold canonicalPiecewiseRate
    rw [piecewiseKLRate_eq_central (le_of_not_ge hv) (by linarith [hr.2.2.1])]
    rfl
  rw [hid]
  exact hbound

lemma bernoulliKL_continuous (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    Continuous (bernoulliKL p) := by
  have hid : bernoulliKL p = fun x =>
      x*Real.log x+(1-x)*Real.log (1-x)-x*Real.log p-(1-x)*Real.log (1-p) := by
    funext x
    unfold bernoulliKL
    by_cases hx : x = 0
    · subst x; simp [Real.log_inv]
    by_cases hx1 : 1-x = 0
    · have : x = 1 := by linarith
      subst x; simp [Real.log_inv]
    rw [Real.log_div hx hp.ne',Real.log_div hx1 (sub_pos.mpr hp1).ne']
    ring
  rw [hid]
  exact (((Real.continuous_mul_log.add
    (Real.continuous_mul_log.comp (continuous_const.sub continuous_id))).sub
    (continuous_id.mul continuous_const)).sub
    ((continuous_const.sub continuous_id).mul continuous_const))

lemma canonicalPiecewiseRate_continuous {N k m : ℝ} (hN : 0 < N)
    (hk : 0 < k) (hkN : k < N) (hroot :
      varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m) ≤
      varianceSwitchPlus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)) :
    Continuous (canonicalPiecewiseRate N k m) := by
  have hp := div_pos hk hN
  have hp1 := (div_lt_one hN).2 hkN
  let IP := fun u => envelopeM N m / envelopeScale N m ^ 2 *
    bernoulliKL (k/N) (k/N+envelopeScale N m*(u-m*k/N)/envelopeM N m)
  let IB := fun u => m*bernoulliKL (k/N) (u/m)
  let rm := varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
  let rp := varianceSwitchPlus (m*k/N) (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
  let sP := fun u => bernoulliFenchelTilt (k/N)
    (k/N+envelopeScale N m*(u-m*k/N)/envelopeM N m)/envelopeScale N m
  let sB := fun u => bernoulliFenchelTilt (k/N) (u/m)
  have hIP : Continuous IP := continuous_const.mul ((bernoulliKL_continuous _ hp hp1).comp
    (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).div_const _)))
  have hIB : Continuous IB := continuous_const.mul
    ((bernoulliKL_continuous _ hp hp1).comp (continuous_id.div_const _))
  let IL := fun u => IB u+IP rm-IB rm+(u-rm)*(sP rm-sB rm)
  let IR := fun u => IB u+IP rp-IB rp+(u-rp)*(sP rp-sB rp)
  have hIL : Continuous IL := (((hIB.add continuous_const).sub continuous_const).add
    ((continuous_id.sub continuous_const).mul continuous_const))
  have hIR : Continuous IR := (((hIB.add continuous_const).sub continuous_const).add
    ((continuous_id.sub continuous_const).mul continuous_const))
  have hinner : Continuous (fun u => if u ≤ rp then IP u else IR u) :=
    hIP.if_le hIR continuous_id continuous_const (by intro u hu; subst u; simp [IR])
  have hfull := hinner.if_le hIL continuous_const continuous_id (by
    intro u hu
    have hru : u = rm := hu.symm
    subst u
    simp [show rm ≤ rp from hroot,IL])
  convert hfull using 1
  funext u
  dsimp [canonicalPiecewiseRate,piecewiseKLRate]
  by_cases hu : u < rm
  · simp [hu,not_le.mpr hu,IL,IP,IB,rm,rp,sP,sB]
  · simp [hu,le_of_not_gt hu,IR,IP,IB,rm,rp,sP,sB]

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

lemma le_at_right_endpoint {g : ℝ → ℝ} {C a b : ℝ} (hg : Continuous g)
    (hab : a < b) (h : ∀ v, a ≤ v → v < b → C ≤ g v) : C ≤ g b := by
  have hlim := hg.continuousAt.tendsto.mono_left
    (show nhdsWithin b (Iio b) ≤ 𝓝 b from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds hab).filter_mono nhdsWithin_le_nhds] with v hv hva
  exact h v hva.le hv

lemma le_at_left_endpoint {g : ℝ → ℝ} {C a b : ℝ} (hg : Continuous g)
    (hab : a < b) (h : ∀ v, a < v → v ≤ b → C ≤ g v) : C ≤ g a := by
  have hlim := hg.continuousAt.tendsto.mono_left
    (show nhdsWithin a (Ioi a) ≤ 𝓝 a from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hab).filter_mono nhdsWithin_le_nhds] with v hv hvb
  exact h v hv hvb.le

/-- The closed piecewise KL upper tail, including the support maximum. -/
theorem hypergeom_upper_tail_piecewise_kl (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hμv : (m:ℝ)*(k:ℝ)/N ≤ v) (hvm : v ≤ m) :
    (∑ i ∈ Finset.range (m+1), if v ≤ (i:ℝ) then hypergeomMass N k m i else 0) ≤
      Real.exp (-canonicalPiecewiseRate N k m v) := by
  rcases hvm.eq_or_lt with heq | hlt
  · subst v
    have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
    have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
    have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
    have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
    have hr := kl_switching_points_full_domain (N:ℝ) k m hmR hmkR hkR hhR
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkN : (k:ℝ) < N := by exact_mod_cast (show k < N by omega)
    have hcont := (canonicalPiecewiseRate_continuous hN hk0 hkN
      (by linarith [hr.2.1,hr.2.2.1])).neg.rexp
    have hμm : (m:ℝ)*(k:ℝ)/N < m := by
      apply (div_lt_iff₀ hN).2
      exact mul_lt_mul_of_pos_left hkN (by linarith)
    apply le_at_right_endpoint hcont hμm
    intro z hμz hzm
    have hzbound := hypergeom_upper_tail_piecewise_interior N k m hm hmk hk hhalf z hμz hzm
    apply le_trans _ hzbound
    apply Finset.sum_le_sum
    intro i hi
    by_cases him : (m:ℝ) ≤ (i:ℝ)
    · rw [if_pos him,if_pos (by linarith : z ≤ (i:ℝ))]
    · rw [if_neg him]
      split_ifs
      · exact hypergeomMass_nonneg N k m i
      · exact le_rfl
  · exact hypergeom_upper_tail_piecewise_interior N k m hm hmk hk hhalf v hμv hlt

/-- The closed piecewise KL lower tail, including the support minimum. -/
theorem hypergeom_lower_tail_piecewise_kl (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hvμ : v ≤ (m:ℝ)*(k:ℝ)/N) (hv0 : 0 ≤ v) :
    (∑ i ∈ Finset.range (m+1), if (i:ℝ) ≤ v then hypergeomMass N k m i else 0) ≤
      Real.exp (-canonicalPiecewiseRate N k m v) := by
  rcases hv0.eq_or_lt with heq | hlt
  · rw [← heq]
    have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
    have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
    have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
    have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
    have hr := kl_switching_points_full_domain (N:ℝ) k m hmR hmkR hkR hhR
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkN : (k:ℝ) < N := by exact_mod_cast (show k < N by omega)
    have hcont := (canonicalPiecewiseRate_continuous hN hk0 hkN
      (by linarith [hr.2.1,hr.2.2.1])).neg.rexp
    have hμ0 : (0:ℝ) < (m:ℝ)*(k:ℝ)/N := div_pos (mul_pos (by linarith) hk0) hN
    apply le_at_left_endpoint hcont hμ0
    intro z hz0 hzμ
    have hzbound := hypergeom_lower_tail_piecewise_interior N k m hm hmk hk hhalf z hzμ hz0
    apply le_trans _ hzbound
    apply Finset.sum_le_sum
    intro i hi
    by_cases hi0 : (i:ℝ) ≤ 0
    · rw [if_pos hi0,if_pos (by linarith : (i:ℝ) ≤ z)]
    · rw [if_neg hi0]
      split_ifs
      · exact hypergeomMass_nonneg N k m i
      · exact le_rfl
  · exact hypergeom_lower_tail_piecewise_interior N k m hm hmk hk hhalf v hvμ hlt

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

lemma scaledBernoulliLogLaplace_reflect {M p a : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (t : ℝ) : scaledBernoulliLogLaplace M p a (-t) =
      scaledBernoulliLogLaplace M (1-p) a t := by
  have hden : scaledBernoulliDenom p a (-t) =
      Real.exp (-(a*t))*scaledBernoulliDenom (1-p) a t := by
    unfold scaledBernoulliDenom
    rw [show a * (-t) = -(a*t) by ring]
    have he : Real.exp (-(a*t))*Real.exp (a*t) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  have hpos : 0 < scaledBernoulliDenom (1-p) a t :=
    scaledBernoulliDenom_pos (by linarith) (by linarith) a t
  unfold scaledBernoulliLogLaplace
  rw [hden,Real.log_mul (Real.exp_pos _).ne' hpos.ne',Real.log_exp]
  ring

theorem stitched_left_fenchel_strict
    {F y V : ℝ → ℝ} {M p a m μ c v : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hm : 0 < m)
    (hp : 0 < p) (hp1 : p < 1) (hμ : μ = m*p)
    (hFc : Continuous F) (hyc : Continuous y)
    (hyd : ∀ t, HasDerivAt y (V t) t) (hFd : ∀ t, HasDerivAt F (y t) t)
    (hF0 : F 0 = 0) (hy0 : y 0 = 0)
    (hP : ∀ t, V t ≤ M*p*(1-p)+a*(1-2*p)*y t-a^2/M*(y t)^2)
    (hB : ∀ t, V t ≤ m*p*(1-p)+(1-2*p)*y t-(y t)^2/m)
    (hFstrict : ∀ t, t ≠ 0 → F t < scaledBernoulliLogLaplace M p a t)
    (hcμ : c < μ) (hc0 : 0 < c) (hvc : v ≤ c) (hv0 : 0 < v)
    (hθ0 : 0 < p+a*(c-μ)/M) (hθ1 : p+a*(c-μ)/M < 1) :
    ∃ t : ℝ, t ≤ 0 ∧ outerKLRate M p a m μ c v < t*(v-μ)-F t := by
  let Fr : ℝ → ℝ := F ∘ Neg.neg
  let yr : ℝ → ℝ := -(y ∘ Neg.neg)
  let Vr : ℝ → ℝ := fun t => V (-t)
  have hFr : Continuous Fr := hFc.comp continuous_neg
  have hyr : Continuous yr := (hyc.comp continuous_neg).neg
  have hydr : ∀ t, HasDerivAt yr (Vr t) t := by
    intro t
    have h := ((hyd (-t)).comp t (hasDerivAt_neg t)).neg
    simpa [yr,Vr,Function.comp_def] using h
  have hFdr : ∀ t, HasDerivAt Fr (yr t) t := by
    intro t
    have h := (hFd (-t)).comp t (hasDerivAt_neg t)
    simpa [Fr,yr,Function.comp_def] using h
  have hPr : ∀ t, Vr t ≤ M*(1-p)*(1-(1-p))+a*(1-2*(1-p))*yr t-a^2/M*(yr t)^2 := by
    intro t
    convert hP (-t) using 1 <;> dsimp [Vr,yr] <;> ring
  have hBr : ∀ t, Vr t ≤ m*(1-p)*(1-(1-p))+(1-2*(1-p))*yr t-(yr t)^2/m := by
    intro t
    convert hB (-t) using 1 <;> dsimp [Vr,yr] <;> ring
  have harg : 1-p+a*((m-c)-(m-μ))/M = 1-(p+a*(c-μ)/M) := by ring
  have hθ0r : 0 < 1-p+a*((m-c)-(m-μ))/M := by rw [harg]; linarith
  have hθ1r : 1-p+a*((m-c)-(m-μ))/M < 1 := by rw [harg]; linarith
  have hstrictr : ∀ t, t ≠ 0 → Fr t < scaledBernoulliLogLaplace M (1-p) a t := by
    intro t ht
    have h := hFstrict (-t) (neg_ne_zero.mpr ht)
    have href := scaledBernoulliLogLaplace_reflect (M := M) (a := a) hp hp1 t
    simpa [Fr, Function.comp_def] using h.trans_eq href
  obtain ⟨s,hs,hR⟩ := stitched_right_fenchel_strict hM ha hm
    (by linarith : 0 < 1-p) (by linarith : 1-p < 1)
    (by rw [hμ]; ring : m-μ = m*(1-p)) hFr hyr hydr hFdr
    (by simpa [Fr] using hF0) (by simp [yr,hy0]) hPr hBr hstrictr
    (by linarith : m-μ < m-c) (by linarith : m-c < m)
    (by linarith : m-c ≤ m-v) (by linarith : m-v < m) hθ0r hθ1r
  have hcm : c < m := by rw [hμ] at hcμ; nlinarith
  rw [outerKLRate_reflect hM ha hm hp hp1 hc0 hcm hθ0 hθ1] at hR
  refine ⟨-s, by linarith, ?_⟩
  dsimp [Fr,Function.comp_def] at hR
  try simp only [neg_neg] at hR
  nlinarith [hR]



theorem stitched_left_fenchel_contact_gap
    {F y V : ℝ → ℝ} {M p a m μ c v : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hm : 0 < m)
    (hp : 0 < p) (hp1 : p < 1) (hμ : μ = m*p)
    (hFc : Continuous F) (hyc : Continuous y)
    (hyd : ∀ t, HasDerivAt y (V t) t) (hFd : ∀ t, HasDerivAt F (y t) t)
    (hF0 : F 0 = 0) (hy0 : y 0 = 0)
    (hP : ∀ t, V t ≤ M*p*(1-p)+a*(1-2*p)*y t-a^2/M*(y t)^2)
    (hB : ∀ t, V t ≤ m*p*(1-p)+(1-2*p)*y t-(y t)^2/m)
    (hFstrict : ∀ t, t ≠ 0 → F t < scaledBernoulliLogLaplace M p a t)
    (hcμ : c < μ) (hc0 : 0 < c) (hvc : v ≤ c) (hv0 : 0 < v)
    (hθ0 : 0 < p+a*(c-μ)/M) (hθ1 : p+a*(c-μ)/M < 1) :
    ∃ t : ℝ, t ≤ 0 ∧ outerKLRate M p a m μ c v +
      (scaledBernoulliLogLaplace M p a
        (bernoulliFenchelTilt p (p+a*(c-μ)/M)/a)-
        F (bernoulliFenchelTilt p (p+a*(c-μ)/M)/a)) ≤ t*(v-μ)-F t := by
  let Fr : ℝ → ℝ := F ∘ Neg.neg
  let yr : ℝ → ℝ := -(y ∘ Neg.neg)
  let Vr : ℝ → ℝ := fun t => V (-t)
  have hFr : Continuous Fr := hFc.comp continuous_neg
  have hyr : Continuous yr := (hyc.comp continuous_neg).neg
  have hydr : ∀ t, HasDerivAt yr (Vr t) t := by
    intro t
    have h := ((hyd (-t)).comp t (hasDerivAt_neg t)).neg
    simpa [yr,Vr,Function.comp_def] using h
  have hFdr : ∀ t, HasDerivAt Fr (yr t) t := by
    intro t
    have h := (hFd (-t)).comp t (hasDerivAt_neg t)
    simpa [Fr,yr,Function.comp_def] using h
  have hPr : ∀ t, Vr t ≤ M*(1-p)*(1-(1-p))+a*(1-2*(1-p))*yr t-a^2/M*(yr t)^2 := by
    intro t
    convert hP (-t) using 1 <;> dsimp [Vr,yr] <;> ring
  have hBr : ∀ t, Vr t ≤ m*(1-p)*(1-(1-p))+(1-2*(1-p))*yr t-(yr t)^2/m := by
    intro t
    convert hB (-t) using 1 <;> dsimp [Vr,yr] <;> ring
  have harg : 1-p+a*((m-c)-(m-μ))/M = 1-(p+a*(c-μ)/M) := by ring
  have hθ0r : 0 < 1-p+a*((m-c)-(m-μ))/M := by rw [harg]; linarith
  have hθ1r : 1-p+a*((m-c)-(m-μ))/M < 1 := by rw [harg]; linarith
  have hstrictr : ∀ t, t ≠ 0 → Fr t < scaledBernoulliLogLaplace M (1-p) a t := by
    intro t ht
    have h := hFstrict (-t) (neg_ne_zero.mpr ht)
    have href := scaledBernoulliLogLaplace_reflect (M := M) (a := a) hp hp1 t
    simpa [Fr, Function.comp_def] using h.trans_eq href
  obtain ⟨s,hs,hR⟩ := stitched_right_fenchel_contact_gap hM ha hm
    (by linarith : 0 < 1-p) (by linarith : 1-p < 1)
    (by rw [hμ]; ring : m-μ = m*(1-p)) hFr hyr hydr hFdr
    (by simpa [Fr] using hF0) (by simp [yr,hy0]) hPr hBr hstrictr
    (by linarith : m-μ < m-c) (by linarith : m-c < m)
    (by linarith : m-c ≤ m-v) (by linarith : m-v < m) hθ0r hθ1r
  have hcm : c < m := by rw [hμ] at hcμ; nlinarith
  rw [outerKLRate_reflect hM ha hm hp hp1 hc0 hcm hθ0 hθ1] at hR
  have htref : bernoulliFenchelTilt (1-p) (1-p+a*((m-c)-(m-μ))/M)/a =
      -(bernoulliFenchelTilt p (p+a*(c-μ)/M)/a) := by
    rw [harg,bernoulliFenchelTilt_reflect hp hp1 hθ0 hθ1]
    ring
  rw [htref] at hR
  have hlogref := scaledBernoulliLogLaplace_reflect (M := M) (a := a) hp hp1
    (-(bernoulliFenchelTilt p (p+a*(c-μ)/M)/a))
  simp only [neg_neg] at hlogref
  rw [← hlogref] at hR
  refine ⟨-s, by linarith, ?_⟩
  dsimp [Fr,Function.comp_def] at hR
  try simp only [neg_neg] at hR
  nlinarith [hR]


end
end ExactHoeffding
