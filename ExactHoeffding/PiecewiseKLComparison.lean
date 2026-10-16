import ExactHoeffding.PiecewiseKLFull

open Set
open scoped Topology

namespace ExactHoeffding
noncomputable section

lemma bernoulliKL_entropy_identity (p x : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    bernoulliKL p x = x*Real.log x+(1-x)*Real.log (1-x)-
      x*Real.log p-(1-x)*Real.log (1-p) := by
  unfold bernoulliKL
  by_cases hx : x = 0
  · subst x; simp [Real.log_inv]
  by_cases hx1 : 1-x = 0
  · have : x = 1 := by linarith
    subst x; simp [Real.log_inv]
  rw [Real.log_div hx hp.ne',Real.log_div hx1 (sub_pos.mpr hp1).ne']
  ring

lemma bernoulliKL_hasDerivAt {p x : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (bernoulliKL p) (bernoulliFenchelTilt p x) x := by
  have hid : bernoulliKL p = fun z => z*Real.log z+(1-z)*Real.log (1-z)-
      z*Real.log p-(1-z)*Real.log (1-p) :=
    funext (fun z => bernoulliKL_entropy_identity p z hp hp1)
  rw [hid]
  have h := (((Real.hasDerivAt_mul_log hx.ne').add
      ((Real.hasDerivAt_mul_log (sub_pos.mpr hx1).ne').comp x
        ((hasDerivAt_const x 1).sub (hasDerivAt_id x)))).sub
      ((hasDerivAt_id x).mul_const (Real.log p))).sub
      (((hasDerivAt_const x 1).sub (hasDerivAt_id x)).mul_const (Real.log (1-p)))
  apply h.congr_deriv
  unfold bernoulliFenchelTilt
  rw [Real.log_div (mul_ne_zero hx.ne' (sub_pos.mpr hp1).ne')
      (mul_ne_zero hp.ne' (sub_pos.mpr hx1).ne'),
    Real.log_mul hx.ne' (sub_pos.mpr hp1).ne',
    Real.log_mul hp.ne' (sub_pos.mpr hx1).ne']
  ring

lemma bernoulliFenchelTilt_hasDerivAt {p x : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (bernoulliFenchelTilt p) (1/(x*(1-x))) x := by
  have hq : 1-p ≠ 0 := (sub_pos.mpr hp1).ne'
  have h1x : 1-x ≠ 0 := (sub_pos.mpr hx1).ne'
  have hnum := (hasDerivAt_id x).mul_const (1-p)
  have hden := (hasDerivAt_const x p).mul ((hasDerivAt_const x 1).sub (hasDerivAt_id x))
  have h := (hnum.div hden (mul_ne_zero hp.ne' h1x)).log
    (div_ne_zero (mul_ne_zero hx.ne' hq) (mul_ne_zero hp.ne' h1x))
  apply h.congr_deriv
  simp only [Pi.mul_apply, Pi.sub_apply, Pi.div_apply, id_eq]
  field_simp [hp.ne',hx.ne',hq,h1x]
  <;> ring

lemma scaledKLRate_hasDerivAt {M p a μ v : ℝ} (hM : 0 < M) (ha : 0 < a)
    (hp : 0 < p) (hp1 : p < 1)
    (hθ : p+a*(v-μ)/M ∈ Ioo 0 1) :
    HasDerivAt (scaledKLRate M p a μ) (scaledKLSlope M p a μ v) v := by
  have hd := (((hasDerivAt_id v).sub_const μ).const_mul a).div_const M |>.const_add p
  have h := ((bernoulliKL_hasDerivAt hp hp1 hθ.1 hθ.2).comp v hd).const_mul (M/a^2)
  apply h.congr_deriv
  unfold scaledKLSlope
  field_simp
  <;> ring

lemma scaledKLSlope_hasDerivAt {M p a μ v : ℝ} (hM : 0 < M) (ha : 0 < a)
    (hp : 0 < p) (hp1 : p < 1)
    (hθ : p+a*(v-μ)/M ∈ Ioo 0 1) :
    HasDerivAt (scaledKLSlope M p a μ)
      (1/(M*(p+a*(v-μ)/M)*(1-(p+a*(v-μ)/M)))) v := by
  have hd := (((hasDerivAt_id v).sub_const μ).const_mul a).div_const M |>.const_add p
  have h := ((bernoulliFenchelTilt_hasDerivAt hp hp1 hθ.1 hθ.2).comp v hd).div_const a
  apply h.congr_deriv
  field_simp
  <;> ring

lemma binomialKLRate_hasDerivAt {m p v : ℝ} (hm : 0 < m)
    (hp : 0 < p) (hp1 : p < 1) (hv : 0 < v) (hvm : v < m) :
    HasDerivAt (binomialKLRate m p) (binomialKLSlope m p v) v := by
  have h := ((bernoulliKL_hasDerivAt hp hp1 (div_pos hv hm)
    ((div_lt_one hm).2 hvm)).comp v ((hasDerivAt_id v).div_const m)).const_mul m
  apply h.congr_deriv
  unfold binomialKLSlope
  field_simp
  <;> ring

lemma binomialKLSlope_hasDerivAt {m p v : ℝ} (hm : 0 < m)
    (hp : 0 < p) (hp1 : p < 1) (hv : 0 < v) (hvm : v < m) :
    HasDerivAt (binomialKLSlope m p) (1/klBinomialEnvelope m v) v := by
  have h := ((bernoulliFenchelTilt_hasDerivAt hp hp1 (div_pos hv hm)
    ((div_lt_one hm).2 hvm)).comp v ((hasDerivAt_id v).div_const m))
  apply h.congr_deriv
  unfold klBinomialEnvelope
  field_simp
  <;> ring

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- A function with positive second derivative and zero value and slope at an
interior point is strictly positive away from that point, including endpoints. -/
lemma centered_positive_second_derivative
    {f s ds : ℝ → ℝ} {l μ r : ℝ} (hl : l < μ) (hr : μ < r)
    (hf : ∀ x ∈ Icc l r, HasDerivAt f (s x) x)
    (hs : ∀ x ∈ Icc l r, HasDerivAt s (ds x) x)
    (hds : ∀ x ∈ Ioo l r, 0 < ds x) (hf0 : f μ = 0) (hs0 : s μ = 0) :
    (∀ x ∈ Icc l r, x ≠ μ → 0 < f x) ∧ s l < 0 ∧ 0 < s r := by
  have hsc : ContinuousOn s (Icc l r) := fun x hx => (hs x hx).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Icc l r) := fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hsm : StrictMonoOn s (Icc l r) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc l r) hsc
      (fun x hx => (hs x (Ioo_subset_Icc_self (by simpa using hx))).hasDerivWithinAt)
      (fun x hx => hds x (by simpa using hx))
  have hμ : μ ∈ Icc l r := ⟨hl.le,hr.le⟩
  refine ⟨?_,?_,?_⟩
  · intro x hx hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hsub : Icc x μ ⊆ Icc l r := by intro z hz; constructor <;> linarith [hx.1,hr,hz.1,hz.2]
      have hanti : StrictAntiOn f (Icc x μ) :=
        strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc x μ) (hfc.mono hsub)
          (fun z hz => (hf z (hsub (Ioo_subset_Icc_self (by simpa using hz)))).hasDerivWithinAt)
          (by
            intro z hz
            have hz' : z ∈ Ioo x μ := by simpa using hz
            have := hsm (hsub (Ioo_subset_Icc_self hz')) hμ hz'.2
            simpa [hs0] using this)
      have := hanti ⟨le_rfl,hlt.le⟩ ⟨hlt.le,le_rfl⟩ hlt
      simpa [hf0] using this
    · have hsub : Icc μ x ⊆ Icc l r := by intro z hz; constructor <;> linarith [hl,hx.2,hz.1,hz.2]
      have hmono : StrictMonoOn f (Icc μ x) :=
        strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc μ x) (hfc.mono hsub)
          (fun z hz => (hf z (hsub (Ioo_subset_Icc_self (by simpa using hz)))).hasDerivWithinAt)
          (by
            intro z hz
            have hz' : z ∈ Ioo μ x := by simpa using hz
            have := hsm hμ (hsub (Ioo_subset_Icc_self hz')) hz'.1
            simpa [hs0] using this)
      have := hmono ⟨le_rfl,hgt.le⟩ ⟨hgt.le,le_rfl⟩ hgt
      simpa [hf0] using this
  · have := hsm ⟨le_rfl,(lt_trans hl hr).le⟩ hμ hl
    simpa [hs0] using this
  · have := hsm hμ ⟨(lt_trans hl hr).le,le_rfl⟩ hr
    simpa [hs0] using this

lemma scaledKL_denominator_identity (M p a μ v : ℝ) (hM : M ≠ 0) :
    M*(p+a*(v-μ)/M)*(1-(p+a*(v-μ)/M)) =
      M*p*(1-p)+a*(1-2*p)*(v-μ)-a^2/M*(v-μ)^2 := by
  field_simp [hM]
  <;> ring

lemma klQuadraticEnvelope_pos {N k m v : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hv0 : 0 ≤ v) (hvm : v ≤ m) : 0 < klQuadraticEnvelope N k m v := by
  have hM := envelopeM_positive N m hm hhalf
  have hθ := scaledKL_argument_mem_Ioo hm hmk hk hhalf hv0 hvm
  have hid := scaledKL_denominator_identity (envelopeM N m) (k/N)
    (envelopeScale N m) (m*k/N) v hM.ne'
  unfold klQuadraticEnvelope varianceBarrier
  have hid' : envelopeM N m * (1-(1-2*k/N)^2)/4 +
      envelopeScale N m*(1-2*k/N)*(v-m*k/N)-
      envelopeScale N m^2/envelopeM N m*(v-m*k/N)^2 =
      envelopeM N m*(k/N+envelopeScale N m*(v-m*k/N)/envelopeM N m)*
      (1-(k/N+envelopeScale N m*(v-m*k/N)/envelopeM N m)) := by
    rw [hid]; ring
  rw [hid']
  exact mul_pos (mul_pos hM hθ.1) (sub_pos.mpr hθ.2)

lemma scaledKLSlope_hasDerivAt_canonical {N k m v : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    HasDerivAt (scaledKLSlope (envelopeM N m) (k/N) (envelopeScale N m) (m*k/N))
      (1/klQuadraticEnvelope N k m v) v := by
  have hM := envelopeM_positive N m hm hhalf
  have hN : 0 < N := by linarith
  have ha : 0 < envelopeScale N m := div_pos (by linarith) (by linarith)
  have hp : 0 < k/N := div_pos (by linarith) hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith)
  have h := scaledKLSlope_hasDerivAt hM ha hp hp1
    (scaledKL_argument_mem_Ioo hm hmk hk hhalf hv0 hvm)
  convert h using 1
  rw [scaledKL_denominator_identity _ _ _ _ _ hM.ne']
  congr 1
  unfold klQuadraticEnvelope varianceBarrier
  ring

lemma klQuadraticEnvelope_lt_binomial_between {N k m v : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hl : varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m)
      (klSwitchB N k m) < v)
    (hr : v < varianceSwitchPlus (m*k/N) (klSwitchC N m) (klSwitchH N k m)
      (klSwitchB N k m)) : klQuadraticEnvelope N k m v < klBinomialEnvelope m v := by
  have hc := klSwitchC_pos N m hm hhalf
  have hb := klSwitchB_pos N k m hm hmk hk hhalf
  rw [← sub_neg, kl_variance_envelope_difference N k m v (by linarith),
    varianceEnvelopeDifference_factorization _ _ _ _ hc.ne'
      (varianceSwitchDiscriminant_pos hc hb).le]
  apply mul_neg_of_pos_of_neg
  · apply mul_pos hc
    dsimp [varianceSwitchMinus] at hl
    linarith
  · dsimp [varianceSwitchPlus] at hr
    linarith

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- On the entire canonical domain, the central scaled KL rate strictly
exceeds the binomial rate except at their common mean, with the required
outward slope signs at both explicit contacts. -/
theorem canonical_central_kl_strict_comparison {N k m : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    let μ := m*k/N
    let rm := varianceSwitchMinus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
    let rp := varianceSwitchPlus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
    let IP := scaledKLRate (envelopeM N m) (k/N) (envelopeScale N m) μ
    let sP := scaledKLSlope (envelopeM N m) (k/N) (envelopeScale N m) μ
    (∀ v ∈ Icc rm rp, v ≠ μ → binomialKLRate m (k/N) v < IP v) ∧
      sP rm - binomialKLSlope m (k/N) rm < 0 ∧
      0 < sP rp - binomialKLSlope m (k/N) rp := by
  dsimp only
  let μ := m*k/N
  let rm := varianceSwitchMinus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
  let rp := varianceSwitchPlus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
  let IP := scaledKLRate (envelopeM N m) (k/N) (envelopeScale N m) μ
  let sP := scaledKLSlope (envelopeM N m) (k/N) (envelopeScale N m) μ
  let f := fun v => IP v-binomialKLRate m (k/N) v
  let s := fun v => sP v-binomialKLSlope m (k/N) v
  have hroots := kl_switching_points_full_domain N k m hm hmk hk hhalf
  change 0 < rm ∧ rm < μ ∧ μ < rp ∧ rp < m at hroots
  have hN : 0 < N := by linarith
  have hm0 : 0 < m := by linarith
  have hM := envelopeM_positive N m hm hhalf
  have ha : 0 < envelopeScale N m := div_pos (by linarith) (by linarith)
  have hp : 0 < k/N := div_pos (by linarith) hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith)
  have hv (v : ℝ) (hv : v ∈ Icc rm rp) : 0 < v ∧ v < m := by
    constructor <;> linarith [hv.1,hv.2,hroots.1,hroots.2.2.2]
  have hfd : ∀ v ∈ Icc rm rp, HasDerivAt f (s v) v := by
    intro v hv'
    have hv0 := hv v hv'
    exact (scaledKLRate_hasDerivAt hM ha hp hp1
      (scaledKL_argument_mem_Ioo hm hmk hk hhalf hv0.1.le hv0.2.le)).sub
      (binomialKLRate_hasDerivAt hm0 hp hp1 hv0.1 hv0.2)
  have hsd : ∀ v ∈ Icc rm rp, HasDerivAt s
      (1/klQuadraticEnvelope N k m v-1/klBinomialEnvelope m v) v := by
    intro v hv'
    have hv0 := hv v hv'
    exact (scaledKLSlope_hasDerivAt_canonical hm hmk hk hhalf hv0.1.le hv0.2.le).sub
      (binomialKLSlope_hasDerivAt hm0 hp hp1 hv0.1 hv0.2)
  have hds : ∀ v ∈ Ioo rm rp,
      0 < 1/klQuadraticEnvelope N k m v-1/klBinomialEnvelope m v := by
    intro v hv'
    apply sub_pos.mpr
    exact one_div_lt_one_div_of_lt
      (klQuadraticEnvelope_pos hm hmk hk hhalf (hv v (Ioo_subset_Icc_self hv')).1.le
        (hv v (Ioo_subset_Icc_self hv')).2.le)
      (klQuadraticEnvelope_lt_binomial_between hm hmk hk hhalf hv'.1 hv'.2)
  have hμm : μ/m = k/N := by dsimp [μ]; field_simp
  have hf0 : f μ = 0 := by
    dsimp [f,IP,scaledKLRate,binomialKLRate]
    rw [hμm]
    simp [bernoulliKL, hp.ne', (sub_pos.mpr hp1).ne']
  have hs0 : s μ = 0 := by
    dsimp [s,sP,scaledKLSlope,binomialKLSlope]
    rw [hμm]
    simp [bernoulliFenchelTilt, hp.ne', (sub_pos.mpr hp1).ne']
  have h := centered_positive_second_derivative hroots.2.1 hroots.2.2.1 hfd hsd hds hf0 hs0
  refine ⟨?_,h.2⟩
  intro v hv' hvne
  have := h.1 v hv' hvne
  exact sub_pos.mp this

/-- The actual closed piecewise KL rate strictly improves the ordinary
binomial KL rate at every noncentral threshold, including support endpoints. -/
theorem canonicalPiecewiseRate_strict_improves_binomial {N k m : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv : v ≠ m*k/N) :
    m*bernoulliKL (k/N) (v/m) < canonicalPiecewiseRate N k m v := by
  have hr := kl_switching_points_full_domain N k m hm hmk hk hhalf
  have hc := canonical_central_kl_strict_comparison hm hmk hk hhalf
  unfold canonicalPiecewiseRate
  apply piecewiseKLRate_strict_improves hr.2.1 hr.2.2.1
    (fun z hz hlo hhi => hc.1 z ⟨hlo,hhi⟩ hz) hc.2.1.le hc.2.2.le v hv

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

lemma positive_from_contact_right {f s ds : ℝ → ℝ} {c r : ℝ} (hcr : c < r)
    (hfc : ContinuousOn f (Icc c r))
    (hfd : ∀ x ∈ Ioo c r, HasDerivAt f (s x) x)
    (hsd : ∀ x ∈ Ico c r, HasDerivAt s (ds x) x)
    (hds : ∀ x ∈ Ioo c r, 0 < ds x) (hf0 : f c = 0) (hs0 : s c = 0) :
    ∀ x ∈ Ioc c r, 0 < f x := by
  have hsc : ContinuousOn s (Ico c r) := fun x hx => (hsd x hx).continuousAt.continuousWithinAt
  have hsm : StrictMonoOn s (Ico c r) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ico c r) hsc
      (fun x hx => (hsd x (Ioo_subset_Ico_self (by simpa using hx))).hasDerivWithinAt)
      (fun x hx => hds x (by simpa using hx))
  have hfm : StrictMonoOn f (Icc c r) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc c r) hfc
      (fun x hx => (hfd x (by simpa using hx)).hasDerivWithinAt)
      (by
        intro x hx
        have hx' : x ∈ Ioo c r := by simpa using hx
        have := hsm ⟨le_rfl,hcr⟩ (Ioo_subset_Ico_self hx') hx'.1
        simpa [hs0] using this)
  intro x hx
  have := hfm ⟨le_rfl,hcr.le⟩ ⟨hx.1.le,hx.2⟩ hx.1
  simpa [hf0] using this

lemma positive_from_contact_left {f s ds : ℝ → ℝ} {l c : ℝ} (hlc : l < c)
    (hfc : ContinuousOn f (Icc l c))
    (hfd : ∀ x ∈ Ioo l c, HasDerivAt f (s x) x)
    (hsd : ∀ x ∈ Ioc l c, HasDerivAt s (ds x) x)
    (hds : ∀ x ∈ Ioo l c, 0 < ds x) (hf0 : f c = 0) (hs0 : s c = 0) :
    ∀ x ∈ Ico l c, 0 < f x := by
  have hsc : ContinuousOn s (Ioc l c) := fun x hx => (hsd x hx).continuousAt.continuousWithinAt
  have hsm : StrictMonoOn s (Ioc l c) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioc l c) hsc
      (fun x hx => (hsd x (Ioo_subset_Ioc_self (by simpa using hx))).hasDerivWithinAt)
      (fun x hx => hds x (by simpa using hx))
  have hfm : StrictAntiOn f (Icc l c) :=
    strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc l c) hfc
      (fun x hx => (hfd x (by simpa using hx)).hasDerivWithinAt)
      (by
        intro x hx
        have hx' : x ∈ Ioo l c := by simpa using hx
        have := hsm (Ioo_subset_Ioc_self hx') ⟨hlc,le_rfl⟩ hx'.2
        simpa [hs0] using this)
  intro x hx
  have := hfm ⟨hx.1,hx.2.le⟩ ⟨hlc.le,le_rfl⟩ hx.2
  simpa [hf0] using this

lemma outerKLRate_gap_hasDerivAt {M p a m μ c v : ℝ}
    (hM : 0 < M) (ha : 0 < a) (hm : 0 < m) (hp : 0 < p) (hp1 : p < 1)
    (hv : 0 < v) (hvm : v < m) (hθ : p+a*(v-μ)/M ∈ Ioo 0 1) :
    HasDerivAt (fun z => outerKLRate M p a m μ c z-scaledKLRate M p a μ z)
      (binomialKLSlope m p v-scaledKLSlope M p a μ v+
        (scaledKLSlope M p a μ c-binomialKLSlope m p c)) v := by
  have h := (((binomialKLRate_hasDerivAt hm hp hp1 hv hvm).add_const
    (scaledKLRate M p a μ c)).sub_const (binomialKLRate m p c)).add
    (((hasDerivAt_id v).sub_const c).mul_const
      (scaledKLSlope M p a μ c-binomialKLSlope m p c)) |>.sub
    (scaledKLRate_hasDerivAt hM ha hp hp1 hθ)
  apply h.congr_deriv
  ring

lemma outerKLRate_gap_continuous {M p a m μ c : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Continuous (fun z => outerKLRate M p a m μ c z-scaledKLRate M p a μ z) := by
  have hIP : Continuous (scaledKLRate M p a μ) :=
    continuous_const.mul ((bernoulliKL_continuous p hp hp1).comp
      (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).div_const M)))
  have hIB : Continuous (binomialKLRate m p) :=
    continuous_const.mul ((bernoulliKL_continuous p hp hp1).comp (continuous_id.div_const m))
  exact (((hIB.add continuous_const).sub continuous_const).add
    ((continuous_id.sub continuous_const).mul continuous_const)).sub hIP

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

lemma klQuadraticEnvelope_gt_binomial_outside {N k m v : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hout : v < varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m)
      (klSwitchB N k m) ∨ varianceSwitchPlus (m*k/N) (klSwitchC N m)
      (klSwitchH N k m) (klSwitchB N k m) < v) :
    klBinomialEnvelope m v < klQuadraticEnvelope N k m v := by
  have hi := kl_quadratic_envelope_le_binomial_iff N k m v hm hmk hk hhalf
  apply lt_of_not_ge
  intro hle
  rcases hi.mp hle with ⟨hl,hr⟩
  rcases hout with h | h <;> linarith

/-- On either exterior interval, the tangent-corrected binomial rate is
strictly greater than the scaled KL rate, also at the support endpoints. -/
theorem canonical_outer_kl_strict_comparison {N k m : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    let μ := m*k/N
    let rm := varianceSwitchMinus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
    let rp := varianceSwitchPlus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
    (∀ v ∈ Ico 0 rm, scaledKLRate (envelopeM N m) (k/N) (envelopeScale N m) μ v <
      outerKLRate (envelopeM N m) (k/N) (envelopeScale N m) m μ rm v) ∧
    (∀ v ∈ Ioc rp m, scaledKLRate (envelopeM N m) (k/N) (envelopeScale N m) μ v <
      outerKLRate (envelopeM N m) (k/N) (envelopeScale N m) m μ rp v) := by
  dsimp only
  let μ := m*k/N
  let rm := varianceSwitchMinus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
  let rp := varianceSwitchPlus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
  have hr := kl_switching_points_full_domain N k m hm hmk hk hhalf
  change 0 < rm ∧ rm < μ ∧ μ < rp ∧ rp < m at hr
  have hN : 0 < N := by linarith
  have hm0 : 0 < m := by linarith
  have hM := envelopeM_positive N m hm hhalf
  have ha : 0 < envelopeScale N m := div_pos (by linarith) (by linarith)
  have hp : 0 < k/N := div_pos (by linarith) hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith)
  have hd (v : ℝ) (hv : 0 < v) (hvm : v < m) (c : ℝ) :
      HasDerivAt (fun z => outerKLRate (envelopeM N m) (k/N) (envelopeScale N m) m μ c z-
        scaledKLRate (envelopeM N m) (k/N) (envelopeScale N m) μ z)
        (binomialKLSlope m (k/N) v-
          scaledKLSlope (envelopeM N m) (k/N) (envelopeScale N m) μ v+
          (scaledKLSlope (envelopeM N m) (k/N) (envelopeScale N m) μ c-
            binomialKLSlope m (k/N) c)) v :=
    outerKLRate_gap_hasDerivAt hM ha hm0 hp hp1 hv hvm
      (scaledKL_argument_mem_Ioo hm hmk hk hhalf hv.le hvm.le)
  have hsd (c v : ℝ) (hv : 0 < v) (hvm : v < m) :
      HasDerivAt (fun z => binomialKLSlope m (k/N) z-
        scaledKLSlope (envelopeM N m) (k/N) (envelopeScale N m) μ z+
        (scaledKLSlope (envelopeM N m) (k/N) (envelopeScale N m) μ c-
          binomialKLSlope m (k/N) c))
        (1/klBinomialEnvelope m v-1/klQuadraticEnvelope N k m v) v :=
    ((binomialKLSlope_hasDerivAt hm0 hp hp1 hv hvm).sub
      (scaledKLSlope_hasDerivAt_canonical hm hmk hk hhalf hv.le hvm.le)).add_const _
  have hpos (v : ℝ) (hv : 0 < v) (hvm : v < m)
      (hout : v < rm ∨ rp < v) :
      0 < 1/klBinomialEnvelope m v-1/klQuadraticEnvelope N k m v := by
    apply sub_pos.mpr
    apply one_div_lt_one_div_of_lt
    · unfold klBinomialEnvelope
      exact div_pos (mul_pos hv (sub_pos.mpr hvm)) hm0
    · exact klQuadraticEnvelope_gt_binomial_outside hm hmk hk hhalf hout
  constructor
  · have h := positive_from_contact_left hr.1
      (outerKLRate_gap_continuous (M := envelopeM N m) (a := envelopeScale N m)
        (m := m) (μ := μ) (c := rm) hp hp1).continuousOn
      (fun v hv => hd v hv.1 (by linarith [hv.2,hr.2.1,hr.2.2.1,hr.2.2.2]) rm)
      (fun v hv => hsd rm v hv.1 (by linarith [hv.2,hr.2.1,hr.2.2.1,hr.2.2.2]))
      (fun v hv => hpos v hv.1 (by linarith [hv.2,hr.2.1,hr.2.2.1,hr.2.2.2]) (Or.inl hv.2))
      (by simp [outerKLRate]) (by ring)
    intro v hv
    exact sub_pos.mp (h v hv)
  · have h := positive_from_contact_right hr.2.2.2
      (outerKLRate_gap_continuous (M := envelopeM N m) (a := envelopeScale N m)
        (m := m) (μ := μ) (c := rp) hp hp1).continuousOn
      (fun v hv => hd v (by linarith [hr.1,hr.2.1,hr.2.2.1,hv.1]) hv.2 rp)
      (fun v hv => hsd rp v (by linarith [hr.1,hr.2.1,hr.2.2.1,hv.1]) hv.2)
      (fun v hv => hpos v (by linarith [hr.1,hr.2.1,hr.2.2.1,hv.1]) hv.2 (Or.inr hv.1))
      (by simp [outerKLRate]) (by ring)
    intro v hv
    exact sub_pos.mp (h v hv)

/-- Exact quadratic-rate equality classification for the closed piecewise KL
rate.  The inequality is strict precisely outside the two switching roots. -/
theorem canonicalPiecewiseRate_quadratic_comparison {N k m v : ℝ}
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    let μ := m*k/N
    let rm := varianceSwitchMinus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
    let rp := varianceSwitchPlus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
    let IP := scaledKLRate (envelopeM N m) (k/N) (envelopeScale N m) μ v
    IP ≤ canonicalPiecewiseRate N k m v ∧
      (IP = canonicalPiecewiseRate N k m v ↔ rm ≤ v ∧ v ≤ rp) ∧
      (IP < canonicalPiecewiseRate N k m v ↔ v < rm ∨ rp < v) := by
  dsimp only
  let μ := m*k/N
  let rm := varianceSwitchMinus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
  let rp := varianceSwitchPlus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
  have hr := kl_switching_points_full_domain N k m hm hmk hk hhalf
  change 0 < rm ∧ rm < μ ∧ μ < rp ∧ rp < m at hr
  have ho := canonical_outer_kl_strict_comparison hm hmk hk hhalf
  have hroot : rm ≤ rp := by linarith [hr.2.1,hr.2.2.1]
  by_cases hl : v < rm
  · have hJ : canonicalPiecewiseRate N k m v =
        outerKLRate (envelopeM N m) (k/N) (envelopeScale N m) m μ rm v := by
      unfold canonicalPiecewiseRate
      rw [piecewiseKLRate_eq_left hl]
      rfl
    have hstrict := ho.1 v ⟨hv0,hl⟩
    rw [hJ]
    exact ⟨hstrict.le, iff_of_false (ne_of_lt hstrict) (by intro h; linarith [h.1]),
      iff_of_true hstrict (Or.inl hl)⟩
  · by_cases hh : v ≤ rp
    · have hJ : canonicalPiecewiseRate N k m v =
          scaledKLRate (envelopeM N m) (k/N) (envelopeScale N m) μ v := by
        unfold canonicalPiecewiseRate
        rw [piecewiseKLRate_eq_central (le_of_not_gt hl) hh]
        rfl
      rw [hJ]
      exact ⟨le_rfl, iff_of_true rfl ⟨le_of_not_gt hl,hh⟩,
        iff_of_false (lt_irrefl _) (by rintro (h | h) <;> linarith)⟩
    · have hJ : canonicalPiecewiseRate N k m v =
          outerKLRate (envelopeM N m) (k/N) (envelopeScale N m) m μ rp v := by
        unfold canonicalPiecewiseRate
        rw [piecewiseKLRate_eq_right (lt_of_not_ge hh) hroot]
        rfl
      have hstrict := ho.2 v ⟨lt_of_not_ge hh,hvm⟩
      rw [hJ]
      exact ⟨hstrict.le, iff_of_false (ne_of_lt hstrict) (by intro h; linarith [h.2]),
        iff_of_true hstrict (Or.inr (lt_of_not_ge hh))⟩

end
end ExactHoeffding
