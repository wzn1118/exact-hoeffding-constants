import ExactHoeffding.PiecewiseKLComparison
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set
open scoped Topology

namespace ExactHoeffding
noncomputable section

/-- KL rates obtained by sampling duality and the two complementations. -/
def fourBinomialKLRate2 (N k m v : ℝ) : ℝ :=
  k * bernoulliKL (m/N) (v/k)

def fourBinomialKLRate3 (N k m v : ℝ) : ℝ :=
  (N-m) * bernoulliKL (k/N) ((k-v)/(N-m))

def fourBinomialKLRate4 (N k m v : ℝ) : ℝ :=
  (N-k) * bernoulliKL (m/N) ((m-v)/(N-k))

def fourBinomialKLRate2Slope (N k m v : ℝ) : ℝ :=
  bernoulliFenchelTilt (m/N) (v/k)

def fourBinomialKLRate3Slope (N k m v : ℝ) : ℝ :=
  -bernoulliFenchelTilt (k/N) ((k-v)/(N-m))

def fourBinomialKLRate4Slope (N k m v : ℝ) : ℝ :=
  -bernoulliFenchelTilt (m/N) ((m-v)/(N-k))

def fourBinomialEnvelope1 (m v : ℝ) : ℝ := v*(m-v)/m

def fourBinomialEnvelope2 (k v : ℝ) : ℝ := v*(k-v)/k

def fourBinomialEnvelope3 (N k m v : ℝ) : ℝ :=
  (k-v)*(N-m-k+v)/(N-m)

def fourBinomialEnvelope4 (N k m v : ℝ) : ℝ :=
  (m-v)*(N-k-m+v)/(N-k)

lemma bernoulliKL_self {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    bernoulliKL p p = 0 := by
  unfold bernoulliKL
  rw [div_self hp.ne', div_self (sub_pos.mpr hp1).ne']
  simp

private lemma centered_strict_gap
    {m μ : ℝ} (hμ : 0 < μ) (hμm : μ < m)
    {f s ds : ℝ → ℝ}
    (hfcont : ContinuousOn f (Icc 0 m))
    (hfd : ∀ x ∈ Ioo 0 m, HasDerivAt f (s x) x)
    (hsd : ∀ x ∈ Ioo 0 m, HasDerivAt s (ds x) x)
    (hds : ∀ x ∈ Ioo 0 m, 0 < ds x)
    (hfμ : f μ = 0) (hsμ : s μ = 0) :
    ∀ v ∈ Icc 0 m, v ≠ μ → 0 < f v := by
  have hscont : ContinuousOn s (Ioo 0 m) := fun x hx =>
    (hsd x hx).continuousAt.continuousWithinAt
  have hsmono : StrictMonoOn s (Ioo 0 m) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo 0 m) hscont
      (fun x hx => (hsd x (by simpa using hx)).hasDerivWithinAt)
      (fun x hx => hds x (by simpa using hx))
  have hleft : StrictAntiOn f (Icc 0 μ) :=
    strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc 0 μ)
      (hfcont.mono (by
        intro x hx
        exact ⟨hx.1, hx.2.trans hμm.le⟩))
      (fun x hx => (hfd x (by
        have hx' : x ∈ Ioo 0 μ := by simpa using hx
        exact ⟨hx'.1, hx'.2.trans hμm⟩)).hasDerivWithinAt)
      (by
        intro x hx
        have hx' : x ∈ Ioo 0 μ := by simpa using hx
        have hx0 : x ∈ Ioo 0 m := ⟨hx'.1, hx'.2.trans hμm⟩
        have hμ' : μ ∈ Ioo 0 m := ⟨hμ, hμm⟩
        have hlt := hsmono hx0 hμ' hx'.2
        simpa [hsμ] using hlt)
  have hright : StrictMonoOn f (Icc μ m) :=
    strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc μ m)
      (hfcont.mono (by
        intro x hx
        exact ⟨hμ.le.trans hx.1, hx.2⟩))
      (fun x hx => (hfd x (by
        have hx' : x ∈ Ioo μ m := by simpa using hx
        exact ⟨hμ.trans hx'.1, hx'.2⟩)).hasDerivWithinAt)
      (by
        intro x hx
        have hx' : x ∈ Ioo μ m := by simpa using hx
        have hx0 : x ∈ Ioo 0 m := ⟨hμ.trans hx'.1, hx'.2⟩
        have hμ' : μ ∈ Ioo 0 m := ⟨hμ, hμm⟩
        have hlt := hsmono hμ' hx0 hx'.1
        simpa [hsμ] using hlt)
  intro v hv hvμ
  rcases lt_or_gt_of_ne hvμ with hlt | hgt
  · have hv' : v ∈ Icc 0 μ := ⟨hv.1, hlt.le⟩
    have h := hleft hv' ⟨hμ.le, le_rfl⟩ hlt
    linarith [hfμ]
  · have hv' : v ∈ Icc μ m := ⟨hgt.le, hv.2⟩
    have h := hright ⟨le_rfl, hμm.le⟩ hv' hgt
    linarith [hfμ]

private lemma rate2_hasDerivAt {N k m v : ℝ}
    (hk : 0 < k) (hp : 0 < m/N) (hp1 : m/N < 1)
    (hv : 0 < v) (hvk : v < k) :
    HasDerivAt (fourBinomialKLRate2 N k m)
      (fourBinomialKLRate2Slope N k m v) v := by
  have hx : 0 < v/k := div_pos hv hk
  have hx1 : v/k < 1 := (div_lt_one hk).2 hvk
  have hmap := (hasDerivAt_id v).div_const k
  have h := (bernoulliKL_hasDerivAt hp hp1 hx hx1).comp v hmap |>.const_mul k
  change HasDerivAt (fun y : ℝ => k * bernoulliKL (m/N) (y/k)) _ v
  apply h.congr_deriv
  unfold fourBinomialKLRate2Slope
  change k * (bernoulliFenchelTilt (m/N) (v/k) * (1/k)) =
    bernoulliFenchelTilt (m/N) (v/k)
  field_simp [hk.ne']

private lemma rate2_slope_hasDerivAt {N k m v : ℝ}
    (hk : 0 < k) (hp : 0 < m/N) (hp1 : m/N < 1)
    (hv : 0 < v) (hvk : v < k) :
    HasDerivAt (fourBinomialKLRate2Slope N k m)
      (1/fourBinomialEnvelope2 k v) v := by
  have hx : 0 < v/k := div_pos hv hk
  have hx1 : v/k < 1 := (div_lt_one hk).2 hvk
  have hmap := (hasDerivAt_id v).div_const k
  have h := (bernoulliFenchelTilt_hasDerivAt hp hp1 hx hx1).comp v hmap
  change HasDerivAt (fun y : ℝ => bernoulliFenchelTilt (m/N) (y/k)) _ v
  apply h.congr_deriv
  change 1/(v/k*(1-v/k))*(1/k) =
    1/(v*(k-v)/k)
  field_simp [hk.ne']

private lemma rate3_hasDerivAt {N k m v : ℝ}
    (hNm : 0 < N-m) (hkNm : k < N-m) (hp : 0 < k/N) (hp1 : k/N < 1)
    (hv : 0 < v) (hvk : v < k) :
    HasDerivAt (fourBinomialKLRate3 N k m)
      (fourBinomialKLRate3Slope N k m v) v := by
  have hx : 0 < (k-v)/(N-m) := div_pos (sub_pos.mpr hvk) hNm
  have hx1 : (k-v)/(N-m) < 1 := by
    apply (div_lt_one hNm).2
    linarith
  have hmap := ((hasDerivAt_const v k).sub (hasDerivAt_id v)).div_const (N-m)
  have h := (bernoulliKL_hasDerivAt hp hp1 hx hx1).comp v hmap |>.const_mul (N-m)
  change HasDerivAt (fun y : ℝ => (N-m) * bernoulliKL (k/N) ((k-y)/(N-m))) _ v
  apply h.congr_deriv
  change (N-m) * (bernoulliFenchelTilt (k/N) ((k-v)/(N-m)) * ((0-1)/(N-m))) =
    -bernoulliFenchelTilt (k/N) ((k-v)/(N-m))
  field_simp [hNm.ne']
  ring

private lemma rate3_slope_hasDerivAt {N k m v : ℝ}
    (hNm : 0 < N-m) (hkNm : k < N-m) (hp : 0 < k/N) (hp1 : k/N < 1)
    (hv : 0 < v) (hvk : v < k) :
    HasDerivAt (fourBinomialKLRate3Slope N k m)
      (1/fourBinomialEnvelope3 N k m v) v := by
  have hx : 0 < (k-v)/(N-m) := div_pos (sub_pos.mpr hvk) hNm
  have hx1 : (k-v)/(N-m) < 1 := by
    apply (div_lt_one hNm).2
    linarith
  have hmap := ((hasDerivAt_const v k).sub (hasDerivAt_id v)).div_const (N-m)
  have h := ((bernoulliFenchelTilt_hasDerivAt hp hp1 hx hx1).comp v hmap).neg
  change HasDerivAt (fun y : ℝ => -bernoulliFenchelTilt (k/N) ((k-y)/(N-m))) _ v
  apply h.congr_deriv
  unfold fourBinomialEnvelope3
  change -(1/((k-v)/(N-m)*(1-(k-v)/(N-m)))*((0-1)/(N-m))) =
    1/((k-v)*(N-m-k+v)/(N-m))
  field_simp [hNm.ne']
  ring

private lemma rate4_hasDerivAt {N k m v : ℝ}
    (hNk : 0 < N-k) (hmNk : m < N-k) (hp : 0 < m/N) (hp1 : m/N < 1)
    (hv : 0 < v) (hvm : v < m) :
    HasDerivAt (fourBinomialKLRate4 N k m)
      (fourBinomialKLRate4Slope N k m v) v := by
  have hx : 0 < (m-v)/(N-k) := div_pos (sub_pos.mpr hvm) hNk
  have hx1 : (m-v)/(N-k) < 1 := by
    apply (div_lt_one hNk).2
    linarith
  have hmap := ((hasDerivAt_const v m).sub (hasDerivAt_id v)).div_const (N-k)
  have h := (bernoulliKL_hasDerivAt hp hp1 hx hx1).comp v hmap |>.const_mul (N-k)
  change HasDerivAt (fun y : ℝ => (N-k) * bernoulliKL (m/N) ((m-y)/(N-k))) _ v
  apply h.congr_deriv
  change (N-k) * (bernoulliFenchelTilt (m/N) ((m-v)/(N-k)) * ((0-1)/(N-k))) =
    -bernoulliFenchelTilt (m/N) ((m-v)/(N-k))
  field_simp [hNk.ne']
  ring

private lemma rate4_slope_hasDerivAt {N k m v : ℝ}
    (hNk : 0 < N-k) (hmNk : m < N-k) (hp : 0 < m/N) (hp1 : m/N < 1)
    (hv : 0 < v) (hvm : v < m) :
    HasDerivAt (fourBinomialKLRate4Slope N k m)
      (1/fourBinomialEnvelope4 N k m v) v := by
  have hx : 0 < (m-v)/(N-k) := div_pos (sub_pos.mpr hvm) hNk
  have hx1 : (m-v)/(N-k) < 1 := by
    apply (div_lt_one hNk).2
    linarith
  have hmap := ((hasDerivAt_const v m).sub (hasDerivAt_id v)).div_const (N-k)
  have h := ((bernoulliFenchelTilt_hasDerivAt hp hp1 hx hx1).comp v hmap).neg
  change HasDerivAt (fun y : ℝ => -bernoulliFenchelTilt (m/N) ((m-y)/(N-k))) _ v
  apply h.congr_deriv
  unfold fourBinomialEnvelope4
  change -(1/((m-v)/(N-k)*(1-(m-v)/(N-k)))*((0-1)/(N-k))) =
    1/((m-v)*(N-k-m+v)/(N-k))
  field_simp [hNk.ne']
  ring

private lemma envelope2_gap {m k v : ℝ} (hm : 0 < m) (hk : 0 < k) :
    m ≤ k →
    fourBinomialEnvelope2 k v-fourBinomialEnvelope1 m v =
      (k-m)*v^2/(m*k) := by
  intro _
  unfold fourBinomialEnvelope1 fourBinomialEnvelope2
  field_simp [hm.ne', hk.ne']
  ring

private lemma envelope3_gap {N k m v : ℝ}
    (hm : 0 < m) (hNm : 0 < N-m) :
    fourBinomialEnvelope3 N k m v-fourBinomialEnvelope1 m v =
      ((k-m)*v^2+(N-m-k)*(m-v)^2+m*(k-m)*(N-m-k))/(m*(N-m)) := by
  unfold fourBinomialEnvelope1 fourBinomialEnvelope3
  field_simp [hm.ne', hNm.ne']
  ring

private lemma envelope4_gap {N k m v : ℝ}
    (hm : 0 < m) (hNk : 0 < N-k) :
    fourBinomialEnvelope4 N k m v-fourBinomialEnvelope1 m v =
      (N-m-k)*(m-v)^2/(m*(N-k)) := by
  unfold fourBinomialEnvelope1 fourBinomialEnvelope4
  field_simp [hm.ne', hNk.ne']
  ring

private lemma fourRate2_lt_R1 {N k m : ℝ}
    (hN : 0 < N) (hm : 0 < m) (hmk : m ≤ k) (hk : k ≤ N/2)
    (_hhalf : 2*m < N) (hkm : m < k) :
    ∀ v ∈ Icc 0 m, v ≠ m*k/N →
      fourBinomialKLRate2 N k m v < binomialKLRate m (k/N) v := by
  let μ := m*k/N
  let f := fun v => binomialKLRate m (k/N) v-fourBinomialKLRate2 N k m v
  let s := fun v => binomialKLSlope m (k/N) v-fourBinomialKLRate2Slope N k m v
  let ds := fun v => 1/klBinomialEnvelope m v-1/fourBinomialEnvelope2 k v
  have hk0 : 0 < k := lt_of_lt_of_le hm hmk
  have hp : 0 < k/N := div_pos hk0 hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith [hk])
  have hp2 : 0 < m/N := div_pos hm hN
  have hp21 : m/N < 1 := (div_lt_one hN).2 (by linarith [_hhalf])
  have hμ : 0 < μ := div_pos (mul_pos hm hk0) hN
  have hμm : μ < m := by
    dsimp [μ]
    rw [div_lt_iff₀ hN]
    nlinarith [hk]
  have hrate1 : Continuous (binomialKLRate m (k/N)) :=
    continuous_const.mul ((bernoulliKL_continuous (k/N) hp hp1).comp
      (continuous_id.div_const m))
  have hrate2 : Continuous (fourBinomialKLRate2 N k m) :=
    continuous_const.mul ((bernoulliKL_continuous (m/N) hp2 hp21).comp
      (continuous_id.div_const k))
  have hfcont : ContinuousOn f (Icc 0 m) := by
    dsimp [f]
    exact (hrate1.sub hrate2).continuousOn
  have hfd : ∀ v ∈ Ioo 0 m, HasDerivAt f (s v) v := by
    intro v hv
    have h1 := binomialKLRate_hasDerivAt hm hp hp1 hv.1 hv.2
    have h2 := rate2_hasDerivAt hk0 hp2 hp21 hv.1 (lt_of_lt_of_le hv.2 hmk)
    dsimp [f, s]
    exact h1.sub h2
  have hsd : ∀ v ∈ Ioo 0 m, HasDerivAt s (ds v) v := by
    intro v hv
    have h1 := binomialKLSlope_hasDerivAt hm hp hp1 hv.1 hv.2
    have h2 := rate2_slope_hasDerivAt hk0 hp2 hp21 hv.1
      (lt_of_lt_of_le hv.2 hmk)
    dsimp [s, ds, fourBinomialEnvelope1, klBinomialEnvelope]
    exact h1.sub h2
  have hds : ∀ v ∈ Ioo 0 m, 0 < ds v := by
    intro v hv
    have hb1 : 0 < klBinomialEnvelope m v := by
      unfold klBinomialEnvelope
      exact div_pos (mul_pos hv.1 (sub_pos.mpr hv.2)) hm
    have hb2 : 0 < fourBinomialEnvelope2 k v := by
      unfold fourBinomialEnvelope2
      exact div_pos (mul_pos hv.1 (sub_pos.mpr (lt_of_lt_of_le hv.2 hmk))) hk0
    have hgap : klBinomialEnvelope m v < fourBinomialEnvelope2 k v := by
      change fourBinomialEnvelope1 m v < fourBinomialEnvelope2 k v
      rw [← sub_pos, envelope2_gap hm hk0 hmk]
      exact div_pos (mul_pos (sub_pos.mpr hkm) (sq_pos_of_pos hv.1))
        (mul_pos hm hk0)
    dsimp [ds]
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hb1 hgap)
  have harg1 : μ/m = k/N := by
    dsimp [μ]
    field_simp [hm.ne', hN.ne']
  have harg2 : μ/k = m/N := by
    dsimp [μ]
    field_simp [hk0.ne', hN.ne']
  have hfμ : f μ = 0 := by
    dsimp [f, binomialKLRate, fourBinomialKLRate2]
    rw [harg1, harg2, bernoulliKL_self hp hp1, bernoulliKL_self hp2 hp21]
    ring
  have hsμ : s μ = 0 := by
    dsimp [s, binomialKLSlope, fourBinomialKLRate2Slope]
    rw [harg1, harg2]
    simp [bernoulliFenchelTilt, hp.ne', hp2.ne',
      (sub_pos.mpr hp1).ne', (sub_pos.mpr hp21).ne']
  intro v hv hvμ
  have h := centered_strict_gap hμ hμm hfcont hfd hsd hds hfμ hsμ v hv hvμ
  exact sub_pos.mp h

private lemma fourRate3_lt_R1 {N k m : ℝ}
    (hN : 0 < N) (hm : 0 < m) (hmk : m ≤ k) (hk : k ≤ N/2)
    (hhalf : 2*m < N) :
    ∀ v ∈ Icc 0 m, v ≠ m*k/N →
      fourBinomialKLRate3 N k m v < binomialKLRate m (k/N) v := by
  let μ := m*k/N
  let f := fun v => binomialKLRate m (k/N) v-fourBinomialKLRate3 N k m v
  let s := fun v => binomialKLSlope m (k/N) v-fourBinomialKLRate3Slope N k m v
  let ds := fun v => 1/klBinomialEnvelope m v-1/fourBinomialEnvelope3 N k m v
  have hk0 : 0 < k := lt_of_lt_of_le hm hmk
  have hNm : 0 < N-m := by linarith [hhalf]
  have hR : 0 < N-m-k := by nlinarith [hk, hhalf]
  have hkNm : k < N-m := by linarith
  have hp : 0 < k/N := div_pos hk0 hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith [hk])
  have hp2 : 0 < m/N := div_pos hm hN
  have hp21 : m/N < 1 := (div_lt_one hN).2 (by linarith [hhalf])
  have hμ : 0 < μ := div_pos (mul_pos hm hk0) hN
  have hμm : μ < m := by
    dsimp [μ]
    rw [div_lt_iff₀ hN]
    nlinarith [hk]
  have hrate1 : Continuous (binomialKLRate m (k/N)) :=
    continuous_const.mul ((bernoulliKL_continuous (k/N) hp hp1).comp
      (continuous_id.div_const m))
  have hrate3 : Continuous (fourBinomialKLRate3 N k m) := by
    have hmap : Continuous (fun v : ℝ => (k-v)/(N-m)) := by fun_prop
    exact continuous_const.mul ((bernoulliKL_continuous (k/N) hp hp1).comp hmap)
  have hfcont : ContinuousOn f (Icc 0 m) := by
    dsimp [f]
    exact (hrate1.sub hrate3).continuousOn
  have hfd : ∀ v ∈ Ioo 0 m, HasDerivAt f (s v) v := by
    intro v hv
    have h1 := binomialKLRate_hasDerivAt hm hp hp1 hv.1 hv.2
    have h2 := rate3_hasDerivAt hNm hkNm hp hp1 hv.1
      (lt_of_lt_of_le hv.2 hmk)
    dsimp [f, s]
    exact h1.sub h2
  have hsd : ∀ v ∈ Ioo 0 m, HasDerivAt s (ds v) v := by
    intro v hv
    have h1 := binomialKLSlope_hasDerivAt hm hp hp1 hv.1 hv.2
    have h2 := rate3_slope_hasDerivAt hNm hkNm hp hp1 hv.1
      (lt_of_lt_of_le hv.2 hmk)
    dsimp [s, ds, fourBinomialEnvelope1, klBinomialEnvelope]
    exact h1.sub h2
  have hds : ∀ v ∈ Ioo 0 m, 0 < ds v := by
    intro v hv
    have hb1 : 0 < klBinomialEnvelope m v := by
      unfold klBinomialEnvelope
      exact div_pos (mul_pos hv.1 (sub_pos.mpr hv.2)) hm
    have hb3 : 0 < fourBinomialEnvelope3 N k m v := by
      unfold fourBinomialEnvelope3
      exact div_pos (mul_pos (sub_pos.mpr (lt_of_lt_of_le hv.2 hmk))
        (by nlinarith [hR, hv.1] : 0 < N-m-k+v)) hNm
    have hgap0 := envelope3_gap (N:=N) (k:=k) (m:=m) (v:=v) hm hNm
    have hgap : klBinomialEnvelope m v < fourBinomialEnvelope3 N k m v := by
      change fourBinomialEnvelope1 m v < fourBinomialEnvelope3 N k m v
      rw [← sub_pos, hgap0]
      apply div_pos
      · have hterm : 0 < (N-m-k)*(m-v)^2 :=
          mul_pos hR (sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hv.2)))
        have hterm0 : 0 ≤ (k-m)*v^2 := mul_nonneg (sub_nonneg.mpr hmk) (sq_nonneg v)
        have hterm1 : 0 ≤ m*(k-m)*(N-m-k) := by positivity
        linarith
      · exact mul_pos hm hNm
    dsimp [ds]
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hb1 hgap)
  have harg1 : μ/m = k/N := by
    dsimp [μ]
    field_simp [hm.ne', hN.ne']
  have harg3 : (k-μ)/(N-m) = k/N := by
    dsimp [μ]
    field_simp [hN.ne', hNm.ne']
  have hfμ : f μ = 0 := by
    dsimp [f, binomialKLRate, fourBinomialKLRate3]
    rw [harg1, harg3, bernoulliKL_self hp hp1]
    ring
  have hsμ : s μ = 0 := by
    dsimp [s, binomialKLSlope, fourBinomialKLRate3Slope]
    rw [harg1, harg3]
    simp [bernoulliFenchelTilt, hp.ne', (sub_pos.mpr hp1).ne']
  intro v hv hvμ
  have h := centered_strict_gap hμ hμm hfcont hfd hsd hds hfμ hsμ v hv hvμ
  exact sub_pos.mp h

private lemma fourRate4_lt_R1 {N k m : ℝ}
    (hN : 0 < N) (hm : 0 < m) (hmk : m ≤ k) (hk : k ≤ N/2)
    (hhalf : 2*m < N) :
    ∀ v ∈ Icc 0 m, v ≠ m*k/N →
      fourBinomialKLRate4 N k m v < binomialKLRate m (k/N) v := by
  let μ := m*k/N
  let f := fun v => binomialKLRate m (k/N) v-fourBinomialKLRate4 N k m v
  let s := fun v => binomialKLSlope m (k/N) v-fourBinomialKLRate4Slope N k m v
  let ds := fun v => 1/klBinomialEnvelope m v-1/fourBinomialEnvelope4 N k m v
  have hk0 : 0 < k := lt_of_lt_of_le hm hmk
  have hNk : 0 < N-k := by nlinarith [hk, hhalf]
  have hR : 0 < N-m-k := by nlinarith [hk, hhalf]
  have hmNk : m < N-k := by linarith
  have hp : 0 < k/N := div_pos hk0 hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith [hk])
  have hp2 : 0 < m/N := div_pos hm hN
  have hp21 : m/N < 1 := (div_lt_one hN).2 (by linarith [hhalf])
  have hμ : 0 < μ := div_pos (mul_pos hm hk0) hN
  have hμm : μ < m := by
    dsimp [μ]
    rw [div_lt_iff₀ hN]
    nlinarith [hk]
  have hrate1 : Continuous (binomialKLRate m (k/N)) :=
    continuous_const.mul ((bernoulliKL_continuous (k/N) hp hp1).comp
      (continuous_id.div_const m))
  have hrate4 : Continuous (fourBinomialKLRate4 N k m) := by
    have hmap : Continuous (fun v : ℝ => (m-v)/(N-k)) := by fun_prop
    exact continuous_const.mul ((bernoulliKL_continuous (m/N) hp2 hp21).comp hmap)
  have hfcont : ContinuousOn f (Icc 0 m) := by
    dsimp [f]
    exact (hrate1.sub hrate4).continuousOn
  have hfd : ∀ v ∈ Ioo 0 m, HasDerivAt f (s v) v := by
    intro v hv
    have h1 := binomialKLRate_hasDerivAt hm hp hp1 hv.1 hv.2
    have h2 := rate4_hasDerivAt hNk hmNk hp2 hp21 hv.1 hv.2
    dsimp [f, s]
    exact h1.sub h2
  have hsd : ∀ v ∈ Ioo 0 m, HasDerivAt s (ds v) v := by
    intro v hv
    have h1 := binomialKLSlope_hasDerivAt hm hp hp1 hv.1 hv.2
    have h2 := rate4_slope_hasDerivAt hNk hmNk hp2 hp21 hv.1 hv.2
    dsimp [s, ds, fourBinomialEnvelope1, klBinomialEnvelope]
    exact h1.sub h2
  have hds : ∀ v ∈ Ioo 0 m, 0 < ds v := by
    intro v hv
    have hb1 : 0 < klBinomialEnvelope m v := by
      unfold klBinomialEnvelope
      exact div_pos (mul_pos hv.1 (sub_pos.mpr hv.2)) hm
    have hb4 : 0 < fourBinomialEnvelope4 N k m v := by
      unfold fourBinomialEnvelope4
      exact div_pos (mul_pos (sub_pos.mpr hv.2)
        (by nlinarith [hR, hv.1] : 0 < N-k-m+v)) hNk
    have hgap0 := envelope4_gap (N:=N) (k:=k) (m:=m) (v:=v) hm hNk
    have hgap : klBinomialEnvelope m v < fourBinomialEnvelope4 N k m v := by
      change fourBinomialEnvelope1 m v < fourBinomialEnvelope4 N k m v
      rw [← sub_pos, hgap0]
      exact div_pos (mul_pos hR (sq_pos_of_ne_zero (ne_of_gt (sub_pos.mpr hv.2))))
        (mul_pos hm hNk)
    dsimp [ds]
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hb1 hgap)
  have harg1 : μ/m = k/N := by
    dsimp [μ]
    field_simp [hm.ne', hN.ne']
  have harg4 : (m-μ)/(N-k) = m/N := by
    dsimp [μ]
    field_simp [hN.ne', hNk.ne']
  have hfμ : f μ = 0 := by
    dsimp [f, binomialKLRate, fourBinomialKLRate4]
    rw [harg1, harg4, bernoulliKL_self hp hp1, bernoulliKL_self hp2 hp21]
    ring
  have hsμ : s μ = 0 := by
    dsimp [s, binomialKLSlope, fourBinomialKLRate4Slope]
    rw [harg1, harg4]
    simp [bernoulliFenchelTilt, hp.ne', hp2.ne',
      (sub_pos.mpr hp1).ne', (sub_pos.mpr hp21).ne']
  intro v hv hvμ
  have h := centered_strict_gap hμ hμm hfcont hfd hsd hds hfμ hsμ v hv hvμ
  exact sub_pos.mp h

private lemma fourRate2_eq_R1_at_mean {N k m : ℝ}
    (hN : 0 < N) (hm : 0 < m) (hk : 0 < k)
    (hp : 0 < k/N) (hp1 : k/N < 1)
    (hp2 : 0 < m/N) (hp21 : m/N < 1) :
    fourBinomialKLRate2 N k m (m*k/N)=binomialKLRate m (k/N) (m*k/N) := by
  have harg1 : (m*k/N)/m = k/N := by field_simp [hm.ne',hN.ne']
  have harg2 : (m*k/N)/k = m/N := by field_simp [hk.ne',hN.ne']
  unfold fourBinomialKLRate2 binomialKLRate
  rw [harg1,harg2,bernoulliKL_self hp hp1,bernoulliKL_self hp2 hp21]
  ring

private lemma fourRate3_eq_R1_at_mean {N k m : ℝ}
    (hN : 0 < N) (hm : 0 < m) (hk : 0 < k)
    (hNm : 0 < N-m) (hp : 0 < k/N) (hp1 : k/N < 1) :
    fourBinomialKLRate3 N k m (m*k/N)=binomialKLRate m (k/N) (m*k/N) := by
  have harg1 : (m*k/N)/m = k/N := by field_simp [hm.ne',hN.ne']
  have harg3 : (k-m*k/N)/(N-m) = k/N := by
    field_simp [hN.ne',hNm.ne']
  unfold fourBinomialKLRate3 binomialKLRate
  rw [harg1,harg3,bernoulliKL_self hp hp1]
  ring

private lemma fourRate4_eq_R1_at_mean {N k m : ℝ}
    (hN : 0 < N) (hm : 0 < m) (hk : 0 < k)
    (hNk : 0 < N-k) (hp : 0 < k/N) (hp1 : k/N < 1)
    (hp2 : 0 < m/N) (hp21 : m/N < 1) :
    fourBinomialKLRate4 N k m (m*k/N)=binomialKLRate m (k/N) (m*k/N) := by
  have harg1 : (m*k/N)/m = k/N := by field_simp [hm.ne',hN.ne']
  have harg4 : (m-m*k/N)/(N-k) = m/N := by
    field_simp [hN.ne',hNk.ne']
  unfold fourBinomialKLRate4 binomialKLRate
  rw [harg1,harg4,bernoulliKL_self hp hp1,bernoulliKL_self hp2 hp21]
  ring

/-- On the stated half-population domain, the ordinary binomial KL rate is
the maximum of the four sampling/complementation rates.  Equality with the
second rate also occurs identically in the degenerate comparison case `k=m`;
the third and fourth rates meet it only at the mean. -/
theorem fourBinomialKLRate_comparisons {N k m v : ℝ}
    (hN : 0 < N) (hm : 0 < m) (hmk : m ≤ k) (hk : k ≤ N/2)
    (hhalf : 2*m < N) (hv : v ∈ Icc 0 m) :
    (fourBinomialKLRate2 N k m v ≤ binomialKLRate m (k/N) v ∧
      (fourBinomialKLRate2 N k m v=binomialKLRate m (k/N) v ↔
        v=m*k/N ∨ k=m)) ∧
    (fourBinomialKLRate3 N k m v ≤ binomialKLRate m (k/N) v ∧
      (fourBinomialKLRate3 N k m v=binomialKLRate m (k/N) v ↔ v=m*k/N)) ∧
    (fourBinomialKLRate4 N k m v ≤ binomialKLRate m (k/N) v ∧
      (fourBinomialKLRate4 N k m v=binomialKLRate m (k/N) v ↔ v=m*k/N)) := by
  have hk0 : 0 < k := lt_of_lt_of_le hm hmk
  have hp : 0 < k/N := div_pos hk0 hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith [hk])
  have hp2 : 0 < m/N := div_pos hm hN
  have hp21 : m/N < 1 := (div_lt_one hN).2 (by linarith [hhalf])
  have hNk : 0 < N-k := by linarith [hk, hhalf]
  have hNm : 0 < N-m := by linarith [hhalf]
  have hμ0 : 0 < m*k/N := div_pos (mul_pos hm hk0) hN
  have hμm : m*k/N < m := by
    rw [div_lt_iff₀ hN]
    nlinarith [hk]
  have hEq2mean := fourRate2_eq_R1_at_mean hN hm hk0 hp hp1 hp2 hp21
  have hEq3mean := fourRate3_eq_R1_at_mean hN hm hk0 hNm hp hp1
  have hEq4mean := fourRate4_eq_R1_at_mean hN hm hk0 hNk hp hp1 hp2 hp21
  have hrate2eq : k=m → fourBinomialKLRate2 N k m v=binomialKLRate m (k/N) v := by
    intro h
    subst k
    rfl
  have hrate2strict : m<k → v≠m*k/N →
      fourBinomialKLRate2 N k m v < binomialKLRate m (k/N) v := by
    intro hmk' hmean
    exact fourRate2_lt_R1 hN hm hmk hk hhalf hmk' v hv hmean
  have hrate3strict : v≠m*k/N →
      fourBinomialKLRate3 N k m v < binomialKLRate m (k/N) v :=
    fourRate3_lt_R1 hN hm hmk hk hhalf v hv
  have hrate4strict : v≠m*k/N →
      fourBinomialKLRate4 N k m v < binomialKLRate m (k/N) v :=
    fourRate4_lt_R1 hN hm hmk hk hhalf v hv
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · by_cases hmean : v=m*k/N
    · rw [hmean]
      rw [hEq2mean]
    · by_cases hkm : k=m
      · rw [hrate2eq hkm]
      · have hlt : m<k := lt_of_le_of_ne hmk (Ne.symm hkm)
        exact (hrate2strict hlt hmean).le
  · constructor
    · intro heq
      by_cases hmean : v=m*k/N
      · exact Or.inl hmean
      · by_cases hkm : k=m
        · exact Or.inr hkm
        · have hlt := hrate2strict (lt_of_le_of_ne hmk (Ne.symm hkm)) hmean
          linarith
    · rintro (hmean|hkm)
      · rw [hmean,hEq2mean]
      · exact hrate2eq hkm
  · by_cases hmean : v=m*k/N
    · rw [hmean,hEq3mean]
    · exact (hrate3strict hmean).le
  · constructor
    · intro heq
      by_contra hmean
      have hlt := hrate3strict hmean
      linarith
    · intro hmean
      rw [hmean,hEq3mean]
  · by_cases hmean : v=m*k/N
    · rw [hmean,hEq4mean]
    · exact (hrate4strict hmean).le
  · constructor
    · intro heq
      by_contra hmean
      have hlt := hrate4strict hmean
      linarith
    · intro hmean
      rw [hmean,hEq4mean]

def fourBinomialKLRateMax (N k m v : ℝ) : ℝ :=
  max (binomialKLRate m (k/N) v)
    (max (fourBinomialKLRate2 N k m v)
      (max (fourBinomialKLRate3 N k m v) (fourBinomialKLRate4 N k m v)))

/-- The maximum among the four classical rates is exactly the ordinary
binomial rate on the full supported interval. -/
theorem fourBinomialKLRateMax_eq_R1 {N k m v : ℝ}
    (hN : 0 < N) (hm : 0 < m) (hmk : m ≤ k) (hk : k ≤ N/2)
    (hhalf : 2*m < N) (hv : v ∈ Icc 0 m) :
    fourBinomialKLRateMax N k m v=binomialKLRate m (k/N) v := by
  obtain ⟨⟨h2,_⟩,⟨h3,_⟩,⟨h4,_⟩⟩ :=
    fourBinomialKLRate_comparisons hN hm hmk hk hhalf hv
  unfold fourBinomialKLRateMax
  apply max_eq_left
  exact max_le h2 (max_le h3 h4)

/-- The piecewise rate strictly improves the maximum of all four
sampling/complementation KL rates at every noncentral supported threshold.
The proof combines the four-rate comparison with the existing strict
piecewise-versus-ordinary-binomial theorem. -/
theorem canonicalPiecewiseRate_strict_improves_fourBinomialKLRateMax
    {N k m v : ℝ} (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N)
    (hhalf : 2*m < N) (hv0 : 0 ≤ v) (hvm : v ≤ m)
    (hvμ : v ≠ m*k/N) :
    fourBinomialKLRateMax N k m v < canonicalPiecewiseRate N k m v := by
  have hN : 0 < N := by linarith [hm,hhalf]
  have hkhalf : k ≤ N/2 := by linarith
  have hmax := fourBinomialKLRateMax_eq_R1 hN (by linarith) hmk hkhalf hhalf
    ⟨hv0,hvm⟩
  rw [hmax]
  exact canonicalPiecewiseRate_strict_improves_binomial hm hmk hk hhalf v hvμ

end
end ExactHoeffding
