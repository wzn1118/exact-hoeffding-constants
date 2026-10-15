import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Topology

namespace ExactHoeffding

/-- A continuous function starting below zero cannot meet zero before the right
endpoint when its derivative at every interior zero is strictly negative. -/
theorem strict_neg_of_deriv_neg_at_zeros_left
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (ha : f a < 0)
    (hd : ∀ x ∈ Ioo a b, f x = 0 → HasDerivAt f (f' x) x)
    (hs : ∀ x ∈ Ioo a b, f x = 0 → f' x < 0) :
    ∀ x ∈ Ico a b, f x < 0 := by
  intro x hx
  by_contra hfx
  have hfx : 0 ≤ f x := le_of_not_gt hfx
  have hcx : ContinuousOn f (Icc a x) :=
    hc.mono (Icc_subset_Icc le_rfl hx.2.le)
  obtain ⟨z₀, hz₀, hfz₀⟩ :=
    intermediate_value_Icc hx.1 hcx (show (0 : ℝ) ∈ Icc (f a) (f x) from ⟨ha.le, hfx⟩)
  let Z : Set ℝ := Icc a x ∩ f ⁻¹' {0}
  have hZc : IsCompact Z := isCompact_Icc.of_isClosed_subset
    (hcx.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
    (fun _ h => h.1)
  have hZn : Z.Nonempty := ⟨z₀, hz₀, hfz₀⟩
  obtain ⟨z, hzmem, hzleast⟩ := hZc.exists_isLeast hZn
  have hzrange : z ∈ Icc a x := hzmem.1
  have hfz : f z = 0 := hzmem.2
  have haz : a < z := lt_of_le_of_ne hzrange.1 (by
    intro haz
    have : f a = 0 := by simpa [haz] using hfz
    linarith)
  have hzb : z < b := hzrange.2.trans_lt hx.2
  have hbefore : ∀ y ∈ Ioo a z, f y < 0 := by
    intro y hy
    by_contra hfy
    have hfy : 0 ≤ f y := le_of_not_gt hfy
    obtain ⟨w, hw, hfw⟩ := intermediate_value_Icc hy.1.le
      (hcx.mono (Icc_subset_Icc le_rfl (hy.2.le.trans hzrange.2)))
      (show (0 : ℝ) ∈ Icc (f a) (f y) from ⟨ha.le, hfy⟩)
    have hzw : z ≤ w := hzleast ⟨⟨hw.1, hw.2.trans (hy.2.le.trans hzrange.2)⟩, hfw⟩
    exact (not_lt_of_ge (hzw.trans hw.2)) hy.2
  have hlim : Tendsto (slope f z) (𝓝[<] z) (𝓝 (f' z)) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp (hd z ⟨haz, hzb⟩ hfz)).1
  have hnonneg : 0 ≤ f' z := ge_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsLT haz] with y hy
    simp only [slope_def_field, hfz, sub_zero]
    exact div_nonneg_of_nonpos (hbefore y hy).le (sub_nonpos.mpr hy.2.le))
  linarith [hs z ⟨haz, hzb⟩ hfz]

/-- The reflected crossing statement: strict positivity of derivatives at
interior zeros and a negative right endpoint exclude every interior zero. -/
theorem strict_neg_of_deriv_pos_at_zeros_right
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b)) (hb : f b < 0)
    (hd : ∀ x ∈ Ioo a b, f x = 0 → HasDerivAt f (f' x) x)
    (hs : ∀ x ∈ Ioo a b, f x = 0 → 0 < f' x) :
    ∀ x ∈ Ioc a b, f x < 0 := by
  intro x hx
  by_contra hfx
  have hfx : 0 ≤ f x := le_of_not_gt hfx
  have hcx : ContinuousOn f (Icc x b) :=
    hc.mono (Icc_subset_Icc hx.1.le le_rfl)
  obtain ⟨z₀, hz₀, hfz₀⟩ :=
    intermediate_value_Icc' hx.2 hcx (show (0 : ℝ) ∈ Icc (f b) (f x) from ⟨hb.le, hfx⟩)
  let Z : Set ℝ := Icc x b ∩ f ⁻¹' {0}
  have hZc : IsCompact Z := isCompact_Icc.of_isClosed_subset
    (hcx.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton)
    (fun _ h => h.1)
  have hZn : Z.Nonempty := ⟨z₀, hz₀, hfz₀⟩
  obtain ⟨z, hzmem, hzgreatest⟩ := hZc.exists_isGreatest hZn
  have hzrange : z ∈ Icc x b := hzmem.1
  have hfz : f z = 0 := hzmem.2
  have haz : a < z := hx.1.trans_le hzrange.1
  have hzb : z < b := lt_of_le_of_ne hzrange.2 (by
    intro hzb
    have : f b = 0 := by simpa [hzb] using hfz
    linarith)
  have hafter : ∀ y ∈ Ioo z b, f y < 0 := by
    intro y hy
    by_contra hfy
    have hfy : 0 ≤ f y := le_of_not_gt hfy
    obtain ⟨w, hw, hfw⟩ := intermediate_value_Icc' hy.2.le
      (hcx.mono (Icc_subset_Icc (hzrange.1.trans hy.1.le) le_rfl))
      (show (0 : ℝ) ∈ Icc (f b) (f y) from ⟨hb.le, hfy⟩)
    have hwz : w ≤ z := hzgreatest ⟨⟨(hzrange.1.trans hy.1.le).trans hw.1, hw.2⟩, hfw⟩
    exact (not_lt_of_ge (hw.1.trans hwz)) hy.1
  have hlim : Tendsto (slope f z) (𝓝[>] z) (𝓝 (f' z)) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp (hd z ⟨haz, hzb⟩ hfz)).2
  have hnonpos : f' z ≤ 0 := le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT hzb] with y hy
    simp only [slope_def_field, hfz, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (hafter y hy).le (sub_nonneg.mpr hy.1.le))
  linarith [hs z ⟨haz, hzb⟩ hfz]

/-- Global barrier comparison with a prescribed central contact point. The
strict derivative signs are required only at additional potential contacts. -/
theorem global_crossing_barrier
    {f f' : ℝ → ℝ} {a c b : ℝ} (hac : a < c) (hcb : c < b)
    (hc : ContinuousOn f (Icc a b)) (ha : f a < 0) (hb : f b < 0)
    (hcenter : f c = 0)
    (hd : ∀ x ∈ Ioo a b, x ≠ c → f x = 0 → HasDerivAt f (f' x) x)
    (hleft : ∀ x ∈ Ioo a c, f x = 0 → f' x < 0)
    (hright : ∀ x ∈ Ioo c b, f x = 0 → 0 < f' x) :
    (∀ x ∈ Icc a b, f x ≤ 0) ∧
      (∀ x ∈ Icc a b, f x = 0 ↔ x = c) := by
  have hl : ∀ x ∈ Ico a c, f x < 0 :=
    strict_neg_of_deriv_neg_at_zeros_left
      (hc.mono (Icc_subset_Icc le_rfl hcb.le)) ha
      (fun x hx hf => hd x ⟨hx.1, hx.2.trans hcb⟩ (ne_of_lt hx.2) hf) hleft
  have hr : ∀ x ∈ Ioc c b, f x < 0 :=
    strict_neg_of_deriv_pos_at_zeros_right
      (hc.mono (Icc_subset_Icc hac.le le_rfl)) hb
      (fun x hx hf => hd x ⟨hac.trans hx.1, hx.2⟩ (ne_of_gt hx.1) hf) hright
  have hstrict : ∀ x ∈ Icc a b, x ≠ c → f x < 0 := by
    intro x hx hxc
    rcases lt_or_gt_of_ne hxc with hlt | hgt
    · exact hl x ⟨hx.1, hlt⟩
    · exact hr x ⟨hgt, hx.2⟩
  constructor
  · intro x hx
    by_cases hxc : x = c
    · simp [hxc, hcenter]
    · exact (hstrict x hx hxc).le
  · intro x hx
    constructor
    · intro hfx
      by_contra hxc
      linarith [hstrict x hx hxc]
    · rintro rfl
      exact hcenter

end ExactHoeffding
