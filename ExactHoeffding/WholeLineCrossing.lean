import ExactHoeffding.GlobalCrossing

open Set Filter
open scoped Topology

namespace ExactHoeffding

/-- Endpoint negativity at both infinities and the derivative signs at every
noncentral zero determine the complete global equality set. -/
theorem whole_line_crossing_barrier
    {f f' : ℝ → ℝ} (hc : Continuous f) (hz : f 0 = 0)
    (hbot : ∀ᶠ x in atBot, f x < 0) (htop : ∀ᶠ x in atTop, f x < 0)
    (hd : ∀ x, x ≠ 0 → f x = 0 → HasDerivAt f (f' x) x)
    (hleft : ∀ x, x < 0 → f x = 0 → f' x < 0)
    (hright : ∀ x, 0 < x → f x = 0 → 0 < f' x) :
    (∀ x, f x ≤ 0) ∧ (∀ x, f x = 0 ↔ x = 0) := by
  obtain ⟨L, hL⟩ := eventually_atBot.mp hbot
  obtain ⟨R, hR⟩ := eventually_atTop.mp htop
  have hlocal : ∀ x, f x ≤ 0 ∧ (f x = 0 ↔ x = 0) := by
    intro x
    let a := min L (min x 0) - 1
    let b := max R (max x 0) + 1
    have haL : a ≤ L := by dsimp [a]; linarith [min_le_left L (min x 0)]
    have hR_b : R ≤ b := by dsimp [b]; linarith [le_max_left R (max x 0)]
    have hax : a ≤ x := by
      dsimp [a]
      linarith [min_le_right L (min x 0), min_le_left x 0]
    have hxb : x ≤ b := by
      dsimp [b]
      linarith [le_max_right R (max x 0), le_max_left x 0]
    have ha : a < 0 := by
      dsimp [a]
      linarith [min_le_right L (min x 0), min_le_right x 0]
    have hb : 0 < b := by
      dsimp [b]
      linarith [le_max_right R (max x 0), le_max_right x 0]
    have hcompare := global_crossing_barrier ha hb hc.continuousOn
      (hL a haL) (hR b hR_b) hz (fun t _ ht => hd t ht)
      (fun t ht => hleft t ht.2) (fun t ht => hright t ht.1)
    exact ⟨hcompare.1 x ⟨hax, hxb⟩, hcompare.2 x ⟨hax, hxb⟩⟩
  exact ⟨fun x => (hlocal x).1, fun x => (hlocal x).2⟩

/-- Negative limits at the two infinities imply the endpoint conditions in
the whole-line crossing theorem. -/
theorem whole_line_crossing_barrier_of_limits
    {f f' : ℝ → ℝ} {l r : ℝ} (hc : Continuous f) (hz : f 0 = 0)
    (hl : Tendsto f atBot (𝓝 l)) (hr : Tendsto f atTop (𝓝 r))
    (hlneg : l < 0) (hrneg : r < 0)
    (hd : ∀ x, x ≠ 0 → f x = 0 → HasDerivAt f (f' x) x)
    (hleft : ∀ x, x < 0 → f x = 0 → f' x < 0)
    (hright : ∀ x, 0 < x → f x = 0 → 0 < f' x) :
    (∀ x, f x ≤ 0) ∧ (∀ x, f x = 0 ↔ x = 0) := by
  exact whole_line_crossing_barrier hc hz
    (hl.eventually (Iio_mem_nhds hlneg)) (hr.eventually (Iio_mem_nhds hrneg))
    hd hleft hright

end ExactHoeffding
