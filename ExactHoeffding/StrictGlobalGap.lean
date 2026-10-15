import ExactHoeffding.StationaryGlobal

open Filter Set
open scoped Topology

namespace ExactHoeffding

/-- Pointwise strict domination has a uniform gap when the continuous
function tends to zero at both infinities and the ceiling is positive. -/
theorem exists_uniform_strict_ceiling {f : ℝ→ℝ} {C : ℝ}
    (hc : Continuous f) (hC : 0<C)
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0))
    (hstrict : ∀t, f t<C) : ∃D<C, ∀t, f t≤D := by
  have hhalf : 0<C/2 := by linarith
  obtain ⟨L,hL⟩ := eventually_atBot.mp (hbot.eventually (Iio_mem_nhds hhalf))
  obtain ⟨R,hR⟩ := eventually_atTop.mp (htop.eventually (Iio_mem_nhds hhalf))
  let a := min L 0-1
  let b := max R 0+1
  have ha : a≤0 := by dsimp [a]; linarith [min_le_right L 0]
  have hb : 0≤b := by dsimp [b]; linarith [le_max_right R 0]
  have haL : a≤L := by dsimp [a]; linarith [min_le_left L 0]
  have hRb : R≤b := by dsimp [b]; linarith [le_max_left R 0]
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc a b).Nonempty from ⟨0,ha,hb⟩) hc.continuousOn
  refine ⟨max (C/2) (f x),max_lt (by linarith) (hstrict x),?_⟩
  intro t
  by_cases hat : a≤t
  · by_cases htb : t≤b
    · exact (hmax ⟨hat,htb⟩).trans (le_max_right _ _)
    · have hrt : R≤t := hRb.trans (lt_of_not_ge htb).le
      exact (hR t hrt).le.trans (le_max_left _ _)
  · have htl : t≤L := (lt_of_not_ge hat).le.trans haL
    exact (hL t htl).le.trans (le_max_left _ _)

end ExactHoeffding
