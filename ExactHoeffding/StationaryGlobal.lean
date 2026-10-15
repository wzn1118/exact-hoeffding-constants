import ExactHoeffding.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set Filter
open scoped Topology

namespace ExactHoeffding

/-- A bound at every stationary point controls a continuous curve globally
when both tails converge to zero and the bound is strictly positive. -/
theorem global_bound_of_stationary_bound {f : ℝ → ℝ} {B : ℝ}
    (hc : Continuous f) (hB : 0<B)
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0))
    (hstationary : ∀ t, deriv f t=0 → f t≤B) : ∀ t, f t≤B := by
  intro t
  by_contra hbad
  have hBt : B<f t := lt_of_not_ge hbad
  have hft : 0<f t := hB.trans hBt
  obtain ⟨L,hL⟩ := eventually_atBot.mp (hbot.eventually (Iio_mem_nhds hft))
  obtain ⟨R,hR⟩ := eventually_atTop.mp (htop.eventually (Iio_mem_nhds hft))
  let a := min L t-1
  let b := max R t+1
  have hat : a<t := by dsimp [a]; linarith [min_le_right L t]
  have htb : t<b := by dsimp [b]; linarith [le_max_right R t]
  have haL : a≤L := by dsimp [a]; linarith [min_le_left L t]
  have hRb : R≤b := by dsimp [b]; linarith [le_max_left R t]
  obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc a b).Nonempty from ⟨t,hat.le,htb.le⟩) hc.continuousOn
  have htx : f t≤f x := hmax ⟨hat.le,htb.le⟩
  have hax : a<x := lt_of_le_of_ne hx.1 (by
    intro h
    have hfa := hL a haL
    rw [h] at hfa
    exact (not_lt_of_ge htx) hfa)
  have hxb : x<b := lt_of_le_of_ne hx.2 (by
    intro h
    have hfb := hR b hRb
    rw [← h] at hfb
    exact (not_lt_of_ge htx) hfb)
  have hlocal : IsLocalMax f x := hmax.isLocalMax (Icc_mem_nhds hax hxb)
  have hstation := hstationary x hlocal.deriv_eq_zero
  exact (not_lt_of_ge (htx.trans hstation)) hBt

end ExactHoeffding
