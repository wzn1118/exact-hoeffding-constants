import ExactHoeffding.MGFDerivatives
import Mathlib.Analysis.Calculus.Taylor

/-!
# Fourth-order Taylor formulas for the actual hypergeometric log-MGF

The population parameters are fixed and valid. The Peano remainder is for
`t → 0`; no uniform or globally optimized `N → ∞` expansion is asserted.
-/

namespace ExactHoeffding

noncomputable section

open scoped Topology

/-- The fourth-order ordinary cumulant Taylor polynomial. -/
def hypergeomLogMGFTaylor4 (N k m : ℕ) (t : ℝ) : ℝ :=
  hypergeomCumulant1 N k m * t + hypergeomCumulant2 N k m * t ^ 2 / 2 +
    hypergeomCumulant3 N k m * t ^ 3 / 6 + hypergeomCumulant4 N k m * t ^ 4 / 24

theorem hypergeom_logMGF_taylor4_eq (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    taylorWithinEval (fun u => Real.log (hypergeomMGF N k m u)) 4
        Set.univ 0 t = hypergeomLogMGFTaylor4 N k m t := by
  norm_num [taylor_within_apply, Finset.sum_range_succ, iteratedDerivWithin_univ,
    iteratedDeriv_zero, hypergeomMGF_zero N k m hk hm,
    hypergeom_logMGF_deriv1_zero N k m hk hm,
    hypergeom_logMGF_deriv2_zero N k m hk hm,
    hypergeom_logMGF_deriv3_zero N k m hk hm,
    hypergeom_logMGF_deriv4_zero N k m hk hm,
    hypergeomLogMGFTaylor4, smul_eq_mul]
  ring

/-- The fourth-order expansion of the actual logarithmic MGF has Peano
remainder `o(t^4)` for every fixed valid finite law. -/
theorem hypergeom_logMGF_taylor4_isLittleO (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    (fun t => Real.log (hypergeomMGF N k m t) - hypergeomLogMGFTaylor4 N k m t)
      =o[𝓝 0] (fun t : ℝ => t ^ 4) := by
  simpa only [sub_zero, hypergeom_logMGF_taylor4_eq N k m hk hm] using
    (taylor_isLittleO_univ (x₀ := 0) (n := 4) (hypergeom_logMGF_contDiff N k m 4 hk hm))

/-- The fourth-order expansion has an actual fifth-derivative Lagrange
remainder for every nonzero real tilt, on either side of zero. -/
theorem hypergeom_logMGF_taylor4_lagrange (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) (ht : t ≠ 0) :
    ∃ u ∈ Set.uIoo (0 : ℝ) t,
      Real.log (hypergeomMGF N k m t) - hypergeomLogMGFTaylor4 N k m t =
        iteratedDeriv 5 (fun v => Real.log (hypergeomMGF N k m v)) u * t ^ 5 / 120 := by
  have hne : (0 : ℝ) ≠ t := Ne.symm ht
  have hpoly :
      taylorWithinEval (fun v => Real.log (hypergeomMGF N k m v)) 4
          (Set.uIcc 0 t) 0 t =
        taylorWithinEval (fun v => Real.log (hypergeomMGF N k m v)) 4
          Set.univ 0 t := by
    rw [taylor_within_apply, taylor_within_apply]
    apply Finset.sum_congr rfl
    intro q hq
    rw [iteratedDerivWithin_univ,
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne)
        (hypergeom_logMGF_contDiff N k m q hk hm).contDiffAt Set.left_mem_uIcc]
  obtain ⟨u, hu, h⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 4) hne
      (hypergeom_logMGF_contDiff N k m 5 hk hm).contDiffOn
  refine ⟨u, hu, ?_⟩
  rw [hpoly, hypergeom_logMGF_taylor4_eq N k m hk hm] at h
  simpa only [sub_zero, show (Nat.factorial 5 : ℝ) = 120 by norm_num] using h

end

end ExactHoeffding
