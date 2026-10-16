import ExactHoeffding.HypergeometricLaplace
import ExactHoeffding.RescaledActualProxy
import ExactHoeffding.AuxiliaryCurvature
import ExactHoeffding.CurvatureNonnegative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ExactHoeffding
noncomputable section
open Set

 theorem hypergeomCenteredLogMGF_nonneg (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    0 ≤ hypergeomCenteredLogMGF N k m t := by
  by_cases ht : t = 0
  · simp [ht, hypergeomCenteredLogMGF_zero N k m hk hm]
  · have hcurv := hypergeomLogMGF_integrated_curvature N k m hk hm t ht
    have hnon : 0 ≤ ∫ u : ℝ in (0 : ℝ)..1,
        (1 - u) * deriv (deriv (fun v => Real.log
          (centeredHypergeomMGF N k m v))) (u * t) := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro u hu
      have hu0 : 0 ≤ 1 - u := by linarith [hu.2]
      have hv : 0 ≤ deriv (deriv (fun v => Real.log
          (centeredHypergeomMGF N k m v))) (u * t) := by
        rw [centeredHypergeomLogMGF_second_deriv N k m hk hm]
        exact hypergeomLogMGF_second_deriv_nonneg N k m hk hm (u*t)
      exact mul_nonneg hu0 hv
    have hsq : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hscaled : 0 ≤ 2 * Real.log (centeredHypergeomMGF N k m t) / t ^ 2 := by
      rw [hcurv]
      exact mul_nonneg (by norm_num) hnon
    have hn : 0 ≤ 2 * Real.log (centeredHypergeomMGF N k m t) := by
      have htmp := (le_div_iff₀ hsq).mp hscaled
      simpa using htmp
    change 0 ≤ Real.log (hypergeomMGF N k m t) - (m : ℝ) * (k : ℝ) / N * t
    rw [← hypergeom_centered_log_identity N k m hk hm t]
    linarith

end
end ExactHoeffding
