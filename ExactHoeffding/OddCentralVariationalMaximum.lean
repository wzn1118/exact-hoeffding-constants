import ExactHoeffding.OddCentralSupportFormula
import ExactHoeffding.OddCentralOptimalTilt
import ExactHoeffding.GoalBIndividualMargin

/-! # Attained maximum of the printed odd central finite-sum formula -/

namespace ExactHoeffding
noncomputable section

/-- The support-truncated proxy with the exact ordinary variance at zero. -/
def oddCentralSupportedProxy (n m : ℕ) (t : ℝ) : ℝ :=
  if t = 0 then individualMarginW (2*n+1) m
  else 2 * Real.log (oddCentralSupportedTiltSum n m t) / t^2

/-- The zero branch in the printed formula is the actual central variance. -/
theorem hypergeomCumulant2_oddCentral_eq_W (n m : ℕ) (hm : m ≤ 2*n+1) :
    hypergeomCumulant2 (2*n+1) n m = individualMarginW (2*n+1) m := by
  rw [hypergeom_cumulant2_complete (2*n+1) n m (by omega) hm]
  have hhalf : (2*n+1)/2 = n := by omega
  simp only [individualMarginW, individualMarginM, hhalf]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The complete printed proxy agrees with the actual continuous proxy at
all real tilts, including the removable value at zero. -/
theorem oddCentralSupportedProxy_eq_actual (n m : ℕ)
    (hn : 0 < n) (hm : m ≤ 2*n+1) (t : ℝ) :
    oddCentralSupportedProxy n m t = actualHypergeomProxy (2*n+1) n m t := by
  by_cases ht : t = 0
  · subst t
    simp only [oddCentralSupportedProxy, actualHypergeomProxy, if_pos rfl]
    exact (hypergeomCumulant2_oddCentral_eq_W n m hm).symm
  · rw [oddCentralSupportedProxy, if_neg ht,
      actualHypergeomProxy_eq_quotient (2*n+1) n m (by omega) hm t ht,
      oddCentral_logMGF_eq_supported_sum n m hn hm t]

/-- For every nondegenerate odd central law the exact finite-sum formula
attains its maximum at a nonzero real tilt. Every value is bounded by that
maximum, which equals the actual least proxy and obeys the contact equation.
No uniqueness of the optimizing tilt is imposed. -/
theorem oddCentral_supported_variational_maximum (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hmN : m < 2*n+1) :
    ∃ t : ℝ, t ≠ 0 ∧
      (∀ u : ℝ, oddCentralSupportedProxy n m u ≤ oddCentralSupportedProxy n m t) ∧
      hypergeomOptimalProxy (2*n+1) n m = oddCentralSupportedProxy n m t ∧
      t * deriv (hypergeomCenteredLogMGF (2*n+1) n m) t =
        2 * hypergeomCenteredLogMGF (2*n+1) n m t := by
  obtain ⟨t, ht, hproxy, hstationary⟩ :=
    oddCentral_exists_nonzero_optimal_tilt_stationary n m hn hm hmN
  refine ⟨t, ht, ?_, ?_, hstationary⟩
  · intro u
    rw [oddCentralSupportedProxy_eq_actual n m hn hmN.le u,
      oddCentralSupportedProxy_eq_actual n m hn hmN.le t, ← hproxy]
    exact actualHypergeomProxy_le_optimalProxy (2*n+1) n m (by omega) hmN.le u
  · rw [oddCentralSupportedProxy_eq_actual n m hn hmN.le t]
    exact hproxy

end
end ExactHoeffding
