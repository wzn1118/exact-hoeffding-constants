import ExactHoeffding.OddCentralVariationalMaximum
import ExactHoeffding.HypergeometricTail

/-! # Odd central variational boundary cases -/

namespace ExactHoeffding
noncomputable section

/-- Sampling zero elements has unit MGF at every tilt. -/
theorem hypergeomMGF_zero_draws_all_tilts (N k : ℕ) (t : ℝ) :
    hypergeomMGF N k 0 t = 1 := by
  unfold hypergeomMGF finiteMGF
  simp [hypergeomMass_no_draws]

/-- The centered log-MGF vanishes identically when no elements are drawn. -/
theorem hypergeomCenteredLogMGF_zero_draws_all_tilts (N k : ℕ) (t : ℝ) :
    hypergeomCenteredLogMGF N k 0 t = 0 := by
  rw [hypergeomCenteredLogMGF, hypergeomMGF_zero_draws_all_tilts]
  simp

/-- Full-population sampling is deterministic, with centered log-MGF zero. -/
theorem hypergeomCenteredLogMGF_full_draws_all_tilts (N k : ℕ)
    (hk : k ≤ N) (hN : 0 < N) (t : ℝ) :
    hypergeomCenteredLogMGF N k N t = 0 := by
  rw [hypergeomCenteredLogMGF,
    hypergeomMGF_sample_complement N k N hk le_rfl t]
  simp only [Nat.sub_self]
  rw [hypergeomMGF_zero_draws_all_tilts]
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [mul_one, Real.log_exp]
  field_simp [hNreal]
  ring

/-- At zero tilt, the support-truncated variational proxy is the actual
un-tilted hypergeometric variance. -/
theorem oddCentralSupportedProxy_zero_eq_variance (n m : ℕ)
    (hn : 0 < n) (hm : m ≤ 2*n+1) :
    oddCentralSupportedProxy n m 0 = hypergeomTiltVariance (2*n+1) n m 0 := by
  rw [oddCentralSupportedProxy_eq_actual n m hn hm 0]
  rw [actualHypergeomProxy, if_pos rfl,
    hypergeom_cumulant2_complete (2*n+1) n m (by omega) hm,
    hypergeomTiltVariance_zero (2*n+1) n m (by omega) hm]

/-- On either odd-central sample-size boundary, the finite-sum proxy is
identically zero. -/
theorem oddCentralSupportedProxy_boundary_zero (n m : ℕ)
    (hn : 0 < n) (hm : m = 0 ∨ m = 2*n+1) (t : ℝ) :
    oddCentralSupportedProxy n m t = 0 := by
  have hmle : m ≤ 2*n+1 := by omega
  rw [oddCentralSupportedProxy_eq_actual n m hn hmle t]
  have hψ : hypergeomCenteredLogMGF (2*n+1) n m t = 0 := by
    rcases hm with hzero | hfull
    · subst m
      exact hypergeomCenteredLogMGF_zero_draws_all_tilts _ _ _
    · subst m
      exact hypergeomCenteredLogMGF_full_draws_all_tilts _ _ (by omega) (by omega) _
  by_cases ht : t = 0
  · subst t
    simp only [actualHypergeomProxy, if_pos rfl]
    rw [hypergeom_cumulant2_complete (2*n+1) n m (by omega) hmle]
    rcases hm with hzero | hfull
    · subst m
      simp
    · subst m
      simp
  · have hmgf : centeredHypergeomMGF (2*n+1) n m t = 1 := by
      rw [centeredHypergeomMGF_eq_exp_log (2*n+1) n m (by omega) hmle t,
        hψ, Real.exp_zero]
    simp [actualHypergeomProxy, ht, hmgf]

/-- The actual least quadratic proxy is zero on the odd-central boundary
laws. Every nonzero tilt therefore maximizes the support-truncated formula;
no artificial uniqueness condition is imposed. -/
theorem oddCentralOptimalProxy_boundary_zero (n m : ℕ)
    (hn : 0 < n) (hm : m = 0 ∨ m = 2*n+1) :
    hypergeomOptimalProxy (2*n+1) n m = 0 := by
  have hψ : ∀ t : ℝ, hypergeomCenteredLogMGF (2*n+1) n m t = 0 := by
    intro t
    rcases hm with hzero | hfull
    · subst m
      exact hypergeomCenteredLogMGF_zero_draws_all_tilts _ _ _
    · subst m
      exact hypergeomCenteredLogMGF_full_draws_all_tilts _ _ (by omega) (by omega) _
  have hopt : IsOptimalQuadraticProxy
      (hypergeomCenteredLogMGF (2*n+1) n m) 0 := by
    constructor
    · intro t
      rw [hψ t]
      norm_num
    · intro D hD
      have h := hD 1
      rw [hψ 1] at h
      norm_num at h
      linarith
  exact optimalProxy_eq_of_optimal _ (hψ 0) 0 hopt

/-- Every nonzero tilt is a maximizing point in the boundary branch, while
its stationary contact equation reduces to the deterministic identity 0=0. -/
theorem oddCentral_boundary_every_nonzero_tilt_maximizes (n m : ℕ)
    (hn : 0 < n) (hm : m = 0 ∨ m = 2*n+1) (t : ℝ) (ht : t ≠ 0) :
    (∀ u : ℝ, oddCentralSupportedProxy n m u ≤ oddCentralSupportedProxy n m t) ∧
      hypergeomOptimalProxy (2*n+1) n m = oddCentralSupportedProxy n m t ∧
      t * deriv (hypergeomCenteredLogMGF (2*n+1) n m) t =
        2 * hypergeomCenteredLogMGF (2*n+1) n m t := by
  have hproxy (u : ℝ) := oddCentralSupportedProxy_boundary_zero n m hn hm u
  have hopt := oddCentralOptimalProxy_boundary_zero n m hn hm
  refine ⟨?_, ?_, ?_⟩
  · intro u
    rw [hproxy u, hproxy t]
  · rw [hopt, hproxy t]
  · have hψ : ∀ u : ℝ, hypergeomCenteredLogMGF (2*n+1) n m u = 0 := by
      intro u
      rcases hm with hzero | hfull
      · subst m
        exact hypergeomCenteredLogMGF_zero_draws_all_tilts _ _ _
      · subst m
        exact hypergeomCenteredLogMGF_full_draws_all_tilts _ _ (by omega) (by omega) _
    have hfun : hypergeomCenteredLogMGF (2*n+1) n m = fun _ => 0 := funext hψ
    rw [hfun]
    simp

end
end ExactHoeffding
