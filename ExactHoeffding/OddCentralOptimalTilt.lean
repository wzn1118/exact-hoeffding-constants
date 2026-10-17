import ExactHoeffding.GoalBOddGlobal
import ExactHoeffding.OddCentralStrict

namespace ExactHoeffding
noncomputable section

/-- For every nondegenerate odd central hypergeometric law, an optimal tilt
exists, is nonzero, realizes the least proxy, and satisfies the stationary
contact equation. No uniqueness assertion is needed: every maximizing tilt
has the same contact property. -/
theorem oddCentral_exists_nonzero_optimal_tilt_stationary (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hmN : m < 2 * n + 1) :
    ∃ t : ℝ, t ≠ 0 ∧
      hypergeomOptimalProxy (2 * n + 1) n m =
        actualHypergeomProxy (2 * n + 1) n m t ∧
      t * deriv (hypergeomCenteredLogMGF (2 * n + 1) n m) t =
        2 * hypergeomCenteredLogMGF (2 * n + 1) n m t := by
  have hN : 2 ≤ 2 * n + 1 := by omega
  have hk0 : 0 < n := hn
  have hkN : n < 2 * n + 1 := by omega
  obtain ⟨t, hmax⟩ := actualHypergeomProxy_exists_global_max
    (2 * n + 1) n m hN hk0 hkN hm hmN
  have hproxy := hypergeomOptimalProxy_eq_actual_at_global_max_all
    (2 * n + 1) n m (by omega) (by omega) t hmax
  have ht : t ≠ 0 := by
    intro ht0
    subst t
    have hzero : actualHypergeomProxy (2 * n + 1) n m 0 =
        hypergeomCumulant2 (2 * n + 1) n m := by
      simp [actualHypergeomProxy]
    have hstrict := hypergeomOptimalProxy_odd_center_gt_variance n m hn hm hmN
    rw [hproxy, hzero] at hstrict
    exact (lt_irrefl _) hstrict
  have hstationary := oddCentral_nonzero_maximizer_stationary
    n m hn hmN.le t ht hmax
  exact ⟨t, ht, hproxy, hstationary⟩

/-- Every nonzero global maximizer at the odd central margin satisfies the
stationary contact equation, whether or not the maximizer is unique. -/
theorem oddCentral_every_nonzero_maximizer_stationary (n m : ℕ)
    (hn : 0 < n) (hmN : m ≤ 2 * n + 1) (t : ℝ) (ht : t ≠ 0)
    (hmax : ∀ u : ℝ,
      actualHypergeomProxy (2 * n + 1) n m u ≤
        actualHypergeomProxy (2 * n + 1) n m t) :
    t * deriv (hypergeomCenteredLogMGF (2 * n + 1) n m) t =
      2 * hypergeomCenteredLogMGF (2 * n + 1) n m t :=
  oddCentral_nonzero_maximizer_stationary n m hn hmN t ht hmax

end
end ExactHoeffding
