import ExactHoeffding.OptimalProxyAsymptotics
import ExactHoeffding.RescaledActualProxy
import ExactHoeffding.Cumulants

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- The finite probability sum for the centered tilt at the odd central
success count. Terms outside the hypergeometric support vanish. -/
def oddCentralFiniteTiltSum (n m : ℕ) (t : ℝ) : ℝ :=
  finiteMGF (Finset.range (m + 1)) (hypergeomMass (2 * n + 1) n m)
    (fun j => (j : ℝ) - (n : ℝ) * (m : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) t

private theorem oddCentral_actualProxy_eq_quotient (n m : ℕ)
    (hn : 0 < n) (hm : m ≤ 2 * n + 1) (t : ℝ) (ht : t ≠ 0) :
    actualHypergeomProxy (2 * n + 1) n m t =
      2 * hypergeomCenteredLogMGF (2 * n + 1) n m t / t ^ 2 := by
  exact actualHypergeomProxy_eq_quotient (2 * n + 1) n m (by omega) hm t ht

/-- The logarithmic transform in the actual hypergeometric law is exactly
the logarithm of its finite centered probability sum. -/
theorem oddCentral_logMGF_eq_finite_sum (n m : ℕ)
    (hn : 0 < n) (hm : m ≤ 2 * n + 1) (t : ℝ) :
    hypergeomCenteredLogMGF (2 * n + 1) n m t =
      Real.log (oddCentralFiniteTiltSum n m t) := by
  have hN : 0 < 2 * n + 1 := by omega
  have hk : n ≤ 2 * n + 1 := by omega
  change Real.log (hypergeomMGF (2 * n + 1) n m t) -
      (m : ℝ) * (n : ℝ) / ((2 * n + 1 : ℕ) : ℝ) * t =
    Real.log (centeredHypergeomMGF (2 * n + 1) n m t)
  rw [← hypergeom_centered_log_identity (2 * n + 1) n m hk hm t]

/-- At zero tilt the actual proxy is the ordinary variance of the central
hypergeometric law. -/
theorem oddCentral_actualProxy_zero_is_variance (n m : ℕ)
    (hn : 0 < n) (hm : m ≤ 2 * n + 1) :
    actualHypergeomProxy (2 * n + 1) n m 0 =
      hypergeomTiltVariance (2 * n + 1) n m 0 := by
  rw [actualHypergeomProxy, if_pos rfl, hypergeom_cumulant2_complete
    (2 * n + 1) n m (by omega) hm,
    hypergeomTiltVariance_zero (2 * n + 1) n m (by omega) hm]

/-- Every nonzero global maximizer of the actual centered proxy satisfies
the first-order stationarity equation. The statement is pointwise, so it
applies to every maximizer even when there is more than one. -/
theorem oddCentral_nonzero_maximizer_stationary (n m : ℕ)
    (hn : 0 < n) (hm : m ≤ 2 * n + 1) (t : ℝ) (ht : t ≠ 0)
    (hmax : ∀ u : ℝ,
      actualHypergeomProxy (2 * n + 1) n m u ≤
        actualHypergeomProxy (2 * n + 1) n m t) :
    t * deriv (hypergeomCenteredLogMGF (2 * n + 1) n m) t =
      2 * hypergeomCenteredLogMGF (2 * n + 1) n m t := by
  let ψ : ℝ → ℝ := hypergeomCenteredLogMGF (2 * n + 1) n m
  let f : ℝ → ℝ := fun u => 2 * ψ u / u ^ 2
  have hN : 2 ≤ 2 * n + 1 := by omega
  have hk : n ≤ 2 * n + 1 := by omega
  have hlocal : IsLocalMax f t := by
    have hne : {u : ℝ | u ≠ 0} ∈ 𝓝 t := by
      exact (isClosed_singleton (x := (0 : ℝ))).isOpen_compl.mem_nhds (by
        simpa using ht)
    filter_upwards [hne] with u hu
    have h := hmax u
    rw [oddCentral_actualProxy_eq_quotient n m hn hm u hu,
      oddCentral_actualProxy_eq_quotient n m hn hm t ht] at h
    exact h
  have hψ : HasDerivAt ψ
      (hypergeomTiltMean (2 * n + 1) n m t -
        (m : ℝ) * (n : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) t := by
    exact hypergeomCenteredLogMGF_hasDerivAt (2 * n + 1) n m hk hm t
  have hnum : HasDerivAt (fun u => 2 * ψ u)
      (2 * (hypergeomTiltMean (2 * n + 1) n m t -
        (m : ℝ) * (n : ℝ) / ((2 * n + 1 : ℕ) : ℝ))) t := hψ.const_mul 2
  have hden := (hasDerivAt_id t).pow 2
  have hquot0 := hnum.div hden (pow_ne_zero 2 (by simpa [id_eq] using ht))
  have hderiv := hlocal.deriv_eq_zero
  have hquot_deriv := hquot0.deriv
  have hfun : ((fun u : ℝ => 2 * ψ u) / id ^ 2) = f := by
    funext u
    simp [f, id_eq]
  rw [hfun] at hquot_deriv
  norm_num [id_eq] at hquot_deriv
  rw [hquot_deriv] at hderiv
  have hscale :
      2 * (hypergeomTiltMean (2 * n + 1) n m t -
        (m : ℝ) * (n : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) * t ^ 2 -
        (2 * ψ t) * (2 * t) = 0 := by
    have hz := (div_eq_zero_iff).mp hderiv |>.resolve_right
      (pow_ne_zero 2 (pow_ne_zero 2 ht))
    convert hz using 1 <;> norm_num [Nat.cast_add, Nat.cast_one]
  have hfactor :
      2 * t * (t * (hypergeomTiltMean (2 * n + 1) n m t -
        (m : ℝ) * (n : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) -
        2 * ψ t) = 0 := by
    nlinarith [hscale]
  have hinner :
      t * (hypergeomTiltMean (2 * n + 1) n m t -
        (m : ℝ) * (n : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) = 2 * ψ t := by
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · exact False.elim (ht (by linarith))
    · linarith
  have hψderiv := hψ.deriv
  change t * deriv (hypergeomCenteredLogMGF (2 * n + 1) n m) t =
    2 * hypergeomCenteredLogMGF (2 * n + 1) n m t
  simpa [ψ, hψderiv] using hinner

/-- The supremum definition remains valid without an attained optimizer;
when a global maximizer is attained at a nonzero tilt, it realizes the
least proxy and obeys the stationarity equation. -/
theorem oddCentral_nonzero_maximizer_realizes_optimalProxy (n m : ℕ)
    (hn : 0 < n) (hm : m ≤ 2 * n + 1) (t : ℝ) (ht : t ≠ 0)
    (hmax : ∀ u : ℝ,
      actualHypergeomProxy (2 * n + 1) n m u ≤
        actualHypergeomProxy (2 * n + 1) n m t) :
    hypergeomOptimalProxy (2 * n + 1) n m =
        actualHypergeomProxy (2 * n + 1) n m t ∧
      t * deriv (hypergeomCenteredLogMGF (2 * n + 1) n m) t =
        2 * hypergeomCenteredLogMGF (2 * n + 1) n m t := by
  have hproxy := hypergeomOptimalProxy_eq_actual_at_global_max_all
    (2 * n + 1) n m (by omega) hm t hmax
  have hstationary := oddCentral_nonzero_maximizer_stationary n m hn hm t ht hmax
  exact ⟨hproxy, hstationary⟩

end
end ExactHoeffding
