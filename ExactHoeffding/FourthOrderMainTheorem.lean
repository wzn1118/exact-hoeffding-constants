import ExactHoeffding.ActualNormalizedFourthCoefficient

/-! # Joint fourth-order theorem for the actual analytic global optimizer

For every fixed positive sample size and real imbalance, one analytic
critical branch has both the cubic tilt expansion and the quartic
normalized-value expansion. The same branch is the unique global optimizer
of every sufficiently large admissible integer-population law. Both
remainders are analytic at inverse population zero. Positive imbalance
gives a positive optimizing tilt on the right of zero.
-/

namespace ExactHoeffding

noncomputable section

open Filter Asymptotics
open scoped Topology

/-- The cubic tilt polynomial for fixed sample size and imbalance. -/
def fixedImbalanceTiltTaylor3 (m : ℕ) (s e : ℝ) : ℝ :=
  4 * s * e + 4 * s * ((m : ℝ) - 1) * e ^ 2 +
    4 * s * (6 * (m : ℝ) + s ^ 2 - 6) / 3 * e ^ 3

/-- The quartic normalized-value polynomial for the same optimizing branch. -/
def fixedImbalanceProxyTaylor4 (m : ℕ) (s e : ℝ) : ℝ :=
  1 + e + (1 - s ^ 2 / 3) * e ^ 2 +
    (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) * e ^ 3 +
    (1 - (4 * (m : ℝ) ^ 2 - 2 * (m : ℝ) - 1) * s ^ 2 / 3 -
      4 * s ^ 4 / 45) * e ^ 4

/-- A single actual analytic critical branch supplies both expansions,
their analytic remainders, and the unique global maximizing tilt of all
eventually admissible integer populations. The inverse-population
neighborhood may depend on the fixed parameters `m` and `s`. -/
theorem actualHypergeomProxy_joint_fourth_order_main
    (m : ℕ) (hm : 0 < m) (s : ℝ) :
    ∃ τ T U : ℝ → ℝ,
      AnalyticAt ℝ τ 0 ∧ AnalyticAt ℝ T 0 ∧ AnalyticAt ℝ U 0 ∧
      τ 0 = 0 ∧ HasDerivAt τ (4 * s) 0 ∧
      (∀ e, τ e = fixedImbalanceTiltTaylor3 m s e + e ^ 4 * T e) ∧
      (∀ e, 4 * rescaledProxyExtension m s e (τ e) /
        ((m : ℝ) * (1 - (m : ℝ) * e)) =
          fixedImbalanceProxyTaylor4 m s e + e ^ 5 * U e) ∧
      (fun e => τ e - fixedImbalanceTiltTaylor3 m s e)
        =O[𝓝 0] (fun e => e ^ 4) ∧
      (fun e => 4 * rescaledProxyExtension m s e (τ e) /
        ((m : ℝ) * (1 - (m : ℝ) * e)) - fixedImbalanceProxyTaylor4 m s e)
        =O[𝓝 0] (fun e => e ^ 5) ∧
      (∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0),
        deriv (rescaledProxyExtension m s u.1) u.2 = 0 ↔ τ u.1 = u.2) ∧
      (0 < s → ∀ᶠ e in 𝓝[>] (0 : ℝ), 0 < τ e) ∧
      (∀ᶠ e in 𝓝 (0 : ℝ), ∀ N k : ℕ,
        2 ≤ N → k ≤ N → m ≤ N → e = 1 / (N : ℝ) →
        2 * (k : ℝ) + s = (N : ℝ) →
        (∀ t, rescaledProxyExtension m s e t = actualHypergeomProxy N k m t) ∧
        (∀ t : ℝ,
          (∀ u : ℝ, actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t) ↔
            t = τ e)) := by
  obtain ⟨τ, hτ, hz, hd, heq⟩ :=
    rescaledProxyExtension_analytic_critical_branch_leading m hm s
  have hτ2 : iteratedDeriv 2 τ 0 / 2 = 4 * s * ((m : ℝ) - 1) := by
    rw [rescaledProxyExtension_critical_branch_deriv2 m hm s τ hτ hz heq]
    ring
  have hτ3 : iteratedDeriv 3 τ 0 / 6 = 4 * s * (6 * (m : ℝ) + s ^ 2 - 6) / 3 := by
    rw [rescaledProxyExtension_critical_branch_deriv3 m hm s τ hτ hz heq]
    ring
  obtain ⟨T, hT, hTeq, hTO⟩ := analytic_cubic_remainder τ hτ
  let R : ℝ → ℝ := fun e => 4 * rescaledProxyExtension m s e (τ e) /
    ((m : ℝ) * (1 - (m : ℝ) * e))
  have hR : AnalyticAt ℝ R 0 :=
    rescaledProxyExtension_normalized_optimum_analytic m hm s τ hτ hz
  have hR0 : R 0 = 1 := rescaledProxyExtension_normalized_optimum_zero m hm s τ hz
  have hR1 : deriv R 0 = 1 :=
    (rescaledProxyExtension_normalized_optimum_hasDerivAt m hm s τ hτ hz).deriv
  have hR2 : iteratedDeriv 2 R 0 / 2 = 1 - s ^ 2 / 3 := by
    rw [rescaledProxyExtension_normalized_optimum_deriv2 m hm s τ hτ hz hd.deriv]
    ring
  have hR3 : iteratedDeriv 3 R 0 / 6 = 1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3 := by
    rw [rescaledProxyExtension_normalized_optimum_deriv3 m hm s τ hτ hz heq]
    ring
  have hR4 : iteratedDeriv 4 R 0 / 24 =
      1 - (4 * (m : ℝ) ^ 2 - 2 * (m : ℝ) - 1) * s ^ 2 / 3 - 4 * s ^ 4 / 45 := by
    rw [rescaledProxyExtension_normalized_optimum_deriv4 m hm s τ hτ hz heq]
    ring
  obtain ⟨U, hU, hUeq, hUO⟩ := analytic_quartic_remainder R hR
  have hτpoly (e : ℝ) : τ e = fixedImbalanceTiltTaylor3 m s e + e ^ 4 * T e := by
    simpa only [hz, hd.deriv, hτ2, hτ3, zero_add, fixedImbalanceTiltTaylor3]
      using hTeq e
  have hRpoly (e : ℝ) : R e = fixedImbalanceProxyTaylor4 m s e + e ^ 5 * U e := by
    simpa only [hR0, hR1, hR2, hR3, hR4, one_mul, fixedImbalanceProxyTaylor4]
      using hUeq e
  refine ⟨τ, T, U, hτ, hT, hU, hz, hd, hτpoly, hRpoly, ?_, ?_, heq, ?_, ?_⟩
  · have hfun : (fun e => τ e - fixedImbalanceTiltTaylor3 m s e) =
        (fun e => τ e - 4 * s * e - 4 * s * ((m : ℝ) - 1) * e ^ 2 -
          4 * s * (6 * (m : ℝ) + s ^ 2 - 6) / 3 * e ^ 3) := by
      funext e
      unfold fixedImbalanceTiltTaylor3
      ring
    rw [hfun]
    simpa only [hz, hd.deriv, hτ2, hτ3, sub_zero] using hTO
  · have hfun : (fun e => R e - fixedImbalanceProxyTaylor4 m s e) =
        (fun e => R e - 1 - e - (1 - s ^ 2 / 3) * e ^ 2 -
          (1 - (2 * (m : ℝ) - 1) * s ^ 2 / 3) * e ^ 3 -
          (1 - (4 * (m : ℝ) ^ 2 - 2 * (m : ℝ) - 1) * s ^ 2 / 3 -
            4 * s ^ 4 / 45) * e ^ 4) := by
      funext e
      unfold fixedImbalanceProxyTaylor4
      ring
    change (fun e => R e - fixedImbalanceProxyTaylor4 m s e) =O[𝓝 0] _
    rw [hfun]
    simpa only [hR0, hR1, hR2, hR3, hR4, one_mul] using hUO
  · intro hs
    exact analytic_branch_eventually_positive τ (4 * s) (by linarith) hz hd
  · filter_upwards [actualHypergeomProxy_critical_branch_is_global m hm s τ heq]
      with e hglobal
    intro N k hN hk hmN he hbalance
    refine ⟨?_, hglobal N k hN hk hmN he hbalance⟩
    intro t
    rw [he]
    exact rescaledProxyExtension_hypergeom N k m s t hN hk hmN (by omega) hbalance

end

end ExactHoeffding
