import ExactHoeffding.FourthOrderMainTheorem

/-! # Typed contract for the appendix's fourth-order optimizer theorem

The contract is stated for the actual finite-population hypergeometric proxy.
Its analytic branch supplies the printed tilt and proxy coefficients, their
remainders, and eventual global uniqueness on every admissible population
sequence.
-/

namespace ExactHoeffding
noncomputable section
open Filter Asymptotics
open scoped Topology

theorem manuscript_thm_odd_expansion_contract
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
  exact actualHypergeomProxy_joint_fourth_order_main m hm s

end
end ExactHoeffding
