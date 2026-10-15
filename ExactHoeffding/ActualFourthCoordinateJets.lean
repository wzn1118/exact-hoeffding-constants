import ExactHoeffding.AnalyticCoordinateJets
import ExactHoeffding.RescaledHigherTiltInputs
import ExactHoeffding.RescaledFourthPopulationInputs

/-! # Actual fourth mixed jets at the balanced population limit -/

namespace ExactHoeffding

noncomputable section

open scoped Topology

theorem rescaledProxyExtension_coordinate_jet4 (m : ℕ) (hm : 0 < m) (s : ℝ) :
    let Q : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
    populationPartial (populationPartial (populationPartial (populationPartial Q))) (0, 0) =
        6 * (m : ℝ) * (1 - (m : ℝ)) * (1 - s ^ 2) ∧
    populationPartial (populationPartial (populationPartial (tiltPartial Q))) (0, 0) =
        (m : ℝ) * s * (2 * (m : ℝ) ^ 2 - 9 * (m : ℝ) - s ^ 2 + 7) / 2 ∧
    populationPartial (populationPartial (tiltPartial (tiltPartial Q))) (0, 0) =
        (m : ℝ) * (-6 * (m : ℝ) ^ 2 + 19 * (m : ℝ) + 4 * s ^ 2 - 13) / 24 ∧
    populationPartial (tiltPartial (tiltPartial (tiltPartial Q))) (0, 0) =
        -(m : ℝ) * s / 20 ∧
    tiltPartial (tiltPartial (tiltPartial (tiltPartial Q))) (0, 0) = (m : ℝ) / 60 := by
  let Q : ℝ × ℝ → ℝ := fun u => rescaledProxyExtension m s u.1 u.2
  have hQ : AnalyticAt ℝ Q (0, 0) := rescaledProxyExtension_joint_analytic m s
  have hj (n r : ℕ) := analytic_mixed_coordinate_jets n r Q hQ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change ((populationPartial^[4]) ((tiltPartial^[0]) Q)) (0, 0) = _
    rw [hj 4 0]
    exact rescaledProxyExtension_zero_tilt_deriv4 m s
  · change ((populationPartial^[3]) ((tiltPartial^[1]) Q)) (0, 0) = _
    rw [hj 3 1]
    simpa only [iteratedDeriv_one] using rescaledProxyExtension_tilt_deriv_zero_deriv3 m s
  · change ((populationPartial^[2]) ((tiltPartial^[2]) Q)) (0, 0) = _
    rw [hj 2 2]
    exact rescaledProxyExtension_tilt_deriv2_zero_deriv2 m s
  · change ((populationPartial^[1]) ((tiltPartial^[3]) Q)) (0, 0) = _
    rw [hj 1 3, iteratedDeriv_one]
    exact (rescaledProxyExtension_tilt_deriv3_zero_hasDerivAt m (by omega) s).deriv
  · change ((populationPartial^[0]) ((tiltPartial^[4]) Q)) (0, 0) = _
    rw [hj 0 4, iteratedDeriv_zero]
    exact rescaledProxyExtension_limit_deriv4 m (by omega) s

end

end ExactHoeffding
