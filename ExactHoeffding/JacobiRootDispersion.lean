import ExactHoeffding.BernoulliMGFGeometry
import ExactHoeffding.SharpCurvatureTheorem

namespace ExactHoeffding
noncomputable section

/-- Enumerating the actual negative roots identifies the actual tilted
hypergeometric variance with the Bernoulli root-probability variance. -/
theorem jacobiHypergeom_tilt_variance_root_sum (j h r : ℕ) (t : ℝ) :
    hypergeomTiltVariance (jacobiN j h r) (jacobiK j) (jacobiM j h) t =
      (((jacobiPGF j h r).roots.map (fun x =>
        jacobiTiltedRootProbability (Real.exp t) x *
          (1 - jacobiTiltedRootProbability (Real.exp t) x))).sum) := by
  classical
  let roots := (jacobiPGF j h r).roots.toList
  let p : Fin roots.length → ℝ := fun i =>
    jacobiTiltedRootProbability (Real.exp t) (roots.get i)
  have hp (i : Fin roots.length) : p i ∈ Set.Ioo 0 1 := by
    apply jacobiTiltedRootProbability_mem_Ioo (Real.exp_pos t)
    apply jacobiPGF_roots_negative j h r
    exact Multiset.mem_toList.mp (List.get_mem roots i)
  have hmgf (u : ℝ) :
      hypergeomMGF (jacobiN j h r) (jacobiK j) (jacobiM j h) (t+u) /
          hypergeomMGF (jacobiN j h r) (jacobiK j) (jacobiM j h) t =
        Real.exp (0*u) * ∏ i, (1-p i+p i*Real.exp u) := by
    rw [hypergeomMGF_eq_polynomial, hypergeomMGF_eq_polynomial,
      div_div_div_cancel_right₀ (show (Nat.choose (jacobiN j h r) (jacobiM j h) : ℝ) ≠ 0 by
        exact_mod_cast Nat.choose_ne_zero (jacobi_m_le_N j h r)), Real.exp_add]
    simp only [zero_mul, Real.exp_zero, one_mul]
    rw [jacobiHypergeomPolynomial_tilted_bernoulli_pgf j h r (Real.exp_pos t)]
    calc
      _ = (roots.map (fun x => jacobiTiltedRootPGFFactor
            (Real.exp t) x (Real.exp u))).prod := (Multiset.prod_map_toList _ _).symm
      _ = _ := by
        simpa only [p, jacobiTiltedRootPGFFactor, List.get_eq_getElem] using
          (Fin.prod_univ_fun_getElem roots
            (fun x => jacobiTiltedRootPGFFactor (Real.exp t) x (Real.exp u))).symm
  rw [← hypergeomLogMGF_second_deriv_eq_variance _ _ _
    (jacobi_k_le_N j h r) (jacobi_m_le_N j h r)]
  rw [shifted_bernoulli_log_second_deriv
    (hypergeomMGF_pos _ _ _ (jacobi_k_le_N j h r) (jacobi_m_le_N j h r)) p hp hmgf]
  calc
    _ = (roots.map (fun x => jacobiTiltedRootProbability (Real.exp t) x *
          (1 - jacobiTiltedRootProbability (Real.exp t) x))).sum := by
      simpa only [p, List.get_eq_getElem] using
        (Fin.sum_univ_fun_getElem roots (fun x => jacobiTiltedRootProbability (Real.exp t) x *
          (1 - jacobiTiltedRootProbability (Real.exp t) x)))
    _ = _ := Multiset.sum_map_toList _ _

/-- The transformed-root squares are exactly the degree minus four times
the variance of the actual tilted hypergeometric law. -/
theorem jacobi_transformed_root_square_sum (j h r : ℕ) (z : ℝ) (hz : 0 < z) :
    (((jacobiPGF j h r).roots.map (fun x => ((z+x)/(z-x))^2)).sum) =
      (j : ℝ) - 4 * hypergeomTiltVariance
        (jacobiN j h r) (jacobiK j) (jacobiM j h) (Real.log z) := by
  classical
  have hv := jacobiHypergeom_tilt_variance_root_sum j h r (Real.log z)
  rw [Real.exp_log hz] at hv
  rw [hv]
  have heach (x : ℝ) (hx : x ∈ (jacobiPGF j h r).roots) :
      ((z+x)/(z-x))^2 =
        1 - 4 * (jacobiTiltedRootProbability z x * (1-jacobiTiltedRootProbability z x)) := by
    have hxneg := jacobiPGF_roots_negative j h r hx
    unfold jacobiTiltedRootProbability
    field_simp [show z-x ≠ 0 by linarith]
    <;> ring
  calc
    _ = (((jacobiPGF j h r).roots.map (fun x =>
        1 - 4 * (jacobiTiltedRootProbability z x * (1-jacobiTiltedRootProbability z x)))).sum) := by
      apply congrArg Multiset.sum
      exact Multiset.map_congr rfl heach
    _ = _ := by
      rw [Multiset.sum_map_sub, Multiset.sum_map_mul_left]
      simp only [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul,
        mul_one, jacobiPGF_roots_card]

/-- Jacobi root dispersion, derived from the actual all-tilt sharp
hypergeometric curvature bound. Roots are counted with their multiplicities. -/
theorem jacobi_root_dispersion (j h r : ℕ) (z : ℝ) (hz : 0 < z) :
    (j : ℝ) * ((j : ℝ)-1) / ((jacobiN j h r : ℝ)-1) ≤
      (((jacobiPGF j h r).roots.map (fun x => ((z+x)/(z-x))^2)).sum) := by
  rw [jacobi_transformed_root_square_sum j h r z hz]
  by_cases hj : j = 0
  · subst j
    simp only [Nat.cast_zero, zero_mul, zero_div, zero_sub]
    have hv := jacobiHypergeom_tilt_variance_root_sum 0 h r (Real.log z)
    have hroots : (jacobiPGF 0 h r).roots = 0 := by
      apply Multiset.card_eq_zero.mp
      exact jacobiPGF_roots_card 0 h r
    rw [hroots] at hv
    simp only [Multiset.map_zero, Multiset.sum_zero] at hv
    rw [hv]
    norm_num
  · have hj1 : 1 ≤ j := by omega
    have hNR : (2 : ℝ) ≤ jacobiN j h r := by
      exact_mod_cast (show 2 ≤ jacobiN j h r by unfold jacobiN; omega)
    have hden : 0 < (jacobiN j h r : ℝ)-1 := by linarith
    have hv := hypergeomTiltVariance_sharp (jacobiN j h r) (jacobiK j) (jacobiM j h)
      (jacobi_k_le_N j h r) (jacobi_m_le_N j h r) (Real.log z)
    have hb : sharpCurvatureConstant (jacobiN j h r) (jacobiK j) (jacobiM j h) ≤
        (j : ℝ) * ((jacobiN j h r : ℝ)-j) / (4*((jacobiN j h r : ℝ)-1)) := by
      unfold sharpCurvatureConstant jacobiK
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
    have hv' := hv.trans hb
    have halg : (j : ℝ) - 4 *
        ((j : ℝ)*((jacobiN j h r : ℝ)-j)/(4*((jacobiN j h r : ℝ)-1))) =
        (j : ℝ)*((j : ℝ)-1)/((jacobiN j h r : ℝ)-1) := by
      field_simp [hden.ne'] <;> ring
    rw [← halg]
    nlinarith only [hv']

end
end ExactHoeffding
