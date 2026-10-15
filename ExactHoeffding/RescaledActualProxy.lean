import ExactHoeffding.RescaledQLimit
import ExactHoeffding.Sampling
import ExactHoeffding.TiltedVariance

/-! # The analytic proxy extension is the actual finite-law proxy

The zero-tilt branch is proved from the first two actual factorial moments.
The nonzero branch uses the exact MGF bridge and the actual centering factor.
-/

namespace ExactHoeffding

noncomputable section

theorem rescaledFactorialMoment_eq_zero_of_lt (m q : ℕ) (s e : ℝ)
    (hmq : m < q) : rescaledFactorialMoment m s q e = 0 := by
  simp [rescaledFactorialMoment, Nat.descFactorial_eq_zero_iff_lt.mpr hmq]

theorem rescaledMGFQuadratic_tilt_zero (m : ℕ) (s e : ℝ) :
    rescaledMGFQuadratic m s e 0 =
      (rescaledMean m s e + rescaledFactorialMoment m s 2 e) / 2 := by
  unfold rescaledMGFQuadratic
  rw [expQuadraticKernel_at_zero, expSlopeKernel_zero]
  have htail :
      (∑ j ∈ Finset.range (m - 1),
        rescaledFactorialMoment m s (j + 2) e / (Nat.factorial (j + 2) : ℝ) *
          0 ^ j * 1 ^ (j + 2)) = rescaledFactorialMoment m s 2 e / 2 := by
    by_cases hm2 : 2 ≤ m
    · rw [Finset.sum_eq_single 0]
      · norm_num
      · intro j hj hj0
        simp [hj0]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim
    · rw [show m - 1 = 0 by omega,
        rescaledFactorialMoment_eq_zero_of_lt m 2 s e (by omega)]
      simp
  rw [htail]
  ring

/-- The removable value is the variance polynomial in actual factorial moments. -/
theorem rescaledProxyExtension_tilt_zero (m : ℕ) (s e : ℝ) :
    rescaledProxyExtension m s e 0 =
      rescaledMean m s e + rescaledFactorialMoment m s 2 e -
        rescaledMean m s e ^ 2 := by
  unfold rescaledProxyExtension rescaledMGFSlope
  rw [rescaledMGFQuadratic_tilt_zero]
  simp only [zero_mul, add_zero, logQuadraticKernel_zero]
  ring

theorem rescaledMean_hypergeom (N k m : ℕ) (s : ℝ) (hN : 0 < N)
    (hbalance : 2 * (k : ℝ) + s = (N : ℝ)) :
    rescaledMean m s (1 / (N : ℝ)) = (m : ℝ) * (k : ℝ) / N := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  unfold rescaledMean
  field_simp [hN0]
  nlinarith [hbalance]

/-- Along the actual population sequence, the removable value is the variance. -/
theorem rescaledProxyExtension_hypergeom_zero (N k m : ℕ) (s : ℝ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hm : m ≤ N)
    (hbalance : 2 * (k : ℝ) + s = (N : ℝ)) :
    rescaledProxyExtension m s (1 / (N : ℝ)) 0 = hypergeomCumulant2 N k m := by
  rw [rescaledProxyExtension_tilt_zero,
    rescaledMean_hypergeom N k m s (by omega) hbalance,
    rescaledFactorialMoment_hypergeom N k m 2 s (by omega) hk hm hN hbalance]
  change _ = hypergeomRawMoment N k m 2 - hypergeomRawMoment N k m 1 ^ 2
  rw [hypergeom_raw_moment_one N k m (by omega) hk hm,
    hypergeom_raw_moment_two N k m hN hk hm,
    hypergeom_factorial_moment_formula N k m 2 hk hm, if_pos hN,
    Nat.cast_descFactorial_two, Nat.cast_descFactorial_two,
    Nat.cast_descFactorial_two]
  ring

theorem hypergeom_centered_log_identity (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    Real.log (centeredHypergeomMGF N k m t) =
      Real.log (hypergeomMGF N k m t) - (m : ℝ) * (k : ℝ) / N * t := by
  have hpos : 0 < hypergeomMGF N k m t :=
    finiteMGF_pos_of_normalized (Finset.range (m + 1))
      (hypergeomMass N k m) (fun i => (i : ℝ))
      (fun i _ => hypergeomMass_nonneg N k m i) (hypergeomMass_total N k m hk hm) t
  rw [centeredHypergeomMGF_factor,
    Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hpos), Real.log_exp]
  ring

theorem rescaledProxyExtension_hypergeom_nonzero (N k m : ℕ) (s t : ℝ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N) (hmpos : 1 ≤ m)
    (hbalance : 2 * (k : ℝ) + s = (N : ℝ)) (ht : t ≠ 0) :
    rescaledProxyExtension m s (1 / (N : ℝ)) t =
      2 * Real.log (centeredHypergeomMGF N k m t) / t ^ 2 := by
  rw [rescaledProxyExtension_eq_quotient m hmpos,
    rescaledMGF_hypergeom N k m s t hN hk hm hbalance,
    rescaledMean_hypergeom N k m s hN hbalance,
    hypergeom_centered_log_identity N k m hk hm t]
  exact ht

/-- The actual centered proxy, with its variance branch specified at zero. -/
def actualHypergeomProxy (N k m : ℕ) (t : ℝ) : ℝ :=
  if t = 0 then hypergeomCumulant2 N k m
  else 2 * Real.log (centeredHypergeomMGF N k m t) / t ^ 2

theorem rescaledProxyExtension_hypergeom (N k m : ℕ) (s t : ℝ)
    (hN : 2 ≤ N) (hk : k ≤ N) (hm : m ≤ N) (hmpos : 1 ≤ m)
    (hbalance : 2 * (k : ℝ) + s = (N : ℝ)) :
    rescaledProxyExtension m s (1 / (N : ℝ)) t = actualHypergeomProxy N k m t := by
  by_cases ht : t = 0
  · subst t
    simpa [actualHypergeomProxy] using
      rescaledProxyExtension_hypergeom_zero N k m s hN hk hm hbalance
  · simpa [actualHypergeomProxy, ht] using
      rescaledProxyExtension_hypergeom_nonzero N k m s t (by omega) hk hm hmpos
        hbalance ht

end

end ExactHoeffding
