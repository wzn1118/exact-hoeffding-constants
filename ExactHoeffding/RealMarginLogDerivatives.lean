import ExactHoeffding.RealMarginCumulants
import ExactHoeffding.MGFDerivatives

/-! # Actual logarithmic derivatives for small real imbalance -/

namespace ExactHoeffding

noncomputable section

open Finset

/-- The common falling denominator is positive throughout the legal
sampling domain, independently of the real success margin. -/
theorem realMarginPopulationDenom_pos (N m : ℕ) (hN : 0 < N) (hm : m ≤ N) :
    0 < scaledFalling 1 (1/(N:ℝ)) m := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  apply scaledFalling_pos
  intro i hi
  have hiN : (i:ℝ) < N := by exact_mod_cast (show i < N by omega)
  rw [show 1-(i:ℝ)*(1/(N:ℝ)) = ((N:ℝ)-i)/N by field_simp]
  exact div_pos (sub_pos.mpr hiN) hNr

/-- Explicit normalized probability laws exist on a nonzero open
neighborhood of the balanced real margin, also when `N` is odd. -/
theorem realMarginMass_near_balanced_probability (N m : ℕ) (hN : 0 < N)
    (hm : 2*m ≤ N) (d : ℝ) (hd : |d| < 1/(N:ℝ)) :
    (∀ i ∈ range (m+1), 0 ≤ realMarginMass m (1/(N:ℝ)) ((1-d)/2) i) ∧
      ∑ i ∈ range (m+1), realMarginMass m (1/(N:ℝ)) ((1-d)/2) i = 1 := by
  refine ⟨?_, realMarginMass_sum m _ _
    (realMarginPopulationDenom_pos N m hN (by omega)).ne'⟩
  intro i hi
  exact (realMarginMass_pos_near_balanced N m hN hm d hd i
    (Nat.le_of_lt_succ (Finset.mem_range.mp hi))).le

/-- The centered logarithmic Laplace transform of the actual real law. -/
def realMarginCenteredLogMGF (N m : ℕ) (d t : ℝ) : ℝ :=
  Real.log (finiteMGF (range (m+1))
    (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) (fun i => (i:ℝ)) t) -
    (m:ℝ)*((1-d)/2)*t

/-- The actual second log-Laplace derivative is the manuscript's closed
variance, for every sufficiently small real imbalance. -/
theorem realMarginLogMGF_deriv2_zero (N m : ℕ) (hN : 5 ≤ N)
    (hm : 2*m ≤ N) (d : ℝ) (hd : |d| < 1/(N:ℝ)) :
    iteratedDeriv 2 (fun t => Real.log (finiteMGF (range (m+1))
      (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) (fun i => (i:ℝ)) t)) 0 =
      (m:ℝ)*((N:ℝ)-m)*(1-d^2)/(4*((N:ℝ)-1)) := by
  obtain ⟨hw, hs⟩ := realMarginMass_near_balanced_probability N m (by omega) hm d hd
  rw [finiteLogMGF_deriv2_zero_cumulant _ _ _ hw hs,
    realMarginMass_cumulant2 N m d (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne']
  exact margin_cumulant2_closed N m hN d

/-- The actual third log-Laplace derivative has the exact odd-margin factor. -/
theorem realMarginLogMGF_deriv3_zero (N m : ℕ) (hN : 5 ≤ N)
    (hm : 2*m ≤ N) (d : ℝ) (hd : |d| < 1/(N:ℝ)) :
    iteratedDeriv 3 (fun t => Real.log (finiteMGF (range (m+1))
      (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) (fun i => (i:ℝ)) t)) 0 =
      (m:ℝ)*((N:ℝ)-m)*((N:ℝ)-2*m)*d*(1-d^2)/
        (4*(((N:ℝ)-2)*((N:ℝ)-1))) := by
  obtain ⟨hw, hs⟩ := realMarginMass_near_balanced_probability N m (by omega) hm d hd
  rw [finiteLogMGF_deriv3_zero_cumulant _ _ _ hw hs,
    realMarginMass_cumulant3 N m d (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne']
  exact margin_cumulant3_closed N m hN d

/-- At balance the actual fourth log-Laplace derivative is strictly
negative in the nondegenerate domain needed for the implicit optimizer. -/
theorem realMarginLogMGF_deriv4_zero_balanced (N m : ℕ) (hN : 5 ≤ N)
    (hm : 2*m ≤ N) :
    iteratedDeriv 4 (fun t => Real.log (finiteMGF (range (m+1))
      (realMarginMass m (1/(N:ℝ)) (1/2)) (fun i => (i:ℝ)) t)) 0 =
      -(m:ℝ)*((N:ℝ)-m)*imbalanceD N m /
        (8*((N:ℝ)-3)*((N:ℝ)-1)^2) := by
  have hd : |(0:ℝ)| < 1/(N:ℝ) := by
    simp only [abs_zero]
    have : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  obtain ⟨hw, hs⟩ := realMarginMass_near_balanced_probability N m (by omega) hm 0 hd
  have h := finiteLogMGF_deriv4_zero_cumulant (range (m+1))
    (realMarginMass m (1/(N:ℝ)) ((1-0)/2)) (fun i => (i:ℝ)) hw hs
  rw [realMarginMass_cumulant4 N m 0 (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne',
    margin_cumulant4_zero N m hN] at h
  simpa only [sub_zero] using h

end
end ExactHoeffding
