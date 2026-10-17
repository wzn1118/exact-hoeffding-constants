import ExactHoeffding.GoalBOddVariation
import ExactHoeffding.Support

/-! # The odd central variational sum on its exact support -/

namespace ExactHoeffding
noncomputable section

/-- The finite sum printed in the odd-population variational formula. -/
def oddCentralSupportedTiltSum (n m : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (m - n - 1) (min m n),
    hypergeomMass (2*n+1) n m j *
      Real.exp (t * ((j:ℝ) - (n:ℝ)*(m:ℝ)/((2*n+1:ℕ):ℝ)))

/-- Restricting the actual finite exponential sum to the true support does
not change its value. This includes all degenerate sample sizes. -/
theorem oddCentralFiniteTiltSum_eq_supported (n m : ℕ) (t : ℝ) :
    oddCentralFiniteTiltSum n m t = oddCentralSupportedTiltSum n m t := by
  unfold oddCentralFiniteTiltSum finiteMGF oddCentralSupportedTiltSum
  symm
  apply Finset.sum_subset
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    exact Finset.mem_range.mpr (by omega)
  · intro i hi hnot
    have him : i ≤ m := by have := Finset.mem_range.mp hi; omega
    have hnot' : ¬ (m-n-1 ≤ i ∧ i ≤ min m n) := by
      simpa only [Finset.mem_Icc] using hnot
    have hzero : hypergeomMass (2*n+1) n m i = 0 := by
      by_cases hin : i ≤ n
      · have hbelow : i < m-n-1 := by omega
        have hnsub : 2*n+1-n = n+1 := by omega
        have hchoose : Nat.choose (n+1) (m-i) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        simp [hypergeomMass, hypergeomCount, hnsub, hchoose]
      · have hchoose : Nat.choose n i = 0 := Nat.choose_eq_zero_of_lt (by omega)
        simp [hypergeomMass, hypergeomCount, hchoose]
    simp only [hzero, zero_mul]

/-- The actual centered log-MGF is the logarithm of the support-truncated
sum, with the exact endpoints in the manuscript. -/
theorem oddCentral_logMGF_eq_supported_sum (n m : ℕ)
    (hn : 0 < n) (hm : m ≤ 2*n+1) (t : ℝ) :
    hypergeomCenteredLogMGF (2*n+1) n m t =
      Real.log (oddCentralSupportedTiltSum n m t) := by
  rw [oddCentral_logMGF_eq_finite_sum n m hn hm t,
    oddCentralFiniteTiltSum_eq_supported]

/-- The least actual proxy is precisely the variational supremum of the
support-truncated probability sum over nonzero real tilts. -/
theorem hypergeomOptimalProxy_oddCentral_eq_supported_variation (n m : ℕ)
    (hn : 0 < n) (hm : m ≤ 2*n+1) :
    hypergeomOptimalProxy (2*n+1) n m =
      optimalProxy (fun t => Real.log (oddCentralSupportedTiltSum n m t)) := by
  unfold hypergeomOptimalProxy
  congr 1
  funext t
  exact oddCentral_logMGF_eq_supported_sum n m hn hm t

end
end ExactHoeffding
