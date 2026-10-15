import ExactHoeffding.HypergeometricODE
import ExactHoeffding.OrdinaryMomentsComplete

namespace ExactHoeffding

theorem hypergeomTiltMean_zero (N k m : ℕ) (hk : k≤N) (hm : m≤N) :
    hypergeomTiltMean N k m 0=(m:ℝ)*(k:ℝ)/(N:ℝ) := by
  unfold hypergeomTiltMean
  rw [hypergeomMGF_zero N k m hk hm]
  simp only [finiteTiltFirst,zero_mul,Real.exp_zero,mul_one,div_one]
  simpa only [mul_comm] using hypergeom_mean_complete N k m hk hm

theorem hypergeomTiltVariance_zero (N k m : ℕ) (hk : k≤N) (hm : m≤N) :
    hypergeomTiltVariance N k m 0=
      (m:ℝ)*(k:ℝ)*((N-k:ℕ):ℝ)*((N-m:ℕ):ℝ)/
        ((N:ℝ)^2*((N:ℝ)-1)) := by
  rw [← hypergeomTiltVariance_centered_square N k m hk hm 0,
    hypergeomTiltMean_zero N k m hk hm]
  unfold hypergeomTiltExpectation
  rw [hypergeomMGF_zero N k m hk hm]
  simp only [zero_mul,Real.exp_zero,mul_one,div_one]
  simpa only [mul_comm] using hypergeom_variance_complete N k m hk hm

end ExactHoeffding
