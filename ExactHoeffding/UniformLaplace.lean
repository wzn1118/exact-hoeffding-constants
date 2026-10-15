import ExactHoeffding.SharpCurvatureTheorem
import ExactHoeffding.LaplaceEnvelopeTheorem

namespace ExactHoeffding

/-- Global centered log-Laplace domination for every legal finite
hypergeometric law, obtained from the actual all-tilt curvature theorem. -/
theorem hypergeom_uniform_log_laplace_domination (N k m : ℕ)
    (hk : k≤N) (hm : m≤N) (t : ℝ) :
    hypergeomCenteredLogMGF N k m t≤sharpCurvatureConstant N k m*t^2/2 := by
  let y : ℝ→ℝ := fun s => hypergeomTiltMean N k m s-(m:ℝ)*(k:ℝ)/(N:ℝ)
  have hyd (s : ℝ) : HasDerivAt y (hypergeomTiltVariance N k m s) s :=
    (hypergeomTiltMean_hasDerivAt N k m hk hm s).sub_const _
  have hFd := hypergeomCenteredLogMGF_hasDerivAt N k m hk hm
  have hy0 : y 0=0 := by dsimp [y]; rw [hypergeomTiltMean_zero N k m hk hm]; ring
  have hf0 := hypergeomCenteredLogMGF_zero N k m hk hm
  have h := variance_bound_implies_balanced_laplace
    (M := 4*sharpCurvatureConstant N k m) (p := (1:ℝ)/2) hyd hFd
    (by intro s; convert hypergeomTiltVariance_sharp N k m hk hm s using 1 <;> ring) hy0 hf0 t
  unfold balancedBernoulliLogLaplace at h
  convert h using 1 <;> ring

end ExactHoeffding
