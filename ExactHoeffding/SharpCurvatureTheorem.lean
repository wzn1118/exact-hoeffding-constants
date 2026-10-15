import ExactHoeffding.CanonicalCurvatureComplete
import ExactHoeffding.CurvatureSymmetries

namespace ExactHoeffding

noncomputable def sharpCurvatureConstant (N k m : ℕ) : ℝ :=
  min ((k:ℝ)*((N:ℝ)-k)) ((m:ℝ)*((N:ℝ)-m))/(4*((N:ℝ)-1))

theorem sharpCurvatureConstant_transpose (N k m : ℕ) :
    sharpCurvatureConstant N k m=sharpCurvatureConstant N m k := by
  unfold sharpCurvatureConstant
  rw [min_comm]

theorem sharpCurvatureConstant_success_complement (N k m : ℕ) (hk : k≤N) :
    sharpCurvatureConstant N (N-k) m=sharpCurvatureConstant N k m := by
  unfold sharpCurvatureConstant
  rw [Nat.cast_sub hk]
  have h : ((N:ℝ)-k)*((N:ℝ)-((N:ℝ)-k))=(k:ℝ)*((N:ℝ)-k) := by ring
  rw [h]

theorem sharpCurvatureConstant_sample_complement (N k m : ℕ) (hm : m≤N) :
    sharpCurvatureConstant N k (N-m)=sharpCurvatureConstant N k m := by
  rw [sharpCurvatureConstant_transpose N k (N-m),
    sharpCurvatureConstant_success_complement N m k hm,sharpCurvatureConstant_transpose N m k]

theorem hypergeomTiltVariance_sharp_half_margins (N k m : ℕ)
    (hk : 2*k≤N) (hm : 2*m≤N) (t : ℝ) :
    hypergeomTiltVariance N k m t≤sharpCurvatureConstant N k m := by
  have hkN : k≤N := by omega
  have hmN : m≤N := by omega
  have hkm : k+m≤N := by omega
  by_cases hmk : m≤k
  · rw [← hypergeomLogMGF_second_deriv_eq_variance N k m hkN hmN t]
    exact hypergeom_sharp_curvature_canonical_min N k m hmk hkm t
  · rw [hypergeomTiltVariance_transpose N k m hkN hmN t,
      sharpCurvatureConstant_transpose N k m]
    rw [← hypergeomLogMGF_second_deriv_eq_variance N m k hmN hkN t]
    exact hypergeom_sharp_curvature_canonical_min N m k (by omega) (by omega) t

/-- The sharp upper curvature bound for every legal population, marked and
sample count, and every real exponential tilt, including all degeneracies. -/
theorem hypergeomTiltVariance_sharp (N k m : ℕ) (hk : k≤N) (hm : m≤N) (t : ℝ) :
    hypergeomTiltVariance N k m t≤sharpCurvatureConstant N k m := by
  by_cases hkhalf : 2*k≤N
  · by_cases hmhalf : 2*m≤N
    · exact hypergeomTiltVariance_sharp_half_margins N k m hkhalf hmhalf t
    · rw [hypergeomTiltVariance_sample_complement N k m hk hm t]
      rw [← sharpCurvatureConstant_sample_complement N k m hm]
      exact hypergeomTiltVariance_sharp_half_margins N k (N-m) hkhalf (by omega) (-t)
  · have hkhalf' : 2*(N-k)≤N := by omega
    rw [hypergeomTiltVariance_success_complement N k m hk hm t]
    rw [← sharpCurvatureConstant_success_complement N k m hk]
    by_cases hmhalf : 2*m≤N
    · exact hypergeomTiltVariance_sharp_half_margins N (N-k) m hkhalf' hmhalf (-t)
    · rw [hypergeomTiltVariance_sample_complement N (N-k) m (Nat.sub_le _ _) hm (-t)]
      rw [← sharpCurvatureConstant_sample_complement N (N-k) m hm]
      exact hypergeomTiltVariance_sharp_half_margins N (N-k) (N-m) hkhalf' (by omega) (-(-t))

theorem hypergeomLogMGF_sharp_curvature (N k m : ℕ) (hk : k≤N) (hm : m≤N) (t : ℝ) :
    deriv (deriv (fun s => Real.log (hypergeomMGF N k m s))) t≤
      min ((k:ℝ)*((N:ℝ)-k)) ((m:ℝ)*((N:ℝ)-m))/(4*((N:ℝ)-1)) := by
  rw [hypergeomLogMGF_second_deriv_eq_variance N k m hk hm t]
  exact hypergeomTiltVariance_sharp N k m hk hm t

end ExactHoeffding
