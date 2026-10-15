import ExactHoeffding.BernoulliProxy
import ExactHoeffding.OptimalProxy
import ExactHoeffding.SharpExample
import ExactHoeffding.Sampling

namespace ExactHoeffding

/-- The exact Bernoulli proxy on the sub-half interval, including the
nonzero tilt realizing the optimal quadratic coefficient. -/
theorem bernoulli_optimal_proxy_subhalf (p : ℝ) (hp : 0<p) (hhalf : p<1/2) :
    IsOptimalQuadraticProxy (bernoulliCenteredLogMGF p)
      ((1-2*p)/(2*Real.log ((1-p)/p))) := by
  have hlog : 0<Real.log ((1-p)/p) :=
    Real.log_pos ((one_lt_div hp).2 (by linarith))
  apply optimalQuadraticProxy_of_contact _ _ (2*Real.log ((1-p)/p))
    (bernoulli_quadratic_bound_lt_half p hp hhalf) (ne_of_gt (by positivity))
  have h := bernoulli_centered_log_odds_equality p hp (by linarith)
  unfold bernoulliCenteredLogMGF
  calc
    Real.log (bernoulliMGF p (2*Real.log ((1-p)/p)))-p*(2*Real.log ((1-p)/p))=
      (1-2*p)*Real.log ((1-p)/p) := by nlinarith only [h]
    _ = _ := by field_simp [ne_of_gt hlog]

theorem hypergeomCenteredLogMGF_singleton (N k : ℕ) (hk : k≤N) (hN : 0<N) :
    hypergeomCenteredLogMGF N k 1=bernoulliCenteredLogMGF ((k:ℝ)/(N:ℝ)) := by
  funext t
  unfold hypergeomCenteredLogMGF bernoulliCenteredLogMGF
  rw [hypergeomMGF_singleton N k hk hN t]
  norm_num

theorem hypergeomOptimalProxy_singleton_subhalf (N k : ℕ)
    (hk0 : 0<k) (hhalf : 2*k<N) :
    hypergeomOptimalProxy N k 1=
      (1-2*(k:ℝ)/(N:ℝ))/(2*Real.log ((1-(k:ℝ)/(N:ℝ))/((k:ℝ)/(N:ℝ)))) := by
  have hN : 0<N := by omega
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hp : 0<(k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast hk0) hNR
  have hph : (k:ℝ)/(N:ℝ)<1/2 := by
    apply (div_lt_iff₀ hNR).2
    have h := show 2*(k:ℝ)<N by exact_mod_cast hhalf
    linarith
  unfold hypergeomOptimalProxy
  rw [hypergeomCenteredLogMGF_singleton N k (by omega) hN]
  have he := optimalProxy_eq_of_optimal (bernoulliCenteredLogMGF ((k:ℝ)/(N:ℝ)))
    (by simp [bernoulliCenteredLogMGF,bernoulliMGF]) _
    (bernoulli_optimal_proxy_subhalf _ hp hph)
  convert he using 1 <;> ring

end ExactHoeffding
