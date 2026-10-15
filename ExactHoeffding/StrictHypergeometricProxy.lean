import ExactHoeffding.StrictBernoulliProxyComparison
import ExactHoeffding.BernoulliProxy
import ExactHoeffding.LaplaceEnvelopeTheorem
import ExactHoeffding.OptimalProxy

namespace ExactHoeffding

theorem scaledBernoulliLogLaplace_quadratic_bound_subhalf
    (M p a t : ℝ) (hM : 0<M) (ha : a≠0) (hp0 : 0<p) (hp : p<1/2) :
    scaledBernoulliLogLaplace M p a t≤
      M*((1-2*p)/(2*Real.log ((1-p)/p)))*t^2/2 := by
  have h := bernoulli_quadratic_bound_lt_half p hp0 hp (a*t)
  have hscale : 0<M/a^2 := div_pos hM (sq_pos_of_ne_zero ha)
  have hs := mul_le_mul_of_nonneg_left h hscale.le
  have hG : scaledBernoulliLogLaplace M p a t=
      (M/a^2)*bernoulliCenteredLogMGF p (a*t) := by
    unfold scaledBernoulliLogLaplace scaledBernoulliDenom bernoulliCenteredLogMGF bernoulliMGF
    ring
  have hR : (M/a^2)*(((1-2*p)/(2*Real.log ((1-p)/p)))*(a*t)^2/2)=
      M*((1-2*p)/(2*Real.log ((1-p)/p)))*t^2/2 := by
    field_simp [ha]
  rw [hG]
  exact hs.trans_eq hR

/-- The actual hypergeometric quotient lies strictly below the scaled sharp
Bernoulli coefficient at every tilt, including its zero-tilt extension. -/
theorem hypergeomProxyQuotient_lt_scaled_bernoulli_proxy
    (N k m : ℕ) (hm : 3≤m) (hmk : m≤k) (hkhalf : 2*k<N) (t : ℝ) :
    hypergeomProxyQuotient N k m t<envelopeM (N:ℝ) (m:ℝ)*
      ((1-2*((k:ℝ)/N))/(2*Real.log ((1-(k:ℝ)/N)/((k:ℝ)/N)))) := by
  by_cases ht : t=0
  · subst t
    exact hypergeomProxyQuotient_zero_lt_scaled_bernoulli_proxy N k m hm hmk hkhalf
  have hmR : (3:ℝ)≤m := by exact_mod_cast hm
  have hmkR : (m:ℝ)≤k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ)<N := by exact_mod_cast hkhalf
  have hN : (0:ℝ)<N := by linarith
  have hM : 0<envelopeM (N:ℝ) (m:ℝ) :=
    envelopeM_positive (N:ℝ) (m:ℝ) hmR (by linarith)
  have ha : envelopeScale (N:ℝ) (m:ℝ)≠0 := by
    unfold envelopeScale
    exact (div_pos (by linarith) (by linarith)).ne'
  have hp0 : 0<(k:ℝ)/N := div_pos (by linarith) hN
  have hp : (k:ℝ)/N<1/2 := (div_lt_iff₀ hN).mpr (by linarith)
  have hstrict := (hypergeom_laplace_envelope N k m hm hmk (by omega) (by omega)).2 t ht
  have hu := scaledBernoulliLogLaplace_quadratic_bound_subhalf
    (envelopeM (N:ℝ) (m:ℝ)) ((k:ℝ)/N) (envelopeScale (N:ℝ) (m:ℝ)) t
    hM ha hp0 hp
  have hbound := hstrict.trans_le hu
  unfold hypergeomProxyQuotient
  rw [Function.update_of_ne ht]
  apply (div_lt_iff₀ (sq_pos_of_ne_zero ht)).mpr
  linarith

/-- Strict Bernoulli domination yields a genuinely smaller global quadratic
proxy, using the actual hypergeometric quotient's two tail limits. -/
theorem hypergeom_exists_proxy_lt_scaled_bernoulli
    (N k m : ℕ) (hm : 3≤m) (hmk : m≤k) (hkhalf : 2*k<N) :
    ∃D<envelopeM (N:ℝ) (m:ℝ)*
      ((1-2*((k:ℝ)/N))/(2*Real.log ((1-(k:ℝ)/N)/((k:ℝ)/N)))),
      IsQuadraticProxy (hypergeomCenteredLogMGF N k m) D := by
  have hkm : k+m≤N := by omega
  have hN : k+m+(N-(k+m))=N := Nat.add_sub_of_le hkm
  have h := hypergeom_exists_proxy_below_of_quotient_strict k m (N-(k+m)) hmk (by omega)
    (envelopeM (N:ℝ) (m:ℝ)*
      ((1-2*((k:ℝ)/N))/(2*Real.log ((1-(k:ℝ)/N)/((k:ℝ)/N)))))
    (scaled_bernoulli_proxy_pos_of_margins N k m hm hmk hkhalf)
    (by rw [hN]; exact hypergeomProxyQuotient_lt_scaled_bernoulli_proxy N k m hm hmk hkhalf)
  simpa only [hN] using h

/-- The true supremum defining the optimal hypergeometric proxy is strictly
smaller than the finite-population-scaled Bernoulli proxy. -/
theorem hypergeomOptimalProxy_lt_scaled_bernoulli
    (N k m : ℕ) (hm : 3≤m) (hmk : m≤k) (hkhalf : 2*k<N) :
    hypergeomOptimalProxy N k m<envelopeM (N:ℝ) (m:ℝ)*
      ((1-2*((k:ℝ)/N))/(2*Real.log ((1-(k:ℝ)/N)/((k:ℝ)/N)))) := by
  obtain ⟨D,hD,hproxy⟩ := hypergeom_exists_proxy_lt_scaled_bernoulli N k m hm hmk hkhalf
  exact (optimalProxy_le _ D hproxy).trans_lt hD

end ExactHoeffding
