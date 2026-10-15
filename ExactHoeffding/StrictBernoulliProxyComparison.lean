import ExactHoeffding.ArtanhRatio
import ExactHoeffding.ProxyQuotient
import ExactHoeffding.StrictGlobalGap

open Set

namespace ExactHoeffding

/-- The ordinary Bernoulli variance is strictly smaller than its sharp
quadratic proxy away from balance. This sub-half version uses strict convexity
of the log-odds function, independently of the Bernoulli global proxy proof. -/
theorem bernoulli_variance_lt_sharp_proxy_subhalf (p : ℝ)
    (hp0 : 0<p) (hp : p<1/2) :
    p*(1-p)<(1-2*p)/(2*Real.log ((1-p)/p)) := by
  let d := 1-2*p
  have hd0 : 0<d := by dsimp [d]; linarith
  have hd1 : d<1 := by dsimp [d]; linarith
  have hden : 0<1-d^2 := by nlinarith
  have hp1 : p<1 := by linarith
  have hratio : 1<(1-p)/p := (one_lt_div hp0).mpr (by linarith)
  have hlog : 0<Real.log ((1-p)/p) := Real.log_pos hratio
  have hlogOdds : logOdds d=Real.log ((1-p)/p) := by
    unfold logOdds
    congr 1
    dsimp [d]
    field_simp [hp0.ne']
    ring
  have hs := logOdds_strictConvex.slope_lt_of_hasDerivAt
    (show (0:ℝ)∈Ico 0 1 by simp) (show d∈Ico 0 1 from ⟨hd0.le,hd1⟩)
    hd0 (logOdds_hasDerivAt d ⟨by linarith,hd1⟩)
  have hzero : logOdds 0=0 := by simp [logOdds]
  rw [slope_def_field,hzero,sub_zero,sub_zero,hlogOdds] at hs
  have hcross := (div_lt_div_iff₀ hd0 hden).mp hs
  apply (lt_div_iff₀ (by positivity : 0<2*Real.log ((1-p)/p))).mpr
  dsimp [d] at hcross ⊢
  nlinarith only [hcross]

theorem bernoulli_sharp_proxy_pos_subhalf (p : ℝ)
    (hp0 : 0<p) (hp : p<1/2) :
    0<(1-2*p)/(2*Real.log ((1-p)/p)) := by
  have h := bernoulli_variance_lt_sharp_proxy_subhalf p hp0 hp
  have hvar : 0<p*(1-p) := mul_pos hp0 (by linarith)
  exact hvar.trans h

theorem hypergeomTiltVariance_zero_eq_scaled_bernoulli_variance
    (N k m : ℕ) (hN : 1<N) (hk : k≤N) (hm : m≤N) :
    hypergeomTiltVariance N k m 0=
      envelopeM (N:ℝ) (m:ℝ)*((k:ℝ)/N)*(1-(k:ℝ)/N) := by
  rw [hypergeomTiltVariance_zero N k m hk hm,Nat.cast_sub hk,Nat.cast_sub hm]
  unfold envelopeM
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hN1 : (N:ℝ)-1≠0 := by
    have hn : (1:ℝ)<N := by exact_mod_cast hN
    linarith
  field_simp [hN0,hN1]

/-- At zero tilt the actual extended proxy quotient lies strictly below the
finite-population-scaled Bernoulli proxy throughout the sub-half domain. -/
theorem hypergeomProxyQuotient_zero_lt_scaled_bernoulli_proxy
    (N k m : ℕ) (hm : 3≤m) (hmk : m≤k) (hkhalf : 2*k<N) :
    hypergeomProxyQuotient N k m 0<
      envelopeM (N:ℝ) (m:ℝ)*
        ((1-2*((k:ℝ)/N))/(2*Real.log ((1-(k:ℝ)/N)/((k:ℝ)/N)))) := by
  have hNm : (3:ℝ)≤m := by exact_mod_cast hm
  have hmkR : (m:ℝ)≤k := by exact_mod_cast hmk
  have hkhalfR : 2*(k:ℝ)<N := by exact_mod_cast hkhalf
  have hN : (0:ℝ)<N := by linarith
  have hp0 : 0<(k:ℝ)/N := div_pos (by linarith) hN
  have hp : (k:ℝ)/N<1/2 := (div_lt_iff₀ hN).mpr (by linarith)
  have hM : 0<envelopeM (N:ℝ) (m:ℝ) :=
    envelopeM_positive (N:ℝ) (m:ℝ) hNm (by linarith)
  unfold hypergeomProxyQuotient
  rw [Function.update_self,
    hypergeomTiltVariance_zero_eq_scaled_bernoulli_variance N k m (by omega) (by omega) (by omega)]
  have h := mul_lt_mul_of_pos_left (bernoulli_variance_lt_sharp_proxy_subhalf
    ((k:ℝ)/N) hp0 hp) hM
  simpa only [mul_assoc] using h

theorem scaled_bernoulli_proxy_pos_of_margins
    (N k m : ℕ) (hm : 3≤m) (hmk : m≤k) (hkhalf : 2*k<N) :
    0<envelopeM (N:ℝ) (m:ℝ)*
      ((1-2*((k:ℝ)/N))/(2*Real.log ((1-(k:ℝ)/N)/((k:ℝ)/N)))) := by
  have hmR : (3:ℝ)≤m := by exact_mod_cast hm
  have hmkR : (m:ℝ)≤k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ)<N := by exact_mod_cast hkhalf
  have hN : (0:ℝ)<N := by linarith
  exact mul_pos (envelopeM_positive (N:ℝ) (m:ℝ) hmR (by linarith))
    (bernoulli_sharp_proxy_pos_subhalf ((k:ℝ)/N) (div_pos (by linarith) hN)
      ((div_lt_iff₀ hN).mpr (by linarith)))

/-- Compactness converts a strict ceiling for the actual continuous proxy
quotient into a strictly smaller valid quadratic proxy. -/
theorem hypergeom_exists_proxy_below_of_quotient_strict (k m r : ℕ)
    (hmk : m≤k) (hm : 0<m) (C : ℝ) (hC : 0<C)
    (hstrict : ∀t, hypergeomProxyQuotient (k+m+r) k m t<C) :
    ∃D<C, IsQuadraticProxy (hypergeomCenteredLogMGF (k+m+r) k m) D := by
  obtain ⟨D,hD,hbound⟩ := exists_uniform_strict_ceiling
    (hypergeomProxyQuotient_continuous (k+m+r) k m (by omega) (by omega)) hC
    (hypergeomProxyQuotient_tendsto_atBot k m r hmk hm)
    (hypergeomProxyQuotient_tendsto_atTop k m r hmk hm) hstrict
  refine ⟨D,hD,?_⟩
  intro t
  by_cases ht : t=0
  · subst t
    simp [hypergeomCenteredLogMGF_zero (k+m+r) k m (by omega) (by omega)]
  · have h := hbound t
    unfold hypergeomProxyQuotient at h
    rw [Function.update_of_ne ht] at h
    have hmul := (div_le_iff₀ (sq_pos_of_ne_zero ht)).mp h
    linarith


end ExactHoeffding
