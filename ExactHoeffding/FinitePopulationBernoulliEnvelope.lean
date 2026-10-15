import ExactHoeffding.StrictHypergeometricProxy
import ExactHoeffding.TwoDrawComparison
import ExactHoeffding.BernoulliOptimal

namespace ExactHoeffding
noncomputable section

/-- Strict finite-population Bernoulli comparison includes the exact two-draw
law and every larger canonical sample size. -/
theorem hypergeom_proxy_lt_scaled_bernoulli_subhalf (N k m : ℕ)
    (hm : 2≤m) (hmk : m≤k) (hkhalf : 2*k<N) :
    hypergeomOptimalProxy N k m <
      envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) := by
  have hN : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hp : (k:ℝ)/(N:ℝ)<1/2 := by
    apply (div_lt_iff₀ hN).mpr
    have hh : 2*(k:ℝ)<N := by exact_mod_cast hkhalf
    linarith
  rw [bernoulliSharpBeta_eq_formula _ (ne_of_lt hp)]
  by_cases hm2 : m=2
  · subst m
    have hopt := hypergeom_two_draw_optimal_proxy N k hmk (by omega)
    have heq : hypergeomOptimalProxy N k 2 =
        threeMassProxy (hypergeomMass N k 2 0) (hypergeomMass N k 2 2) := by
      unfold hypergeomOptimalProxy
      exact optimalProxy_eq_of_optimal _ (hypergeomCenteredLogMGF_zero N k 2 (by omega) (by omega)) _
        (by convert! hopt using 1)
    rw [heq]
    simpa [envelopeM, mul_div_assoc] using
      hypergeom_two_draw_bernoulli_envelope N k hmk (by omega) hkhalf
  · have h := hypergeomOptimalProxy_lt_scaled_bernoulli N k m (by omega) hmk hkhalf
    simpa [mul_div_assoc] using h

/-- At a balanced success margin the comparison is exact for every sample. -/
theorem hypergeom_proxy_eq_scaled_bernoulli_balanced (N k m : ℕ)
    (hk0 : 0<k) (hbal : 2*k=N) (hm : m≤N) :
    hypergeomOptimalProxy N k m =
      envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) := by
  subst N
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  have hp : (k:ℝ)/((2*k:ℕ):ℝ)=1/2 := by
    push_cast
    field_simp
  rw [hp, bernoulliSharpBeta_half, hypergeomOptimalProxy_balanced_marks k m hk0 hm]
  unfold sharpCurvatureConstant envelopeM
  have horder : (m:ℝ)*(((2*k:ℕ):ℝ)-m) ≤ (k:ℝ)*(((2*k:ℕ):ℝ)-k) := by
    push_cast
    nlinarith [sq_nonneg ((m:ℝ)-k)]
  rw [min_eq_right horder]
  have hn : ((2*k:ℕ):ℝ)-1≠0 := by
    have hk1 : (1:ℝ)≤k := by exact_mod_cast hk0
    push_cast
    linarith
  field_simp [hn]
  <;> ring

/-- Finite-sample comparison with full success reflection. This directly
implies the compact-proportion comparison once both success margins exceed
any prescribed fixed sample size. -/
theorem hypergeom_proxy_le_scaled_bernoulli (N k m : ℕ)
    (hm : 2≤m) (hmk : m≤k) (hmNk : m≤N-k) :
    hypergeomOptimalProxy N k m ≤
      envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) := by
  have hk : k≤N := by omega
  have hmN : m≤N := by omega
  have hN : 0<N := by omega
  rcases lt_trichotomy (2*k) N with hlt | heq | hgt
  · exact (hypergeom_proxy_lt_scaled_bernoulli_subhalf N k m hm hmk hlt).le
  · exact (hypergeom_proxy_eq_scaled_bernoulli_balanced N k m (by omega) heq hmN).le
  · have h := hypergeom_proxy_lt_scaled_bernoulli_subhalf N (N-k) m hm hmNk (by omega)
    rw [hypergeomOptimalProxy_success_complement N k m hk hmN hN]
    have hp0 : 0<(k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0<k by omega))
      (by exact_mod_cast hN)
    have hp1 : (k:ℝ)/(N:ℝ)<1 := (div_lt_one (by exact_mod_cast hN)).mpr
      (by exact_mod_cast (show k<N by omega))
    have hpeq : ((N-k:ℕ):ℝ)/(N:ℝ) = 1-(k:ℝ)/(N:ℝ) := by
      rw [Nat.cast_sub hk]
      field_simp
    have hpne : (k:ℝ)/(N:ℝ)≠1/2 := by
      have hh : (N:ℝ)<2*(k:ℝ) := by exact_mod_cast hgt
      have hn : (0:ℝ)<N := by exact_mod_cast hN
      intro he
      have hc := (div_eq_iff hn.ne').mp he
      nlinarith
    rw [hpeq, bernoulliSharpBeta_reflection _ hp0 hp1 hpne] at h
    exact h.le

/-- Away from the balanced success margin the finite comparison is strict. -/
theorem hypergeom_proxy_lt_scaled_bernoulli (N k m : ℕ)
    (hm : 2≤m) (hmk : m≤k) (hmNk : m≤N-k) (hbal : 2*k≠N) :
    hypergeomOptimalProxy N k m <
      envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) := by
  by_cases hh : 2*k<N
  · exact hypergeom_proxy_lt_scaled_bernoulli_subhalf N k m hm hmk hh
  · have hk : k≤N := by omega
    have hmN : m≤N := by omega
    have hN : 0<N := by omega
    have h := hypergeom_proxy_lt_scaled_bernoulli_subhalf N (N-k) m hm hmNk (by omega)
    rw [hypergeomOptimalProxy_success_complement N k m hk hmN hN]
    have hnR : (0:ℝ)<N := by exact_mod_cast hN
    have hp0 : 0<(k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0<k by omega)) hnR
    have hp1 : (k:ℝ)/(N:ℝ)<1 := (div_lt_one hnR).mpr
      (by exact_mod_cast (show k<N by omega))
    have hpeq : ((N-k:ℕ):ℝ)/(N:ℝ) = 1-(k:ℝ)/(N:ℝ) := by
      rw [Nat.cast_sub hk]
      field_simp
    have hpne : (k:ℝ)/(N:ℝ)≠1/2 := by
      intro he
      have hc := (div_eq_iff hnR.ne').mp he
      have hhR : (N:ℝ)<2*(k:ℝ) := by exact_mod_cast (show N<2*k by omega)
      nlinarith
    rw [hpeq, bernoulliSharpBeta_reflection _ hp0 hp1 hpne] at h
    exact h

/-- The exact equality set for the finite-population Bernoulli comparison. -/
theorem hypergeom_proxy_scaled_bernoulli_equality_iff (N k m : ℕ)
    (hm : 2≤m) (hmk : m≤k) (hmNk : m≤N-k) :
    hypergeomOptimalProxy N k m =
      envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) ↔ 2*k=N := by
  constructor
  · intro he
    by_contra hb
    exact (ne_of_lt (hypergeom_proxy_lt_scaled_bernoulli N k m hm hmk hmNk hb)) he
  · intro hb
    exact hypergeom_proxy_eq_scaled_bernoulli_balanced N k m (by omega) hb (by omega)

/-- The compact-proportion comparison of the supplement, with all
nonbalanced cases strict, follows from the finite comparison. -/
theorem hypergeom_compact_bernoulli_envelope (m : ℕ) (hm : 2≤m)
    (η : ℝ) (hη : 0<η) (_hηhalf : η<1/2) :
    ∃ N₁ : ℕ, ∀ N k : ℕ, N₁≤N → η≤(k:ℝ)/N → (k:ℝ)/N≤1-η →
      hypergeomOptimalProxy N k m ≤
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) ∧
      (hypergeomOptimalProxy N k m =
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N) ↔ 2*k=N) ∧
      (2*k≠N → hypergeomOptimalProxy N k m <
        envelopeM (N:ℝ) (m:ℝ) * bernoulliSharpBeta ((k:ℝ)/N)) := by
  obtain ⟨B,hB⟩ := exists_nat_gt ((m:ℝ)/η)
  refine ⟨max B 1, ?_⟩
  intro N k hBN hlo hhi
  have hN : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hBNR : (B:ℝ)≤N := by exact_mod_cast (show B≤N by omega)
  have hlarge : (m:ℝ)<η*(N:ℝ) := by
    have hB' := (div_lt_iff₀ hη).mp hB
    nlinarith
  have hlow := (le_div_iff₀ hN).mp hlo
  have hhigh := (div_le_iff₀ hN).mp hhi
  have hmk : m≤k := by exact_mod_cast (show (m:ℝ)≤k by linarith)
  have hkN : k≤N := by exact_mod_cast (show (k:ℝ)≤N by nlinarith)
  have hmNk : m≤N-k := by
    have hmr : (m:ℝ)≤((N-k:ℕ):ℝ) := by
      rw [Nat.cast_sub hkN]
      nlinarith
    exact_mod_cast hmr
  exact ⟨hypergeom_proxy_le_scaled_bernoulli N k m hm hmk hmNk,
    hypergeom_proxy_scaled_bernoulli_equality_iff N k m hm hmk hmNk,
    hypergeom_proxy_lt_scaled_bernoulli N k m hm hmk hmNk⟩

end
end ExactHoeffding
