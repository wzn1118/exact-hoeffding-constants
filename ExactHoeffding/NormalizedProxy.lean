import ExactHoeffding.OptimalProxy

namespace ExactHoeffding
noncomputable section

def normalizedHypergeomProxy (N k m : ℕ) : ℝ :=
  4*(N:ℝ)/((m:ℝ)*((N:ℝ)-m))*hypergeomOptimalProxy N k m

theorem normalized_curvature_cancel (N m : ℝ)
    (hm : m≠0) (hNm : N-m≠0) (hN1 : N-1≠0) :
    (4*N/(m*(N-m)))*(m*(N-m)/(4*(N-1)))=N/(N-1) := by
  field_simp [hm,hNm,hN1]

theorem normalizedHypergeomProxy_universal_upper (N k m : ℕ)
    (hN : 2≤N) (hk : k≤N) (hm0 : 0<m) (hmN : m<N) :
    normalizedHypergeomProxy N k m≤(N:ℝ)/((N:ℝ)-1) := by
  have hNR : (2:ℝ)≤N := by exact_mod_cast hN
  have hmR : (0:ℝ)<m := by exact_mod_cast hm0
  have hmNR : (m:ℝ)<N := by exact_mod_cast hmN
  have hden : 0<(m:ℝ)*((N:ℝ)-m) := by positivity
  have hn1 : 0<(N:ℝ)-1 := by linarith
  have hmin : sharpCurvatureConstant N k m≤(m:ℝ)*((N:ℝ)-m)/(4*((N:ℝ)-1)) := by
    exact div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
  have h := mul_le_mul_of_nonneg_left
    ((hypergeomOptimalProxy_le_curvature N k m hk hmN.le).trans hmin)
    (show 0≤4*(N:ℝ)/((m:ℝ)*((N:ℝ)-m)) by positivity)
  have he := normalized_curvature_cancel (N:ℝ) (m:ℝ)
    hmR.ne' (sub_pos.mpr hmNR).ne' hn1.ne'
  exact h.trans_eq he

/-- The even normalized coefficient is attained by every nonconstant
sample margin when the marked margin is balanced. -/
theorem normalizedHypergeomProxy_even_attains (q m : ℕ)
    (hq : 0<q) (hm0 : 0<m) (hmN : m<2*q) :
    normalizedHypergeomProxy (2*q) q m=((2*q:ℕ):ℝ)/(((2*q:ℕ):ℝ)-1) := by
  unfold normalizedHypergeomProxy
  rw [hypergeomOptimalProxy_balanced_marks q m hq hmN.le]
  unfold sharpCurvatureConstant
  have hprod : (m:ℝ)*(((2*q:ℕ):ℝ)-m)≤(q:ℝ)*(((2*q:ℕ):ℝ)-q) := by
    push_cast
    nlinarith [sq_nonneg ((m:ℝ)-q)]
  rw [min_eq_right hprod]
  have hmR : (0:ℝ)<m := by exact_mod_cast hm0
  have hmNR : (m:ℝ)<((2*q:ℕ):ℝ) := by exact_mod_cast hmN
  have hqR : (1:ℝ)≤q := by exact_mod_cast hq
  have hn1 : ((2*q:ℕ):ℝ)-1≠0 := by push_cast; linarith
  exact normalized_curvature_cancel ((2*q:ℕ):ℝ) (m:ℝ) hmR.ne' (sub_pos.mpr hmNR).ne' hn1

theorem normalizedHypergeomProxy_success_complement (N k m : ℕ)
    (hk : k≤N) (hm : m≤N) (hN : 0<N) :
    normalizedHypergeomProxy N k m=normalizedHypergeomProxy N (N-k) m := by
  unfold normalizedHypergeomProxy
  rw [hypergeomOptimalProxy_success_complement N k m hk hm hN]

theorem normalizedHypergeomProxy_sample_complement (N k m : ℕ)
    (hk : k≤N) (hm : m≤N) (hN : 0<N) :
    normalizedHypergeomProxy N k m=normalizedHypergeomProxy N k (N-m) := by
  unfold normalizedHypergeomProxy
  rw [hypergeomOptimalProxy_sample_complement N k m hk hm hN,Nat.cast_sub hm]
  have he : ((N:ℝ)-m)*((N:ℝ)-((N:ℝ)-m))=(m:ℝ)*((N:ℝ)-m) := by ring
  rw [he]

theorem normalizedHypergeomProxy_transpose_ratio (N k m : ℕ)
    (hk0 : 0<k) (hkN : k<N) (hm0 : 0<m) (hmN : m<N) :
    normalizedHypergeomProxy N k m=
      ((k:ℝ)*((N:ℝ)-k)/((m:ℝ)*((N:ℝ)-m)))*normalizedHypergeomProxy N m k := by
  unfold normalizedHypergeomProxy
  rw [hypergeomOptimalProxy_transpose N k m hkN.le hmN.le]
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  have hkNR : (k:ℝ)<N := by exact_mod_cast hkN
  have hmR : (0:ℝ)<m := by exact_mod_cast hm0
  have hmNR : (m:ℝ)<N := by exact_mod_cast hmN
  field_simp [ne_of_gt hkR,ne_of_gt hmR,ne_of_gt (sub_pos.mpr hkNR),ne_of_gt (sub_pos.mpr hmNR)]

theorem normalizedHypergeomProxy_transpose_strict_ceiling (N k m : ℕ)
    (hk0 : 0<k) (hkm : k<m) (hmhalf : 2*m≤N) (C : ℝ)
    (hC : 0<C) (hbound : normalizedHypergeomProxy N m k≤C) :
    normalizedHypergeomProxy N k m<C := by
  have hm0 : 0<m := by omega
  have hkN : k<N := by omega
  have hmN : m<N := by omega
  rw [normalizedHypergeomProxy_transpose_ratio N k m hk0 hkN hm0 hmN]
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  have hkmR : (k:ℝ)<m := by exact_mod_cast hkm
  have hmNR : (m:ℝ)<N := by exact_mod_cast hmN
  have hhR : 2*(m:ℝ)≤N := by exact_mod_cast hmhalf
  have hden : 0<(m:ℝ)*((N:ℝ)-m) := by positivity
  have hratio : (k:ℝ)*((N:ℝ)-k)/((m:ℝ)*((N:ℝ)-m))<1 := by
    apply (div_lt_one hden).2
    have hp := mul_pos (sub_pos.mpr hkmR) (show 0<(N:ℝ)-k-m by linarith)
    nlinarith only [hp]
  have hr0 : 0≤(k:ℝ)*((N:ℝ)-k)/((m:ℝ)*((N:ℝ)-m)) := by
    apply div_nonneg _ hden.le
    apply mul_nonneg hkR.le
    linarith
  exact (mul_le_mul_of_nonneg_left hbound hr0).trans_lt (by nlinarith only [hratio,hC])

end
end ExactHoeffding
