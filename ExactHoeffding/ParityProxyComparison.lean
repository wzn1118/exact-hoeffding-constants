import ExactHoeffding.TwoDrawComparison
import ExactHoeffding.NormalizedProxy

namespace ExactHoeffding
noncomputable section

def imbalanceFactor (d : ℝ) : ℝ := 2*d/logOdds d

def oddHypergeomConstant (N : ℕ) : ℝ :=
  2/(((N:ℝ)-1)*Real.log (((N:ℝ)+1)/((N:ℝ)-1)))

theorem imbalanceFactor_pos (d : ℝ) (hd : 0<d) (hd1 : d<1) : 0 < imbalanceFactor d := by
  unfold imbalanceFactor
  exact div_pos (by positivity) (logOdds_pos d hd hd1)

theorem imbalanceFactor_strictAnti : StrictAntiOn imbalanceFactor (Set.Ioo 0 1) := by
  intro x hx y hy hxy
  have h := logOdds_ratio_strictMono hx hy hxy
  have hxL := logOdds_pos x hx.1 hx.2
  have hyL := logOdds_pos y hy.1 hy.2
  have hh := (div_lt_div_iff₀ hx.1 hy.1).mp h
  unfold imbalanceFactor
  apply (div_lt_div_iff₀ hyL hxL).2
  nlinarith only [hh]

theorem logOdds_gt_twice (d : ℝ) (hd : 0<d) (hd1 : d<1) : 2*d<logOdds d := by
  have h := logOdds_strictConvex.lt_slope_of_hasDerivAt
    (show (0:ℝ)∈Set.Ico 0 1 by simp) (show d∈Set.Ico 0 1 from ⟨hd.le,hd1⟩)
    hd (logOdds_hasDerivAt 0 (by norm_num))
  have hz : logOdds 0=0 := by simp [logOdds]
  simp only [slope_def_field,hz,sub_zero,zero_pow (by decide : (2:ℕ)≠0),sub_zero,div_one] at h
  exact (lt_div_iff₀ hd).mp h

theorem imbalanceFactor_lt_one (d : ℝ) (hd : 0<d) (hd1 : d<1) : imbalanceFactor d<1 := by
  exact (div_lt_one (logOdds_pos d hd hd1)).2 (logOdds_gt_twice d hd hd1)

theorem logOdds_success_fraction (N k : ℝ) (hN : N≠0) (hk : k≠0) :
    logOdds (1-2*k/N)=Real.log ((1-k/N)/(k/N)) := by
  unfold logOdds
  congr 1
  field_simp [hN,hk] <;> ring

theorem oddHypergeomConstant_pos (N : ℕ) (hN : 1<N) : 0<oddHypergeomConstant N := by
  have hNR : (1:ℝ)<N := by exact_mod_cast hN
  have hfrac : 1<((N:ℝ)+1)/((N:ℝ)-1) := (one_lt_div (by linarith)).2 (by linarith)
  unfold oddHypergeomConstant
  exact div_pos (by norm_num) (mul_pos (by linarith) (Real.log_pos hfrac))

theorem oddHypergeomConstant_eq_artanh (N : ℕ) (hN : 1<N) :
    oddHypergeomConstant N=1/(((N:ℝ)-1)*Real.artanh (1/(N:ℝ))) := by
  have hNR : (1:ℝ)<N := by exact_mod_cast hN
  have hN0 : (N:ℝ)≠0 := by linarith
  have hN1 : (N:ℝ)-1≠0 := by linarith
  have hd : (1/(N:ℝ))∈Set.Icc (-1:ℝ) 1 := by
    constructor
    · have : 0<1/(N:ℝ) := by positivity
      linarith
    · exact (div_le_one (by linarith)).2 hNR.le
  rw [Real.artanh_eq_half_log hd]
  have he : (1+1/(N:ℝ))/(1-1/(N:ℝ))=((N:ℝ)+1)/((N:ℝ)-1) := by
    field_simp [hN0,hN1] <;> ring
  rw [he]
  unfold oddHypergeomConstant
  generalize Real.log (((N:ℝ)+1)/((N:ℝ)-1))=L
  field_simp

theorem oddHypergeomConstant_eq_factor (N : ℕ) (hN : 1<N) :
    (N:ℝ)/((N:ℝ)-1)*imbalanceFactor (1/(N:ℝ))=oddHypergeomConstant N := by
  have hNR : (1:ℝ)<N := by exact_mod_cast hN
  have hN0 : (N:ℝ)≠0 := by linarith
  have hN1 : (N:ℝ)-1≠0 := by linarith
  have he : (1+1/(N:ℝ))/(1-1/(N:ℝ))=((N:ℝ)+1)/((N:ℝ)-1) := by
    field_simp [hN0,hN1] <;> ring
  unfold imbalanceFactor logOdds oddHypergeomConstant
  rw [he]
  field_simp [hN0,hN1]

theorem oddHypergeomConstant_lt_even_bound (N : ℕ) (hN : 1<N) :
    oddHypergeomConstant N<(N:ℝ)/((N:ℝ)-1) := by
  rw [← oddHypergeomConstant_eq_factor N hN]
  have hNR : (1:ℝ)<N := by exact_mod_cast hN
  have h := imbalanceFactor_lt_one (1/(N:ℝ)) (by positivity)
    ((div_lt_one (by linarith)).2 hNR)
  have hscale : 0<(N:ℝ)/((N:ℝ)-1) := by positivity
  simpa only [mul_one] using mul_lt_mul_of_pos_left h hscale

theorem odd_imbalance_bound (n k : ℕ) (hn : 0<n) (hk : 0<k) (hkn : k≤n) :
    ((2*n+1:ℕ):ℝ)/(((2*n+1:ℕ):ℝ)-1)*
      imbalanceFactor (1-2*(k:ℝ)/((2*n+1:ℕ):ℝ))≤oddHypergeomConstant (2*n+1) := by
  let N : ℝ := ((2*n+1:ℕ):ℝ)
  have hNR : 1<N := by dsimp [N]; exact_mod_cast (show 1<2*n+1 by omega)
  have hkR : (0:ℝ)<k := by exact_mod_cast hk
  have hknR : 2*(k:ℝ)+1≤N := by dsimp [N]; exact_mod_cast (show 2*k+1≤2*n+1 by omega)
  have hlow : 0<1/N := by positivity
  have hlow1 : 1/N<1 := (div_lt_one (by linarith)).2 hNR
  have hd1 : 1-2*(k:ℝ)/N<1 := by have := div_pos (show 0<2*(k:ℝ) by positivity) (show 0<N by linarith); linarith
  have hd : 1/N≤1-2*(k:ℝ)/N := by
    apply (div_le_iff₀ (show 0<N by linarith)).2
    field_simp
    linarith
  have hfactor : imbalanceFactor (1-2*(k:ℝ)/N) ≤ imbalanceFactor (1/N) :=
    imbalanceFactor_strictAnti.antitoneOn ⟨hlow,hlow1⟩ ⟨hlow.trans_le hd,hd1⟩ hd
  have hmul := mul_le_mul_of_nonneg_left hfactor
    (show 0≤N/(N-1) by positivity)
  rw [oddHypergeomConstant_eq_factor (2*n+1) (by omega)] at hmul
  exact hmul

theorem odd_imbalance_bound_equality_iff (n k : ℕ) (hn : 0<n) (hk : 0<k) (hkn : k≤n) :
    ((2*n+1:ℕ):ℝ)/(((2*n+1:ℕ):ℝ)-1)*
      imbalanceFactor (1-2*(k:ℝ)/((2*n+1:ℕ):ℝ))=oddHypergeomConstant (2*n+1) ↔ k=n := by
  let N : ℝ := ((2*n+1:ℕ):ℝ)
  have hNR : 1<N := by dsimp [N]; exact_mod_cast (show 1<2*n+1 by omega)
  have hN0 : N≠0 := by linarith
  have hfactor : 0<N/(N-1) := by positivity
  have hcenter : 1-2*(n:ℝ)/N=1/N := by dsimp [N]; push_cast; field_simp; ring
  constructor
  · intro heq
    by_contra hne
    have hkn' : k<n := lt_of_le_of_ne hkn hne
    have hkR : (0:ℝ)<k := by exact_mod_cast hk
    have hknR : (k:ℝ)<n := by exact_mod_cast hkn'
    have hlow : 0<1/N := by positivity
    have hlow1 : 1/N<1 := (div_lt_one (by linarith)).2 hNR
    have hd1 : 1-2*(k:ℝ)/N<1 := by have h := div_pos (show 0<2*(k:ℝ) by positivity) (show 0<N by linarith); linarith
    have hstrict : 1/N<1-2*(k:ℝ)/N := by
      apply (div_lt_iff₀ (show 0<N by linarith)).2
      dsimp [N] at *
      push_cast at *
      field_simp
      linarith
    have h := mul_lt_mul_of_pos_left
      (imbalanceFactor_strictAnti ⟨hlow,hlow1⟩ ⟨hlow.trans hstrict,hd1⟩ hstrict) hfactor
    rw [oddHypergeomConstant_eq_factor (2*n+1) (by omega)] at h
    exact (ne_of_lt h) heq
  · intro heq
    subst k
    rw [hcenter]
    exact oddHypergeomConstant_eq_factor (2*n+1) (by omega)

end
end ExactHoeffding
