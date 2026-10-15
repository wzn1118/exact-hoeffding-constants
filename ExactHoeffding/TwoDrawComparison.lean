import ExactHoeffding.TwoDrawProxyComplete
import ExactHoeffding.ArtanhRatio

namespace ExactHoeffding

/-- Two logarithmic odds determine the asymmetric two-draw proxy. -/
noncomputable def twoDrawImbalanceProxy (c d : ℝ) : ℝ :=
  2*d/(logOdds d+logOdds (c*d))

theorem logOdds_pos (d : ℝ) (hd : 0<d) (hd1 : d<1) : 0<logOdds d := by
  unfold logOdds
  apply Real.log_pos
  apply (lt_div_iff₀ (by linarith : 0<1-d)).mpr
  linarith

/-- The strict finite-population Bernoulli envelope in imbalance coordinates. -/
theorem twoDrawImbalanceProxy_lt_bernoulli (c d : ℝ)
    (hc : 1<c) (hd : 0<d) (hcd : c*d<1) :
    twoDrawImbalanceProxy c d<2*d/((1+c)*logOdds d) := by
  have hd1 : d<1 := by nlinarith
  have hL := logOdds_pos d hd hd1
  have hR := logOdds_pos (c*d) (mul_pos (by linarith) hd) hcd
  have hscale := logOdds_scale_strict c d hc hd hcd
  unfold twoDrawImbalanceProxy
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have hgap : 0<2*d*(logOdds (c*d)-c*logOdds d) := by positivity
  nlinarith only [hgap]

/-- Increasing the success imbalance strictly decreases the exact two-draw proxy. -/
theorem twoDrawImbalanceProxy_strictAnti (c : ℝ) (hc : 1<c) :
    StrictAntiOn (twoDrawImbalanceProxy c) (Set.Ioo 0 (1/c)) := by
  intro d hd e he hde
  have hc0 : 0<c := by linarith
  have hd1 : d<1 := by
    have h1 : 1/c<1 := (div_lt_one hc0).mpr hc
    exact lt_trans hd.2 h1
  have he1 : e<1 := by
    have h1 : 1/c<1 := (div_lt_one hc0).mpr hc
    exact lt_trans he.2 h1
  have hcd0 : 0<c*d := mul_pos hc0 hd.1
  have hce0 : 0<c*e := mul_pos hc0 he.1
  have hcd1 : c*d<1 := by
    have h := (lt_div_iff₀ hc0).mp hd.2
    nlinarith
  have hce1 : c*e<1 := by
    have h := (lt_div_iff₀ hc0).mp he.2
    nlinarith
  have h1 := logOdds_ratio_strictMono ⟨hd.1,hd1⟩ ⟨he.1,he1⟩ hde
  have h2 := logOdds_ratio_strictMono ⟨hcd0,hcd1⟩ ⟨hce0,hce1⟩
    (mul_lt_mul_of_pos_left hde hc0)
  have h1' := (div_lt_div_iff₀ hd.1 he.1).mp h1
  have h2' := (div_lt_div_iff₀ hcd0 hce0).mp h2
  have h2'' : logOdds (c*d)*e<logOdds (c*e)*d := by
    apply (mul_lt_mul_iff_right₀ hc0).mp
    nlinarith only [h2']
  have hLd := logOdds_pos d hd.1 hd1
  have hLe := logOdds_pos e he.1 he1
  have hLcd := logOdds_pos (c*d) hcd0 hcd1
  have hLce := logOdds_pos (c*e) hce0 hce1
  unfold twoDrawImbalanceProxy
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [h1',h2'']

theorem hypergeom_two_draw_mass_difference (N k : ℕ)
    (hk : k≤N) (hN : 2≤N) :
    hypergeomMass N k 2 0-hypergeomMass N k 2 2=1-2*(k:ℝ)/(N:ℝ) := by
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast (show N≠0 by omega)
  have hN1 : (N:ℝ)-1≠0 := by
    have : (2:ℝ)≤N := by exact_mod_cast hN
    linarith
  rw [hypergeomMass_two_zero N k hk,hypergeomMass_two_two]
  field_simp
  ring

theorem hypergeom_two_draw_log_ratio (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) :
    Real.log (hypergeomMass N k 2 0/hypergeomMass N k 2 2)=
      logOdds (1-2*(k:ℝ)/(N:ℝ))+
      logOdds ((N:ℝ)/((N:ℝ)-2)*(1-2*(k:ℝ)/(N:ℝ))) := by
  have hkle : k≤N := by omega
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hNkR : (k:ℝ)+2≤N := by exact_mod_cast hNk
  have hN0 : (N:ℝ)≠0 := by linarith
  have hN1 : (N:ℝ)-1≠0 := by linarith
  have hN2 : (N:ℝ)-2≠0 := by linarith
  have hk0 : (k:ℝ)≠0 := by linarith
  have hk1 : (k:ℝ)-1≠0 := by linarith
  have h1 : (1+(1-2*(k:ℝ)/(N:ℝ)))/(1-(1-2*(k:ℝ)/(N:ℝ)))=
      ((N:ℝ)-k)/(k:ℝ) := by field_simp; ring
  have h2 : (1+(N:ℝ)/((N:ℝ)-2)*(1-2*(k:ℝ)/(N:ℝ)))/
      (1-(N:ℝ)/((N:ℝ)-2)*(1-2*(k:ℝ)/(N:ℝ)))=
      ((N:ℝ)-k-1)/((k:ℝ)-1) := by
    have hden : (-2:ℝ)+2*k≠0 := by linarith
    have hden1 : (-1:ℝ)+k≠0 := by linarith
    field_simp
    ring_nf
    field_simp [hden]
    ring_nf
  have hp1 : 0<((N:ℝ)-k)/(k:ℝ) := div_pos (by linarith) (by linarith)
  have hp2 : 0<((N:ℝ)-k-1)/((k:ℝ)-1) := div_pos (by linarith) (by linarith)
  rw [logOdds,logOdds,h1,h2,←Real.log_mul (ne_of_gt hp1) (ne_of_gt hp2)]
  congr 1
  rw [hypergeomMass_two_zero N k hkle,hypergeomMass_two_two]
  field_simp

/-- Identifying the exact least coefficient with its imbalance form. -/
theorem hypergeom_two_draw_proxy_eq_imbalance (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) (hhalf : 2*k<N) :
    threeMassProxy (hypergeomMass N k 2 0) (hypergeomMass N k 2 2)=
      twoDrawImbalanceProxy ((N:ℝ)/((N:ℝ)-2)) (1-2*(k:ℝ)/(N:ℝ)) := by
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hh : 2*(k:ℝ)<N := by exact_mod_cast hhalf
  have hN : 2≤N := by omega
  have hdiff := hypergeom_two_draw_mass_difference N k (by omega) hN
  have hpos : 0<1-2*(k:ℝ)/(N:ℝ) := by
    have hdiv : 2*(k:ℝ)/(N:ℝ)<1 := (div_lt_one (by linarith)).mpr hh
    linarith
  have hne : hypergeomMass N k 2 0≠hypergeomMass N k 2 2 := by
    intro heq
    rw [heq,sub_self] at hdiff
    linarith
  rw [threeMassProxy,if_neg hne,hdiff,hypergeom_two_draw_log_ratio N k hk hNk]
  rfl

/-- The strict two-draw finite-population Bernoulli envelope. -/
theorem hypergeom_two_draw_bernoulli_envelope (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) (hhalf : 2*k<N) :
    threeMassProxy (hypergeomMass N k 2 0) (hypergeomMass N k 2 2)<
      (2*((N:ℝ)-2)/((N:ℝ)-1))*
        ((1-2*(k:ℝ)/(N:ℝ))/(2*Real.log ((1-(k:ℝ)/(N:ℝ))/((k:ℝ)/(N:ℝ))))) := by
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hh : 2*(k:ℝ)<N := by exact_mod_cast hhalf
  have hN0 : (0:ℝ)<N := by linarith
  have hN2 : (0:ℝ)<(N:ℝ)-2 := by linarith
  have hc : 1<(N:ℝ)/((N:ℝ)-2) := (lt_div_iff₀ hN2).mpr (by linarith)
  have hd : 0<1-2*(k:ℝ)/(N:ℝ) := by
    have hdiv := (div_lt_one hN0).mpr hh
    linarith
  have hcd : (N:ℝ)/((N:ℝ)-2)*(1-2*(k:ℝ)/(N:ℝ))<1 := by
    have heq : (N:ℝ)/((N:ℝ)-2)*(1-2*(k:ℝ)/(N:ℝ))=
        ((N:ℝ)-2*k)/((N:ℝ)-2) := by field_simp
    rw [heq]
    apply (div_lt_one hN2).mpr
    linarith
  rw [hypergeom_two_draw_proxy_eq_imbalance N k hk hNk hhalf]
  have h := twoDrawImbalanceProxy_lt_bernoulli ((N:ℝ)/((N:ℝ)-2))
    (1-2*(k:ℝ)/(N:ℝ)) hc hd hcd
  have hlog : logOdds (1-2*(k:ℝ)/(N:ℝ))=
      Real.log ((1-(k:ℝ)/(N:ℝ))/((k:ℝ)/(N:ℝ))) := by
    unfold logOdds
    congr 1
    field_simp
    ring
  rw [hlog] at h
  convert h using 1
  have hN1 : (N:ℝ)-1≠0 := by linarith
  have hL : Real.log ((1-(k:ℝ)/(N:ℝ))/((k:ℝ)/(N:ℝ)))≠0 := by
    rw [←hlog]
    exact ne_of_gt (logOdds_pos _ hd (by nlinarith))
  generalize Real.log ((1-(k:ℝ)/(N:ℝ))/((k:ℝ)/(N:ℝ)))=L at hL ⊢
  field_simp [hL,hN1]
  ring

/-- Increasing the success count below half increases the exact two-draw proxy. -/
theorem hypergeom_two_draw_proxy_strictMono_below_half (N k l : ℕ)
    (hk : 2≤k) (hkl : k<l) (hlhalf : 2*l<N) :
    threeMassProxy (hypergeomMass N k 2 0) (hypergeomMass N k 2 2)<
      threeMassProxy (hypergeomMass N l 2 0) (hypergeomMass N l 2 2) := by
  have hNk : k+2≤N := by omega
  have hNl : l+2≤N := by omega
  have hl : 2≤l := by omega
  have hkhalf : 2*k<N := by omega
  have hkR : (2:ℝ)≤k := by exact_mod_cast hk
  have hlR : (2:ℝ)≤l := by exact_mod_cast hl
  have hklR : (k:ℝ)<l := by exact_mod_cast hkl
  have hhalfR : 2*(l:ℝ)<N := by exact_mod_cast hlhalf
  have hN0 : (0:ℝ)<N := by linarith
  have hN2 : (0:ℝ)<(N:ℝ)-2 := by linarith
  have hc : 1<(N:ℝ)/((N:ℝ)-2) := (lt_div_iff₀ hN2).mpr (by linarith)
  have hmem (j : ℕ) (hj : (2:ℝ)≤j) (hjhalf : 2*(j:ℝ)<N) :
      1-2*(j:ℝ)/(N:ℝ)∈Set.Ioo 0 (1/((N:ℝ)/((N:ℝ)-2))) := by
    constructor
    · have h := (div_lt_one hN0).mpr hjhalf
      linarith
    · rw [one_div_div]
      have heq : 1-2*(j:ℝ)/(N:ℝ)=((N:ℝ)-2*j)/(N:ℝ) := by field_simp
      rw [heq]
      apply (div_lt_div_iff_of_pos_right hN0).mpr
      linarith
  rw [hypergeom_two_draw_proxy_eq_imbalance N k hk hNk hkhalf,
    hypergeom_two_draw_proxy_eq_imbalance N l hl hNl hlhalf]
  apply twoDrawImbalanceProxy_strictAnti _ hc (hmem l hlR hhalfR)
    (hmem k hkR (by linarith))
  have h := (div_lt_div_iff_of_pos_right hN0).mpr (by linarith : 2*(k:ℝ)<2*l)
  linarith

/-- For an odd population, the nearest lower balanced count maximizes the
two-draw proxy among all nondegenerate success counts on the lower side. -/
theorem hypergeom_two_draw_odd_lower_max (n k : ℕ)
    (_hn : 2≤n) (hk : 2≤k) (hkn : k≤n) :
    threeMassProxy (hypergeomMass (2*n+1) k 2 0) (hypergeomMass (2*n+1) k 2 2)≤
      threeMassProxy (hypergeomMass (2*n+1) n 2 0) (hypergeomMass (2*n+1) n 2 2) := by
  rcases hkn.eq_or_lt with heq | hlt
  · subst k; rfl
  · exact le_of_lt (hypergeom_two_draw_proxy_strictMono_below_half (2*n+1) k n hk hlt (by omega))

theorem threeMassProxy_symmetric (p0 p2 : ℝ) (hp0 : 0<p0) (hp2 : 0<p2) :
    threeMassProxy p0 p2=threeMassProxy p2 p0 := by
  by_cases heq : p0=p2
  · subst p2; rfl
  · rw [threeMassProxy,threeMassProxy,if_neg heq,if_neg (Ne.symm heq)]
    exact (threeMass_proxy_ratio_reflection p0 p2 hp0 hp2).symm

/-- Complementing success marks leaves the actual two-draw optimal proxy invariant. -/
theorem hypergeom_two_draw_proxy_complement (N k : ℕ)
    (hk : 2≤k) (hNk : k+2≤N) :
    threeMassProxy (hypergeomMass N (N-k) 2 0) (hypergeomMass N (N-k) 2 2)=
      threeMassProxy (hypergeomMass N k 2 0) (hypergeomMass N k 2 2) := by
  have hkle : k≤N := by omega
  have hcle : N-k≤N := Nat.sub_le N k
  have h0 : hypergeomMass N (N-k) 2 0=hypergeomMass N k 2 2 := by
    rw [hypergeomMass_two_zero N (N-k) hcle,hypergeomMass_two_two,Nat.cast_sub hkle]
    congr 1
    ring
  have h2 : hypergeomMass N (N-k) 2 2=hypergeomMass N k 2 0 := by
    rw [hypergeomMass_two_zero N k hkle,hypergeomMass_two_two,Nat.cast_sub hkle]
  rw [h0,h2]
  obtain ⟨hp0,_,hp2,_⟩ := hypergeom_two_draw_threeMass_admissible N k hk hNk
  exact threeMassProxy_symmetric _ _ hp2 hp0

/-- The exact two-draw proxy on every three-point law for an odd population
is maximized by the nearest-balanced success counts. -/
theorem hypergeom_two_draw_odd_max (n k : ℕ)
    (hn : 2≤n) (hk : 2≤k) (hNk : k+2≤2*n+1) :
    threeMassProxy (hypergeomMass (2*n+1) k 2 0) (hypergeomMass (2*n+1) k 2 2)≤
      threeMassProxy (hypergeomMass (2*n+1) n 2 0) (hypergeomMass (2*n+1) n 2 2) := by
  by_cases hkn : k≤n
  · exact hypergeom_two_draw_odd_lower_max n k hn hk hkn
  · rw [←hypergeom_two_draw_proxy_complement (2*n+1) k hk hNk]
    exact hypergeom_two_draw_odd_lower_max n (2*n+1-k) hn (by omega) (by omega)

theorem hypergeom_two_draw_odd_max_iff (n k : ℕ)
    (hn : 2≤n) (hk : 2≤k) (hNk : k+2≤2*n+1) :
    threeMassProxy (hypergeomMass (2*n+1) k 2 0) (hypergeomMass (2*n+1) k 2 2)=
      threeMassProxy (hypergeomMass (2*n+1) n 2 0) (hypergeomMass (2*n+1) n 2 2)
      ↔ k=n ∨ k=n+1 := by
  constructor
  · intro heq
    by_cases hkn : k≤n
    · by_cases hke : k=n
      · exact Or.inl hke
      · have hlt := hypergeom_two_draw_proxy_strictMono_below_half (2*n+1) k n hk
          (by omega) (by omega)
        rw [heq] at hlt
        exact False.elim (lt_irrefl _ hlt)
    · by_cases hke : k=n+1
      · exact Or.inr hke
      · have hc : 2*n+1-k<n := by omega
        have hlt := hypergeom_two_draw_proxy_strictMono_below_half (2*n+1) (2*n+1-k) n
          (by omega) hc (by omega)
        rw [hypergeom_two_draw_proxy_complement (2*n+1) k hk hNk,heq] at hlt
        exact False.elim (lt_irrefl _ hlt)
  · rintro (rfl | rfl)
    · rfl
    · rw [←hypergeom_two_draw_proxy_complement (2*n+1) (n+1) (by omega) (by omega)]
      congr 3 <;> omega

/-- Closed value at the nearest-balanced count of an odd population. -/
theorem hypergeom_two_draw_odd_max_value (n : ℕ) (hn : 2≤n) :
    threeMassProxy (hypergeomMass (2*n+1) n 2 0) (hypergeomMass (2*n+1) n 2 2)=
      2/(((2*n+1:ℕ):ℝ)*Real.log (((n:ℝ)+1)/((n:ℝ)-1))) := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (n:ℝ)≠0 := by linarith
  have hn1 : (n:ℝ)-1≠0 := by linarith
  have hN0 : (((2*n+1:ℕ):ℝ))≠0 := by positivity
  have hN1 : (((2*n+1:ℕ):ℝ))-1≠0 := by
    push_cast
    linarith
  have h0 := hypergeomMass_two_zero (2*n+1) n (by omega)
  have h2 := hypergeomMass_two_two (2*n+1) n
  have hdiff : hypergeomMass (2*n+1) n 2 0-hypergeomMass (2*n+1) n 2 2=
      1/(((2*n+1:ℕ):ℝ)) := by
    rw [hypergeom_two_draw_mass_difference (2*n+1) n (by omega) (by omega)]
    push_cast
    field_simp
    ring
  have hne : hypergeomMass (2*n+1) n 2 0≠hypergeomMass (2*n+1) n 2 2 := by
    intro heq
    rw [heq,sub_self] at hdiff
    exact (one_div_ne_zero hN0) hdiff.symm
  have hratio : hypergeomMass (2*n+1) n 2 0/hypergeomMass (2*n+1) n 2 2=
      ((n:ℝ)+1)/((n:ℝ)-1) := by
    rw [h0,h2]
    push_cast
    field_simp
    ring
  rw [threeMassProxy,if_neg hne,hdiff,hratio]
  ring

end ExactHoeffding
