import ExactHoeffding.TwoDrawComparison
import ExactHoeffding.VarianceOptimality

namespace ExactHoeffding

/-- The exact normalized two-draw coefficient at an odd population `2*n+1`. -/
noncomputable def oddTwoDrawConstant (n : ℕ) : ℝ :=
  4/((2*(n:ℝ)-1)*Real.log (((n:ℝ)+1)/((n:ℝ)-1)))

/-- The exact singleton coefficient at an odd population `2*n+1`. -/
noncomputable def oddSingletonConstant (n : ℕ) : ℝ :=
  1/((n:ℝ)*Real.log (((n:ℝ)+1)/(n:ℝ)))

theorem twoDraw_centeredLog_eq (N k : ℕ) :
    hypergeomCenteredLogMGF N k 2=
      (fun t => Real.log (hypergeomMGF N k 2 t)-2*(k:ℝ)/(N:ℝ)*t) := by
  funext t
  unfold hypergeomCenteredLogMGF
  norm_num

theorem oddTwoDrawConstant_eq_normalized_proxy (n : ℕ) (hn : 2≤n) :
    oddTwoDrawConstant n=
      (2*(((2*n+1:ℕ):ℝ))/((((2*n+1:ℕ):ℝ))-2))*
        threeMassProxy (hypergeomMass (2*n+1) n 2 0) (hypergeomMass (2*n+1) n 2 2) := by
  rw [hypergeom_two_draw_odd_max_value n hn]
  unfold oddTwoDrawConstant
  push_cast
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hN : 2*(n:ℝ)+1≠0 := by linarith
  have hN2 : 2*(n:ℝ)-1≠0 := by linarith
  rw [show 2*(n:ℝ)+1-2=2*(n:ℝ)-1 by ring]
  generalize Real.log (((n:ℝ)+1)/((n:ℝ)-1))=L
  field_simp
  norm_num

/-- The exact two-draw maximum is strictly below the singleton constant,
including the smallest admissible population `N=5`. -/
theorem oddTwoDrawConstant_lt_singleton (n : ℕ) (hn : 2≤n) :
    oddTwoDrawConstant n<oddSingletonConstant n := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hN0 : (0:ℝ)<2*n+1 := by linarith
  have hN2 : (0:ℝ)<2*n-1 := by linarith
  have h := hypergeom_two_draw_bernoulli_envelope (2*n+1) n hn (by omega) (by omega)
  have hmul := mul_lt_mul_of_pos_left h
    (show 0<2*(((2*n+1:ℕ):ℝ))/((((2*n+1:ℕ):ℝ))-2) by
      push_cast
      exact div_pos (by positivity) (by linarith))
  rw [←oddTwoDrawConstant_eq_normalized_proxy n hn] at hmul
  apply lt_of_lt_of_eq hmul
  unfold oddSingletonConstant
  push_cast
  have hn0 : (n:ℝ)≠0 := by linarith
  have hN : 2*(n:ℝ)+1≠0 := ne_of_gt hN0
  have hN2' : 2*(n:ℝ)-1≠0 := ne_of_gt hN2
  have hN2'' : (-1:ℝ)+(n:ℝ)*2≠0 := by linarith
  have hratio : (1-(n:ℝ)/(2*n+1))/((n:ℝ)/(2*n+1))=((n:ℝ)+1)/n := by
    field_simp
    ring
  rw [hratio]
  have hL : Real.log (((n:ℝ)+1)/(n:ℝ))≠0 := ne_of_gt (Real.log_pos
    ((lt_div_iff₀ (by linarith : (0:ℝ)<n)).mpr (by linarith)))
  generalize Real.log (((n:ℝ)+1)/(n:ℝ))=L at hL ⊢
  field_simp
  ring_nf
  field_simp [hN2''] <;> ring

/-- In the usual `N` notation, the preceding comparison is exactly `L_N^(2)<L_N`. -/
theorem odd_two_draw_closed_strict (n : ℕ) (hn : 2≤n) :
    4/((2*(n:ℝ)-1)*Real.log ((2*(n:ℝ)+2)/(2*(n:ℝ)-2)))<
      2/((2*(n:ℝ))*Real.log ((2*(n:ℝ)+2)/(2*(n:ℝ)))) := by
  have h1 : (2*(n:ℝ)+2)/(2*(n:ℝ)-2)=((n:ℝ)+1)/((n:ℝ)-1) := by
    field_simp
  have h2 : (2*(n:ℝ)+2)/(2*(n:ℝ))=((n:ℝ)+1)/(n:ℝ) := by
    field_simp
  rw [h1,h2]
  have h := oddTwoDrawConstant_lt_singleton n hn
  unfold oddTwoDrawConstant oddSingletonConstant at h
  convert h using 1
  ring

/-- A single marked item gives a Bernoulli two-draw law with proxy at most `1/4`. -/
theorem hypergeom_two_draw_single_mark_proxy (N : ℕ) (hN : 3≤N) :
    IsQuadraticProxy (hypergeomCenteredLogMGF N 1 2) (1/4) := by
  have h : sharpCurvatureConstant N 1 2=(1:ℝ)/4 := by
    unfold sharpCurvatureConstant
    norm_num only [Nat.cast_one,Nat.cast_ofNat,one_mul]
    have hNR : (3:ℝ)≤N := by exact_mod_cast hN
    rw [min_eq_left (by linarith)]
    have hN1 : (N:ℝ)-1≠0 := by linarith
    field_simp
  intro t
  rw [←h]
  exact hypergeom_uniform_log_laplace_domination N 1 2 (by omega) (by omega) t

/-- The complementary endpoint law has the same quarter proxy. -/
theorem hypergeom_two_draw_single_failure_proxy (N : ℕ) (hN : 3≤N) :
    IsQuadraticProxy (hypergeomCenteredLogMGF N (N-1) 2) (1/4) := by
  have h : sharpCurvatureConstant N (N-1) 2=(1:ℝ)/4 := by
    rw [sharpCurvatureConstant_success_complement N 1 2 (by omega)]
    unfold sharpCurvatureConstant
    norm_num only [Nat.cast_one,Nat.cast_ofNat,one_mul]
    have hNR : (3:ℝ)≤N := by exact_mod_cast hN
    rw [min_eq_left (by linarith)]
    have hN1 : (N:ℝ)-1≠0 := by linarith
    field_simp
  intro t
  rw [←h]
  exact hypergeom_uniform_log_laplace_domination N (N-1) 2 (Nat.sub_le _ _) (by omega) t

theorem two_draw_endpoint_normalized_lt_one (N : ℝ) (hN : 4<N) :
    (2*N/(N-2))*(1/4:ℝ)<1 := by
  have hN2 : 0<N-2 := by linarith
  have heq : (2*N/(N-2))*(1/4:ℝ)=N/(2*(N-2)) := by field_simp; norm_num
  rw [heq]
  exact (div_lt_one (by positivity)).mpr (by linarith)

/-- The central two-draw proxy is at least its exact variance. -/
theorem odd_two_draw_central_variance_lower (n : ℕ) (hn : 2≤n) :
    (2*(n:ℝ)+2)/(2*(n:ℝ)+1)≤oddTwoDrawConstant n := by
  have hopt := hypergeom_two_draw_optimal_proxy (2*n+1) n hn (by omega)
  have hu : IsQuadraticProxy (hypergeomCenteredLogMGF (2*n+1) n 2)
      (threeMassProxy (hypergeomMass (2*n+1) n 2 0) (hypergeomMass (2*n+1) n 2 2)) := by
    rw [twoDraw_centeredLog_eq]
    exact hopt.1
  have hv := hypergeom_quadratic_proxy_ge_variance (2*n+1) n 2 (by omega) (by omega) _ hu
  rw [hypergeomTiltVariance_zero (2*n+1) n 2 (by omega) (by omega)] at hv
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hN2 : 0<2*(n:ℝ)-1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hv
    (show 0≤2*(((2*n+1:ℕ):ℝ))/((((2*n+1:ℕ):ℝ))-2) by
      push_cast
      exact div_nonneg (by positivity) (by linarith))
  rw [←oddTwoDrawConstant_eq_normalized_proxy n hn] at hmul
  convert hmul using 1 <;> try rfl
  rw [show 2*n+1-n=n+1 by omega,show 2*n+1-2=2*n-1 by omega]
  rw [Nat.cast_sub (show 1≤2*n by omega)]
  push_cast
  have hn0 : (n:ℝ)≠0 := by linarith
  have hN : 2*(n:ℝ)+1≠0 := by positivity
  have hN2' : 2*(n:ℝ)-1≠0 := ne_of_gt hN2
  have hN2'' : (-1:ℝ)+(n:ℝ)*2≠0 := by linarith
  field_simp
  ring_nf
  field_simp [hN2''] <;> ring

theorem one_lt_oddTwoDrawConstant (n : ℕ) (hn : 2≤n) : 1<oddTwoDrawConstant n := by
  have hv := odd_two_draw_central_variance_lower n hn
  have hN : 0<2*(n:ℝ)+1 := by positivity
  have hfrac : 1<(2*(n:ℝ)+2)/(2*(n:ℝ)+1) := (lt_div_iff₀ hN).mpr (by linarith)
  exact lt_of_lt_of_le hfrac hv

/-- Endpoint laws have a strictly smaller normalized proxy than either central law. -/
theorem odd_two_draw_endpoints_strictly_below (n : ℕ) (hn : 2≤n) :
    (2*(2*(n:ℝ)+1)/(2*(n:ℝ)-1))*(1/4:ℝ)<oddTwoDrawConstant n := by
  have hN : 4<2*(n:ℝ)+1 := by exact_mod_cast (show 4<2*n+1 by omega)
  have h := two_draw_endpoint_normalized_lt_one (2*(n:ℝ)+1) hN
  have he : 2*(n:ℝ)+1-2=2*(n:ℝ)-1 := by ring
  rw [he] at h
  exact lt_trans h (one_lt_oddTwoDrawConstant n hn)

theorem odd_two_draw_central_proxy_gt_quarter (n : ℕ) (hn : 2≤n) :
    (1:ℝ)/4<threeMassProxy (hypergeomMass (2*n+1) n 2 0)
      (hypergeomMass (2*n+1) n 2 2) := by
  have h := odd_two_draw_endpoints_strictly_below n hn
  rw [oddTwoDrawConstant_eq_normalized_proxy n hn] at h
  push_cast at h
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hp : 0<2*(2*(n:ℝ)+1)/(2*(n:ℝ)-1) := div_pos (by positivity) (by linarith)
  have heq : 2*(n:ℝ)+1-2=2*(n:ℝ)-1 := by ring
  rw [heq] at h
  exact (mul_lt_mul_iff_right₀ hp).mp h

theorem twoDraw_quadraticProxy_mono (ψ : ℝ→ℝ) (C D : ℝ)
    (hC : IsQuadraticProxy ψ C) (hCD : C≤D) : IsQuadraticProxy ψ D := by
  intro t
  exact le_trans (hC t) (by nlinarith [mul_nonneg (sub_nonneg.mpr hCD) (sq_nonneg t)])

/-- The central coefficient is a common proxy for every success count,
including both Bernoulli endpoint laws. -/
theorem odd_two_draw_all_success_upper (n k : ℕ)
    (hn : 2≤n) (hk : 1≤k) (hkN : k≤2*n) :
    IsQuadraticProxy (hypergeomCenteredLogMGF (2*n+1) k 2)
      (threeMassProxy (hypergeomMass (2*n+1) n 2 0) (hypergeomMass (2*n+1) n 2 2)) := by
  by_cases hk1 : k=1
  · subst k
    exact twoDraw_quadraticProxy_mono _ _ _
      (hypergeom_two_draw_single_mark_proxy (2*n+1) (by omega))
      (odd_two_draw_central_proxy_gt_quarter n hn).le
  by_cases hkcomp : k=2*n
  · subst k
    have h := hypergeom_two_draw_single_failure_proxy (2*n+1) (by omega)
    rw [show 2*n+1-1=2*n by omega] at h
    exact twoDraw_quadraticProxy_mono _ _ _ h (odd_two_draw_central_proxy_gt_quarter n hn).le
  have hki : 2≤k := by omega
  have hkNi : k+2≤2*n+1 := by omega
  have hopt := hypergeom_two_draw_optimal_proxy (2*n+1) k hki hkNi
  have hu : IsQuadraticProxy (hypergeomCenteredLogMGF (2*n+1) k 2)
      (threeMassProxy (hypergeomMass (2*n+1) k 2 0) (hypergeomMass (2*n+1) k 2 2)) := by
    rw [twoDraw_centeredLog_eq]
    exact hopt.1
  exact twoDraw_quadraticProxy_mono _ _ _ hu (hypergeom_two_draw_odd_max n k hn hki hkNi)

/-- The common coefficient over all success counts is itself least. -/
theorem odd_two_draw_all_success_least (n : ℕ) (hn : 2≤n) (D : ℝ)
    (hD : ∀k,1≤k → k≤2*n → IsQuadraticProxy (hypergeomCenteredLogMGF (2*n+1) k 2) D) :
    threeMassProxy (hypergeomMass (2*n+1) n 2 0) (hypergeomMass (2*n+1) n 2 2)≤D := by
  have hopt := hypergeom_two_draw_optimal_proxy (2*n+1) n hn (by omega)
  apply hopt.2 D
  have h := hD n (by omega) (by omega)
  rw [twoDraw_centeredLog_eq] at h
  exact h

/-- Exactly the two nearest-balanced success counts attain the common
optimal coefficient; the Bernoulli endpoints are strictly suboptimal. -/
theorem odd_two_draw_all_success_extremizers (n k : ℕ)
    (hn : 2≤n) (hk : 1≤k) (hkN : k≤2*n) :
    IsOptimalQuadraticProxy (hypergeomCenteredLogMGF (2*n+1) k 2)
      (threeMassProxy (hypergeomMass (2*n+1) n 2 0) (hypergeomMass (2*n+1) n 2 2))
      ↔ k=n ∨ k=n+1 := by
  constructor
  · intro hopt
    have hgt := odd_two_draw_central_proxy_gt_quarter n hn
    by_cases hk1 : k=1
    · subst k
      have hle := hopt.2 (1/4) (hypergeom_two_draw_single_mark_proxy (2*n+1) (by omega))
      exact False.elim (not_le_of_gt hgt hle)
    by_cases hkcomp : k=2*n
    · subst k
      have h := hypergeom_two_draw_single_failure_proxy (2*n+1) (by omega)
      rw [show 2*n+1-1=2*n by omega] at h
      have hle := hopt.2 (1/4) h
      exact False.elim (not_le_of_gt hgt hle)
    have hki : 2≤k := by omega
    have hkNi : k+2≤2*n+1 := by omega
    have hactual := hypergeom_two_draw_optimal_proxy (2*n+1) k hki hkNi
    have hu : IsQuadraticProxy (hypergeomCenteredLogMGF (2*n+1) k 2)
        (threeMassProxy (hypergeomMass (2*n+1) k 2 0) (hypergeomMass (2*n+1) k 2 2)) := by
      rw [twoDraw_centeredLog_eq]
      exact hactual.1
    have heq := le_antisymm (hypergeom_two_draw_odd_max n k hn hki hkNi) (hopt.2 _ hu)
    exact (hypergeom_two_draw_odd_max_iff n k hn hki hkNi).mp heq
  · intro hext
    have hki : 2≤k := by rcases hext with h|h <;> omega
    have hkNi : k+2≤2*n+1 := by rcases hext with h|h <;> omega
    have heq := (hypergeom_two_draw_odd_max_iff n k hn hki hkNi).mpr hext
    have h := hypergeom_two_draw_optimal_proxy (2*n+1) k hki hkNi
    rw [heq] at h
    rw [twoDraw_centeredLog_eq]
    exact h

end ExactHoeffding
