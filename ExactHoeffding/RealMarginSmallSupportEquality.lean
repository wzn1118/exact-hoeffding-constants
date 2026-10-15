import ExactHoeffding.RealMarginRecurrenceLaw
import ExactHoeffding.RealMarginSmallSupport
import ExactHoeffding.RealRecurrenceEquality

/-! # Strict balanced proxy optimality for real one- and two-draw laws -/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

/-- Balance determines the variance at zero for every positive recurrence law,
including degrees one and two. -/
theorem RealRecurrenceLaw.variance_zero_balanced_positive (L : RealRecurrenceLaw)
    (hm : 0 < L.degree) (hbal : L.marks = (L.degree : ℝ) + L.remainder) :
    L.variance 0 = (L.degree : ℝ) * (L.marks + L.remainder) /
      (4 * (L.marks + L.degree + L.remainder - 1)) := by
  have hu := L.mean_zero_balanced hm hbal
  have hh := L.varianceDifferentialBalance 0
  simp only [Real.exp_zero, one_mul] at hh
  rw [hu] at hh
  rw [hbal] at hh ⊢
  have hmR : (1 : ℝ) ≤ L.degree := by exact_mod_cast hm
  have hr := L.remainder_nonneg
  have hT : (L.degree : ℝ) + L.remainder + L.degree + L.remainder - 1 ≠ 0 := by linarith
  apply (eq_div_iff (mul_ne_zero (by norm_num) hT)).mpr
  nlinarith only [hh]

/-- A one-draw recurrence has Bernoulli curvature at most one quarter. -/
theorem RealRecurrenceLaw.variance_le_quarter_of_degree_one (L : RealRecurrenceLaw)
    (hm : L.degree = 1) (t : ℝ) : L.variance t ≤ 1/4 := by
  have h := L.varianceAdmissible (by omega) t
  rw [hm] at h
  norm_num only [Nat.cast_one, div_one] at h
  nlinarith [sq_nonneg (L.mean t - 1/2)]

/-- At balance a one-draw curvature reaches its ceiling only at zero. -/
theorem RealRecurrenceLaw.variance_quarter_contact_one (L : RealRecurrenceLaw)
    (hm : L.degree = 1) (hbal : L.marks = (L.degree : ℝ) + L.remainder)
    (t : ℝ) (heq : L.variance t = 1/4) : t = 0 := by
  have h := L.varianceAdmissible (by omega) t
  rw [hm, heq] at h
  norm_num only [Nat.cast_one, div_one] at h
  have hu : L.mean t = 1/2 := by nlinarith [sq_nonneg (L.mean t - 1/2)]
  have hu0 := L.mean_zero_balanced (by omega) hbal
  rw [hm] at hu0
  norm_num only [Nat.cast_one] at hu0
  have hmono : StrictMono L.mean := strictMono_of_hasDerivAt_pos
    L.mean_hasDerivAt (L.variance_pos (by omega))
  exact hmono.injective (hu.trans hu0.symm)

/-- The real-margin rational variance is exactly its log-MGF curvature. -/
theorem realMarginRecurrenceLaw_second_deriv (m : ℕ) (N k t : ℝ)
    (hN : 0 < N) (hk : (m:ℝ) ≤ k) (hq : k+(m:ℝ) ≤ N) :
    deriv (deriv (fun u => Real.log (finiteMGF (Finset.range (m+1))
      (realMarginMass m (1/N) (k/N)) (fun i => (i:ℝ)) u))) t =
        (realMarginRecurrenceLaw m N k hN hk hq).variance t := by
  let L := realMarginRecurrenceLaw m N k hN hk hq
  have htotal : ∑ i ∈ Finset.range (m+1), realMarginMass m (1/N) (k/N) i = 1 :=
    L.mass_total
  have hnonneg : ∀ i ∈ Finset.range (m+1), 0 ≤ realMarginMass m (1/N) (k/N) i :=
    L.mass_nonneg
  rw [finiteLogMGF_second_deriv _ _ _ hnonneg htotal t]
  change (finiteTiltSecond (Finset.range (m+1)) L.mass (fun i => (i:ℝ)) t * L.mgf t -
    finiteTiltFirst (Finset.range (m+1)) L.mass (fun i => (i:ℝ)) t *
    finiteTiltFirst (Finset.range (m+1)) L.mass (fun i => (i:ℝ)) t) / L.mgf t ^ 2 =
    finiteTiltSecond (Finset.range (m+1)) L.mass (fun i => (i:ℝ)) t / L.mgf t -
    (finiteTiltFirst (Finset.range (m+1)) L.mass (fun i => (i:ℝ)) t / L.mgf t)^2
  field_simp

/-- The balanced two-draw curvature has a single contact at zero. -/
theorem realMarginRecurrenceLaw_two_contact (N t : ℝ) (hN : 5 ≤ N)
    (heq : (realMarginRecurrenceLaw 2 N (N/2) (by linarith)
      (by norm_num; linarith) (by norm_num; linarith)).variance t =
        (N-2)/(2*(N-1))) : t = 0 := by
  have hs := realMargin_two_curvature_equality_necessary N (N/2) t
    (by linarith) (by linarith) (by linarith)
  apply (hs ?_).2
  rw [realMarginRecurrenceLaw_second_deriv]
  exact heq


/-- Any true curvature bound with its sole zero-tilt contact gives the strict
centered quadratic envelope, without a restriction on the support size. -/
theorem RealRecurrenceLaw.centeredLogMGF_lt_variance_of_contact (L : RealRecurrenceLaw)
    (hv : ∀ s, L.variance s ≤ L.variance 0)
    (hc : ∀ s, L.variance s = L.variance 0 → s = 0)
    (t : ℝ) (ht : t ≠ 0) :
    L.centeredLogMGF t < L.variance 0 * t^2 / 2 := by
  exact strict_quadratic_envelope_of_curvature_single_contact _ 0
    L.centeredLogMGF_hasDerivAt (fun s => (L.mean_hasDerivAt s).sub_const _)
    hv hc L.centeredLogMGF_zero (sub_self _) t ht

theorem RealRecurrenceLaw.isOptimalQuadraticProxy_of_contact (L : RealRecurrenceLaw)
    (hv : ∀ s, L.variance s ≤ L.variance 0)
    (hc : ∀ s, L.variance s = L.variance 0 → s = 0) :
    IsOptimalQuadraticProxy L.centeredLogMGF (L.variance 0) := by
  refine ⟨?_, fun D hD => L.quadratic_proxy_ge_variance D hD⟩
  intro t
  by_cases ht : t = 0
  · subst t
    simp [L.centeredLogMGF_zero]
  · exact (L.centeredLogMGF_lt_variance_of_contact hv hc t ht).le

theorem RealRecurrenceLaw.proxyQuotient_unique_max_of_contact (L : RealRecurrenceLaw)
    (hv : ∀ s, L.variance s ≤ L.variance 0)
    (hc : ∀ s, L.variance s = L.variance 0 → s = 0) (t : ℝ) :
    IsMaxOn L.proxyQuotient univ t ↔ t = 0 := by
  have hstrict (s : ℝ) (hs : s ≠ 0) : L.proxyQuotient s < L.variance 0 := by
    simp only [RealRecurrenceLaw.proxyQuotient, if_neg hs]
    apply (div_lt_iff₀ (sq_pos_of_ne_zero hs)).mpr
    have h := L.centeredLogMGF_lt_variance_of_contact hv hc s hs
    nlinarith only [h]
  have hzero : L.proxyQuotient 0 = L.variance 0 := by
    simp [RealRecurrenceLaw.proxyQuotient]
  constructor
  · intro hmax
    by_contra ht
    have h0 : L.proxyQuotient 0 ≤ L.proxyQuotient t := hmax (mem_univ 0)
    rw [hzero] at h0
    exact (not_le_of_gt (hstrict t ht)) h0
  · rintro rfl
    intro s _
    change L.proxyQuotient s ≤ L.proxyQuotient 0
    rw [hzero]
    by_cases hs : s = 0
    · subst s; rw [hzero]
    · exact (hstrict s hs).le

/-- For every positive balanced real-margin law, small and large supports have
the same sole curvature contact. -/
theorem realMarginRecurrenceLaw_balanced_contact (m : ℕ) (N : ℝ)
    (hm : 0 < m) (hN : 5 ≤ N) (hfit : (m:ℝ) ≤ N/2) :
    let L := realMarginRecurrenceLaw m N (N/2) (by linarith) hfit (by linarith)
    (∀ t, L.variance t ≤ L.variance 0) ∧
      (∀ t, L.variance t = L.variance 0 → t = 0) := by
  let L := realMarginRecurrenceLaw m N (N/2) (by linarith) hfit (by linarith)
  change (∀ t, L.variance t ≤ L.variance 0) ∧
    (∀ t, L.variance t = L.variance 0 → t = 0)
  have hdeg : L.degree = m := rfl
  have hbal : L.marks = (L.degree : ℝ) + L.remainder := by
    dsimp [L, realMarginRecurrenceLaw]
    ring
  have hzero := L.variance_zero_balanced_positive (by simpa only [hdeg] using hm) hbal
  by_cases hm1 : m = 1
  · have hdegree : L.degree = 1 := hdeg.trans hm1
    have hC : L.variance 0 = 1/4 := by
      rw [hzero]
      dsimp [L, realMarginRecurrenceLaw]
      rw [hm1]
      norm_num
      field_simp [show N-1 ≠ 0 by linarith]
      ring
    constructor
    · intro t; rw [hC]
      exact L.variance_le_quarter_of_degree_one hdegree t
    · intro t ht
      exact L.variance_quarter_contact_one hdegree hbal t (ht.trans hC)
  by_cases hm2 : m = 2
  · have hC : L.variance 0 = (N-2)/(2*(N-1)) := by
      rw [hzero]
      dsimp [L, realMarginRecurrenceLaw]
      rw [hm2]
      norm_num
      field_simp [show (-4:ℝ)+N*4 ≠ 0 by linarith,
        show (-2:ℝ)+N*2 ≠ 0 by linarith]
      ring
    constructor
    · intro t; rw [hC]
      have hb := realMargin_two_curvature_le N (N/2) t
        (by linarith) (by linarith) (by linarith)
      rw [realMarginRecurrenceLaw_second_deriv] at hb
      simpa only [L, hm2] using hb
    · intro t ht
      apply realMarginRecurrenceLaw_two_contact N t hN
      simpa only [L, hm2] using ht.trans hC
  · have hm3 : 3 ≤ L.degree := by rw [hdeg]; omega
    constructor
    · intro t; rw [hzero]
      exact L.variance_sharp hm3 t
    · intro t ht
      exact (L.variance_sharp_equality_necessary hm3 t (ht.trans hzero)).2

/-- The strict balanced envelope for the actual real-margin masses, now with
no omitted degree-one or degree-two case. -/
theorem realMarginRecurrenceLaw_balanced_strict_quadratic (m : ℕ) (N : ℝ)
    (hm : 0 < m) (hN : 5 ≤ N) (hfit : (m:ℝ) ≤ N/2) (t : ℝ) (ht : t ≠ 0) :
    let L := realMarginRecurrenceLaw m N (N/2) (by linarith) hfit (by linarith)
    L.centeredLogMGF t < L.variance 0 * t^2 / 2 := by
  have hc := realMarginRecurrenceLaw_balanced_contact m N hm hN hfit
  exact RealRecurrenceLaw.centeredLogMGF_lt_variance_of_contact _ hc.1 hc.2 t ht

theorem realMarginRecurrenceLaw_balanced_isOptimal (m : ℕ) (N : ℝ)
    (hm : 0 < m) (hN : 5 ≤ N) (hfit : (m:ℝ) ≤ N/2) :
    let L := realMarginRecurrenceLaw m N (N/2) (by linarith) hfit (by linarith)
    IsOptimalQuadraticProxy L.centeredLogMGF (L.variance 0) := by
  have hc := realMarginRecurrenceLaw_balanced_contact m N hm hN hfit
  exact RealRecurrenceLaw.isOptimalQuadraticProxy_of_contact _ hc.1 hc.2

/-- The completed proxy of the actual balanced law is uniquely maximized at zero. -/
theorem realMarginRecurrenceLaw_balanced_unique_proxy_max (m : ℕ) (N : ℝ)
    (hm : 0 < m) (hN : 5 ≤ N) (hfit : (m:ℝ) ≤ N/2) (t : ℝ) :
    let L := realMarginRecurrenceLaw m N (N/2) (by linarith) hfit (by linarith)
    IsMaxOn L.proxyQuotient univ t ↔ t = 0 := by
  have hc := realMarginRecurrenceLaw_balanced_contact m N hm hN hfit
  exact RealRecurrenceLaw.proxyQuotient_unique_max_of_contact _ hc.1 hc.2 t


/-- The balanced zero-tilt variance in population coordinates. -/
theorem realMarginRecurrenceLaw_balanced_variance_zero (m : ℕ) (N : ℝ)
    (hm : 0 < m) (hN : 5 ≤ N) (hfit : (m:ℝ) ≤ N/2) :
    (realMarginRecurrenceLaw m N (N/2) (by linarith) hfit (by linarith)).variance 0 =
      (m:ℝ)*(N-m)/(4*(N-1)) := by
  let L := realMarginRecurrenceLaw m N (N/2) (by linarith) hfit (by linarith)
  have hbal : L.marks = (L.degree : ℝ) + L.remainder := by
    dsimp [L, realMarginRecurrenceLaw]
    ring
  have hz := L.variance_zero_balanced_positive hm hbal
  convert hz using 1
  dsimp [L, realMarginRecurrenceLaw]
  ring

/-- Exact identification of the recurrence-centered transform with the explicit
real-margin mass at success probability one half. -/
theorem realMarginRecurrenceLaw_balanced_centered_formula (m : ℕ) (N t : ℝ)
    (hm : 0 < m) (hN : 5 ≤ N) (hfit : (m:ℝ) ≤ N/2) :
    (realMarginRecurrenceLaw m N (N/2) (by linarith) hfit (by linarith)).centeredLogMGF t =
      Real.log (finiteMGF (Finset.range (m+1)) (realMarginMass m (1/N) (1/2))
        (fun i => (i:ℝ)) t) - ((m:ℝ)/2)*t := by
  let L := realMarginRecurrenceLaw m N (N/2) (by linarith) hfit (by linarith)
  have hbal : L.marks = (L.degree : ℝ) + L.remainder := by
    dsimp [L, realMarginRecurrenceLaw]
    ring
  change Real.log (L.mgf t) - L.mean 0*t = _
  rw [L.mean_zero_balanced hm hbal]
  dsimp [L, realMarginRecurrenceLaw, RealRecurrenceLaw.mgf]
  have hp : N/2/N = (1/2:ℝ) := by field_simp [show N ≠ 0 by linarith]
  rw [hp]

/-- The actual finite sum has the strict balanced quadratic envelope for every
positive sample size in the canonical domain. -/
theorem realMarginMass_balanced_strict_quadratic (m : ℕ) (N t : ℝ)
    (hm : 0 < m) (hN : 5 ≤ N) (hfit : (m:ℝ) ≤ N/2) (ht : t ≠ 0) :
    Real.log (finiteMGF (Finset.range (m+1)) (realMarginMass m (1/N) (1/2))
        (fun i => (i:ℝ)) t) - ((m:ℝ)/2)*t <
      ((m:ℝ)*(N-m)/(4*(N-1))) * t^2/2 := by
  have h := realMarginRecurrenceLaw_balanced_strict_quadratic m N hm hN hfit t ht
  dsimp only at h
  rw [realMarginRecurrenceLaw_balanced_centered_formula m N t hm hN hfit,
    realMarginRecurrenceLaw_balanced_variance_zero m N hm hN hfit] at h
  exact h


/-- Exact optimality stated solely in terms of the explicit balanced masses. -/
theorem realMarginMass_balanced_isOptimal (m : ℕ) (N : ℝ)
    (hm : 0 < m) (hN : 5 ≤ N) (hfit : (m:ℝ) ≤ N/2) :
    IsOptimalQuadraticProxy
      (fun t => Real.log (finiteMGF (Finset.range (m+1))
        (realMarginMass m (1/N) (1/2)) (fun i => (i:ℝ)) t) - ((m:ℝ)/2)*t)
      ((m:ℝ)*(N-m)/(4*(N-1))) := by
  let L := realMarginRecurrenceLaw m N (N/2) (by linarith) hfit (by linarith)
  have hfun : L.centeredLogMGF = (fun t => Real.log (finiteMGF (Finset.range (m+1))
      (realMarginMass m (1/N) (1/2)) (fun i => (i:ℝ)) t) - ((m:ℝ)/2)*t) := by
    funext t
    exact realMarginRecurrenceLaw_balanced_centered_formula m N t hm hN hfit
  have hh := realMarginRecurrenceLaw_balanced_isOptimal m N hm hN hfit
  change IsOptimalQuadraticProxy L.centeredLogMGF (L.variance 0) at hh
  rw [hfun, realMarginRecurrenceLaw_balanced_variance_zero m N hm hN hfit] at hh
  exact hh

end
end ExactHoeffding
