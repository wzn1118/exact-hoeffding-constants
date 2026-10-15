import ExactHoeffding.RealRecurrenceCurvature
import ExactHoeffding.StationaryEquality
import ExactHoeffding.OptimalProxy
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

/-- The untilted mean follows directly from adjacent-mass balance. -/
theorem RealRecurrenceLaw.mean_zero (L : RealRecurrenceLaw) (hm : 0 < L.degree) :
    L.mean 0 = (L.degree : ℝ) * L.marks /
      (L.marks + L.degree + L.remainder) := by
  have hmR : (0 : ℝ) < L.degree := by exact_mod_cast hm
  have hmk := L.marks_ge
  have hr := L.remainder_nonneg
  have hN : L.marks + L.degree + L.remainder ≠ 0 := by linarith
  have hh := L.meanVarianceBalance 0
  simp only [Real.exp_zero, one_mul] at hh
  apply (eq_div_iff hN).mpr
  nlinarith only [hh]

/-- Balance makes the ordinary mean the midpoint of the actual support. -/
theorem RealRecurrenceLaw.mean_zero_balanced (L : RealRecurrenceLaw)
    (hm : 0 < L.degree) (hbal : L.marks = (L.degree : ℝ) + L.remainder) :
    L.mean 0 = (L.degree : ℝ) / 2 := by
  rw [L.mean_zero hm, hbal]
  have hmR : (0 : ℝ) < L.degree := by exact_mod_cast hm
  have hr := L.remainder_nonneg
  have hN : (L.degree : ℝ) + L.remainder + L.degree + L.remainder ≠ 0 := by linarith
  apply (div_eq_iff hN).mpr
  ring

/-- Equality in the sharp ceiling forces balance and zero tilt for every
positive real-parameter recurrence law of degree at least three. -/
theorem RealRecurrenceLaw.variance_sharp_equality_necessary (L : RealRecurrenceLaw)
    (hm : 3 ≤ L.degree) (t : ℝ)
    (heq : L.variance t = (L.degree : ℝ) * (L.marks + L.remainder) /
      (4 * (L.marks + L.degree + L.remainder - 1))) :
    L.marks = (L.degree : ℝ) + L.remainder ∧ t = 0 := by
  let u := L.mean t
  let v := L.variance t
  let T : ℝ := L.marks + L.degree + L.remainder - 1
  let A : ℝ := L.marks + L.remainder - 1
  let B : ℝ := (L.degree : ℝ) * (L.marks + L.remainder) / (4 * T)
  have hm3 : (3 : ℝ) ≤ L.degree := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < L.degree := by linarith
  have hmkR := L.marks_ge
  have hr0 := L.remainder_nonneg
  have hT : 0 < T := by dsimp [T]; linarith
  have hA : (L.degree : ℝ) - 1 ≤ A := by dsimp [A]; linarith
  have heqB : v = B := heq
  have hlocal : IsLocalMax L.variance t := by
    have hmax : IsMaxOn L.variance univ t := by
      intro s _
      rw [heq]
      exact L.variance_sharp hm s
    exact hmax.isLocalMax (by simp)
  have hw : deriv L.variance t = 0 := hlocal.deriv_eq_zero
  have hbal := L.meanVarianceBalance t
  have hstat := L.varianceStationaryBalance t hw
  have hpoly : stationaryPolynomial (L.degree : ℝ) L.marks L.remainder u v = 0 := by
    apply stationary_elimination (L.degree : ℝ) L.marks L.remainder u v (Real.exp t)
    · dsimp [u,v] at *
      nlinarith only [hbal]
    · dsimp only at hstat
      unfold stationaryDen
      convert hstat using 1
      ring
  have hstrictPB := L.varianceAdmissibleStrict (by omega) t
  change v < u * ((L.degree : ℝ) - u) / L.degree at hstrictPB
  rw [heqB] at hstrictPB
  have hstrict : B * (L.degree : ℝ) < u * ((L.degree : ℝ) - u) :=
    (lt_div_iff₀ hmpos).mp hstrictPB
  have hBT : B * (4 * T) = (L.degree : ℝ) * (L.marks + L.remainder) := by
    dsimp [B]
    field_simp [hT.ne']
  have hp := mul_pos (sub_pos.mpr hstrict) (mul_pos (by norm_num : (0 : ℝ) < 4) hT)
  have hBTm := congrArg (fun z : ℝ => z * (L.degree : ℝ)) hBT
  have hpositive : 0 < (L.degree : ℝ)^2 * ((L.degree : ℝ) - 1) -
      (A + L.degree) * (2 * u - L.degree)^2 := by
    dsimp [T,A] at hp hBTm ⊢
    nlinarith only [hp,hBTm]
  have hD : |L.marks - L.degree - L.remainder| ≤ A - L.degree + 1 := by
    apply abs_le.mpr
    dsimp [A]
    constructor <;> linarith
  have hTform : 2 * (L.degree : ℝ) + (L.marks - L.degree) + L.remainder - 1 = T := by
    dsimp [T]
    ring
  have hmform : (L.degree : ℝ) + (L.marks - L.degree) = L.marks := by ring
  have huform : ((L.degree : ℝ) + (2 * u - L.degree)) / 2 = u := by ring
  have hid := stationary_main_identity (L.degree : ℝ) (L.marks - L.degree)
    L.remainder (2 * u - L.degree) (by rw [hTform]; exact hT.ne')
  rw [hTform,hmform,huform] at hid
  change -16 * T * stationaryPolynomial (L.degree : ℝ) L.marks L.remainder u B = _ at hid
  rw [← heqB,hpoly,mul_zero] at hid
  have hQ : ((L.degree : ℝ)^2 * ((L.degree : ℝ) - 1) -
        (A + L.degree) * (2 * u - L.degree)^2) *
      ((L.marks - L.degree - L.remainder) - (2 * u - L.degree))^2 +
      (A + 1) * (2 * (L.degree : ℝ) * (L.marks - L.degree - L.remainder) *
        (2 * u - L.degree) + (A * (A + 1) - 2 * L.degree) *
          (2 * u - L.degree)^2) = 0 := by
    dsimp [A,T] at hid ⊢
    nlinarith only [hid]
  have hzeros := (universal_stationary_comparison_eq_zero_iff
    (L.degree : ℝ) A (L.marks - L.degree - L.remainder) (2 * u - L.degree)
      hm3 hA hD hpositive).mp hQ
  have hbalance : L.marks = (L.degree : ℝ) + L.remainder := by linarith [hzeros.1]
  have hu : u = (L.degree : ℝ) / 2 := by linarith [hzeros.2]
  have hmu0 := L.mean_zero_balanced (by omega) hbalance
  have hmono : StrictMono L.mean := strictMono_of_hasDerivAt_pos
    L.mean_hasDerivAt (L.variance_pos (by omega))
  have ht : t = 0 := hmono.injective (by change u = _; rw [hu,hmu0])
  exact ⟨hbalance,ht⟩

/-- At balance the ceiling is attained at zero; both the first and second
moments here are consequences of the real recurrence itself. -/
theorem RealRecurrenceLaw.variance_sharp_equality_sufficient (L : RealRecurrenceLaw)
    (hm : 3 ≤ L.degree) (hbal : L.marks = (L.degree : ℝ) + L.remainder) :
    L.variance 0 = (L.degree : ℝ) * (L.marks + L.remainder) /
      (4 * (L.marks + L.degree + L.remainder - 1)) := by
  have hu := L.mean_zero_balanced (by omega) hbal
  have hh := L.varianceDifferentialBalance 0
  simp only [Real.exp_zero, one_mul] at hh
  rw [hu] at hh
  rw [hbal] at hh ⊢
  have hmR : (3 : ℝ) ≤ L.degree := by exact_mod_cast hm
  have hr := L.remainder_nonneg
  have hT : (L.degree : ℝ) + L.remainder + L.degree + L.remainder - 1 ≠ 0 := by linarith
  apply (eq_div_iff (mul_ne_zero (by norm_num) hT)).mpr
  nlinarith only [hh]

/-- Complete equality classification for the actual real-parameter recurrence law. -/
theorem RealRecurrenceLaw.variance_sharp_equality_iff (L : RealRecurrenceLaw)
    (hm : 3 ≤ L.degree) (t : ℝ) :
    L.variance t = (L.degree : ℝ) * (L.marks + L.remainder) /
      (4 * (L.marks + L.degree + L.remainder - 1)) ↔
        L.marks = (L.degree : ℝ) + L.remainder ∧ t = 0 := by
  constructor
  · exact L.variance_sharp_equality_necessary hm t
  · rintro ⟨hbal,rfl⟩
    exact L.variance_sharp_equality_sufficient hm hbal


/-- The centered logarithmic transform of the actual recurrence law. -/
def RealRecurrenceLaw.centeredLogMGF (L : RealRecurrenceLaw) (t : ℝ) : ℝ :=
  Real.log (L.mgf t) - L.mean 0 * t

/-- Its continuous quadratic quotient, completed with the true variance at zero. -/
def RealRecurrenceLaw.proxyQuotient (L : RealRecurrenceLaw) (t : ℝ) : ℝ :=
  if t = 0 then L.variance 0 else 2 * L.centeredLogMGF t / t^2

theorem RealRecurrenceLaw.mgf_zero (L : RealRecurrenceLaw) : L.mgf 0 = 1 :=
  finiteMGF_zero_of_normalized _ _ _ L.mass_total

theorem RealRecurrenceLaw.centeredLogMGF_zero (L : RealRecurrenceLaw) :
    L.centeredLogMGF 0 = 0 := by
  simp [RealRecurrenceLaw.centeredLogMGF, L.mgf_zero]

theorem RealRecurrenceLaw.centeredLogMGF_hasDerivAt (L : RealRecurrenceLaw) (t : ℝ) :
    HasDerivAt L.centeredLogMGF (L.mean t - L.mean 0) t := by
  simpa only [RealRecurrenceLaw.centeredLogMGF, RealRecurrenceLaw.mean,
    RealRecurrenceLaw.mgf, Pi.sub_apply] using!
    (finiteLogMGF_hasDerivAt (Finset.range (L.degree + 1)) L.mass
      (fun i => (i : ℝ)) L.mass_nonneg L.mass_total t).sub
        (hasDerivAt_const_mul (L.mean 0))

/-- The curvature ceiling yields a strict quadratic envelope away from zero. -/
theorem RealRecurrenceLaw.centeredLogMGF_lt_sharp (L : RealRecurrenceLaw)
    (hm : 3 ≤ L.degree) (t : ℝ) (ht : t ≠ 0) :
    L.centeredLogMGF t <
      ((L.degree : ℝ) * (L.marks + L.remainder) /
        (4 * (L.marks + L.degree + L.remainder - 1))) * t^2 / 2 := by
  exact strict_quadratic_envelope_of_curvature_single_contact _ 0
    L.centeredLogMGF_hasDerivAt (fun s => (L.mean_hasDerivAt s).sub_const _)
    (L.variance_sharp hm)
    (fun s hs => (L.variance_sharp_equality_necessary hm s hs).2)
    L.centeredLogMGF_zero (sub_self _) t ht

/-- The variance is the two-sided limit of the centered quadratic quotient. -/
theorem RealRecurrenceLaw.centered_quadratic_limit (L : RealRecurrenceLaw) :
    Tendsto (fun t => L.centeredLogMGF t / t^2) (𝓝[≠] (0 : ℝ))
      (𝓝 (L.variance 0 / 2)) := by
  exact quadratic_quotient_limit L.centeredLogMGF_hasDerivAt
    ((L.mean_hasDerivAt 0).sub_const _) L.centeredLogMGF_zero (sub_self _)

theorem RealRecurrenceLaw.quadratic_proxy_ge_variance (L : RealRecurrenceLaw)
    (D : ℝ) (hD : IsQuadraticProxy L.centeredLogMGF D) : L.variance 0 ≤ D :=
  quadraticProxy_lower_of_quotient_limit _ _ _ L.centered_quadratic_limit hD

/-- At balance the ordinary variance is the exact optimal global proxy. -/
theorem RealRecurrenceLaw.isOptimalQuadraticProxy_balanced (L : RealRecurrenceLaw)
    (hm : 3 ≤ L.degree) (hbal : L.marks = (L.degree : ℝ) + L.remainder) :
    IsOptimalQuadraticProxy L.centeredLogMGF (L.variance 0) := by
  refine ⟨?_, fun D hD => L.quadratic_proxy_ge_variance D hD⟩
  intro t
  by_cases ht : t = 0
  · subst t
    simp [L.centeredLogMGF_zero]
  · have h := L.centeredLogMGF_lt_sharp hm t ht
    rw [← L.variance_sharp_equality_sufficient hm hbal] at h
    exact h.le

theorem RealRecurrenceLaw.optimalProxy_balanced (L : RealRecurrenceLaw)
    (hm : 3 ≤ L.degree) (hbal : L.marks = (L.degree : ℝ) + L.remainder) :
    optimalProxy L.centeredLogMGF = L.variance 0 :=
  optimalProxy_eq_of_optimal _ L.centeredLogMGF_zero _
    (L.isOptimalQuadraticProxy_balanced hm hbal)

/-- Every nonzero tilt has strictly smaller proxy quotient than the balanced
zero-tilt contact. -/
theorem RealRecurrenceLaw.proxyQuotient_lt_balanced (L : RealRecurrenceLaw)
    (hm : 3 ≤ L.degree) (hbal : L.marks = (L.degree : ℝ) + L.remainder)
    (t : ℝ) (ht : t ≠ 0) : L.proxyQuotient t < L.variance 0 := by
  simp only [RealRecurrenceLaw.proxyQuotient, if_neg ht]
  apply (div_lt_iff₀ (sq_pos_of_ne_zero ht)).mpr
  have h := L.centeredLogMGF_lt_sharp hm t ht
  rw [← L.variance_sharp_equality_sufficient hm hbal] at h
  nlinarith only [h]

theorem RealRecurrenceLaw.proxyQuotient_le_balanced (L : RealRecurrenceLaw)
    (hm : 3 ≤ L.degree) (hbal : L.marks = (L.degree : ℝ) + L.remainder)
    (t : ℝ) : L.proxyQuotient t ≤ L.variance 0 := by
  by_cases ht : t = 0
  · subst t
    simp [RealRecurrenceLaw.proxyQuotient]
  · exact (L.proxyQuotient_lt_balanced hm hbal t ht).le

/-- Zero is the unique global maximizer of the completed proxy quotient. -/
theorem RealRecurrenceLaw.proxyQuotient_isMaxOn_iff_balanced (L : RealRecurrenceLaw)
    (hm : 3 ≤ L.degree) (hbal : L.marks = (L.degree : ℝ) + L.remainder) (t : ℝ) :
    IsMaxOn L.proxyQuotient univ t ↔ t = 0 := by
  constructor
  · intro hmax
    by_contra ht
    have h0 : L.proxyQuotient 0 ≤ L.proxyQuotient t := hmax (mem_univ 0)
    rw [show L.proxyQuotient 0 = L.variance 0 by simp [RealRecurrenceLaw.proxyQuotient]] at h0
    exact (not_le_of_gt (L.proxyQuotient_lt_balanced hm hbal t ht)) h0
  · rintro rfl
    intro s _
    change L.proxyQuotient s ≤ L.proxyQuotient 0
    rw [show L.proxyQuotient 0 = L.variance 0 by simp [RealRecurrenceLaw.proxyQuotient]]
    exact L.proxyQuotient_le_balanced hm hbal s

end
end ExactHoeffding
