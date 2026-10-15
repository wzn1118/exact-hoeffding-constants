import ExactHoeffding.CanonicalCurvature
import ExactHoeffding.StrictAdmissibility
import ExactHoeffding.StationaryEquality
import ExactHoeffding.ZeroTiltMoments
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

open Set
open scoped Topology

namespace ExactHoeffding

/-- In the canonical support-degree-at-least-three domain, equality in the
sharp all-tilt curvature bound forces the larger margin to be balanced and
the tilt to be zero. -/
theorem hypergeomTiltVariance_sharp_canonical_equality_necessary
    (k m r : ℕ) (hmk : m≤k) (hm : 3≤m) (t : ℝ)
    (heq : hypergeomTiltVariance (k+m+r) k m t =
      (m:ℝ)*((k:ℝ)+r)/(4*((k:ℝ)+m+r-1))) :
    k=m+r ∧ t=0 := by
  let u := hypergeomTiltMean (k+m+r) k m t
  let v := hypergeomTiltVariance (k+m+r) k m t
  let T : ℝ := (k:ℝ)+m+r-1
  let L : ℝ := (k:ℝ)+r-1
  let B : ℝ := (m:ℝ)*((k:ℝ)+r)/(4*T)
  have hm3 : (3:ℝ)≤m := by exact_mod_cast hm
  have hmpos : (0:ℝ)<m := by linarith
  have hmkR : (m:ℝ)≤k := by exact_mod_cast hmk
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg r
  have hT : 0<T := by dsimp [T]; linarith
  have hL : (m:ℝ)-1≤L := by dsimp [L]; linarith
  have heqB : v=B := heq
  have hlocal : IsLocalMax (hypergeomTiltVariance (k+m+r) k m) t := by
    have hmax : IsMaxOn (hypergeomTiltVariance (k+m+r) k m) univ t := by
      intro s _
      rw [heq]
      exact hypergeomTiltVariance_sharp_canonical k m r hmk hm s
    exact hmax.isLocalMax (by simp)
  have hw : deriv (hypergeomTiltVariance (k+m+r) k m) t=0 := hlocal.deriv_eq_zero
  have hbal := hypergeomTiltMeanVariance_balance k m r hmk t
  have hstat := hypergeomTiltVariance_stationary_balance k m r hmk t hw
  have hpoly : stationaryPolynomial (m:ℝ) (k:ℝ) (r:ℝ) u v=0 := by
    apply stationary_elimination (m:ℝ) (k:ℝ) (r:ℝ) u v (Real.exp t)
    · dsimp [u,v] at *
      nlinarith only [hbal]
    · dsimp only at hstat
      unfold stationaryDen
      convert hstat using 1
      ring
  have hstrictPB := hypergeomTiltVariance_admissible_strict k m r hmk (by omega) t
  change v<u*((m:ℝ)-u)/m at hstrictPB
  rw [heqB] at hstrictPB
  have hstrict : B*(m:ℝ)<u*((m:ℝ)-u) := (lt_div_iff₀ hmpos).mp hstrictPB
  have hBT : B*(4*T)=(m:ℝ)*((k:ℝ)+r) := by dsimp [B]; field_simp [hT.ne']
  have hp := mul_pos (sub_pos.mpr hstrict) (mul_pos (by norm_num : (0:ℝ)<4) hT)
  have hBTm := congrArg (fun z : ℝ => z*(m:ℝ)) hBT
  have hA : 0<(m:ℝ)^2*((m:ℝ)-1)-(L+m)*(2*u-m)^2 := by
    dsimp [T,L] at hp hBTm ⊢
    nlinarith only [hp,hBTm]
  have hD : |(k:ℝ)-m-r|≤L-m+1 := by
    apply abs_le.mpr
    dsimp [L]
    constructor <;> linarith
  have hTform : 2*(m:ℝ)+((k:ℝ)-m)+r-1=T := by dsimp [T]; ring
  have hmform : (m:ℝ)+((k:ℝ)-m)=(k:ℝ) := by ring
  have huform : ((m:ℝ)+(2*u-m))/2=u := by ring
  have hid := stationary_main_identity (m:ℝ) ((k:ℝ)-m) (r:ℝ) (2*u-m)
    (by rw [hTform]; exact hT.ne')
  rw [hTform,hmform,huform] at hid
  change -16*T*stationaryPolynomial (m:ℝ) (k:ℝ) (r:ℝ) u B = _ at hid
  rw [← heqB,hpoly,mul_zero] at hid
  have hQ : ((m:ℝ)^2*((m:ℝ)-1)-(L+m)*(2*u-m)^2)*
      (((k:ℝ)-m-r)-(2*u-m))^2+
      (L+1)*(2*(m:ℝ)*((k:ℝ)-m-r)*(2*u-m)+
        (L*(L+1)-2*m)*(2*u-m)^2)=0 := by
    dsimp [L,T] at hid ⊢
    nlinarith only [hid]
  have hzeros := (universal_stationary_comparison_eq_zero_iff
    (m:ℝ) L ((k:ℝ)-m-r) (2*u-m) hm3 hL hD hA).mp hQ
  have hkm : (k:ℝ)=(m:ℝ)+r := by linarith [hzeros.1]
  have hkmNat : k=m+r := by exact_mod_cast hkm
  have hu : u=(m:ℝ)/2 := by linarith [hzeros.2]
  have hmu0 : hypergeomTiltMean (k+m+r) k m 0=(m:ℝ)/2 := by
    rw [hypergeomTiltMean_zero (k+m+r) k m (by omega) (by omega)]
    push_cast
    have hN : (k:ℝ)+(m:ℝ)+r≠0 := by positivity
    apply (div_eq_iff hN).mpr
    rw [hkm]
    ring
  have hmono : StrictMono (hypergeomTiltMean (k+m+r) k m) :=
    strictMono_of_hasDerivAt_pos
      (hypergeomTiltMean_hasDerivAt (k+m+r) k m (by omega) (by omega))
      (hypergeomTiltVariance_pos k m r hmk (by omega))
  have ht : t=0 := hmono.injective (by change u = _; rw [hu,hmu0])
  exact ⟨hkmNat,ht⟩

theorem hypergeomTiltVariance_sharp_canonical_equality_sufficient
    (k m r : ℕ) (hmk : m≤k) (hm : 3≤m) (hbal : k=m+r) :
    hypergeomTiltVariance (k+m+r) k m 0 =
      (m:ℝ)*((k:ℝ)+r)/(4*((k:ℝ)+m+r-1)) := by
  rw [hypergeomTiltVariance_zero (k+m+r) k m (by omega) (by omega)]
  have hNk : k+m+r-k=m+r := by omega
  have hNm : k+m+r-m=k+r := by omega
  rw [hNk,hNm]
  push_cast
  have hkm : (k:ℝ)=(m:ℝ)+r := by exact_mod_cast hbal
  have hm3 : (3:ℝ)≤m := by exact_mod_cast hm
  have hmkR : (m:ℝ)≤k := by exact_mod_cast hmk
  have hr0 : (0:ℝ)≤r := Nat.cast_nonneg r
  have hN : (k:ℝ)+m+r≠0 := by positivity
  have hN1 : (k:ℝ)+m+r-1≠0 := by linarith
  field_simp [hN,hN1]
  rw [hkm]
  ring

theorem hypergeomTiltVariance_sharp_canonical_equality_iff
    (k m r : ℕ) (hmk : m≤k) (hm : 3≤m) (t : ℝ) :
    hypergeomTiltVariance (k+m+r) k m t =
      (m:ℝ)*((k:ℝ)+r)/(4*((k:ℝ)+m+r-1)) ↔ k=m+r ∧ t=0 := by
  constructor
  · exact hypergeomTiltVariance_sharp_canonical_equality_necessary k m r hmk hm t
  · rintro ⟨hbal,rfl⟩
    exact hypergeomTiltVariance_sharp_canonical_equality_sufficient k m r hmk hm hbal


end ExactHoeffding
