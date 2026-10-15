import ExactHoeffding.TiltedAdmissibilityDirect
import ExactHoeffding.HypergeometricEndpoints
import ExactHoeffding.StationaryCertificates
import ExactHoeffding.StationaryGlobal

namespace ExactHoeffding

/-- The sharp stationary bound applies to the actual hypergeometric law,
with its admissibility supplied by the adjacent-mass argument. -/
theorem hypergeomTiltVariance_stationary_sharp (k m r : ℕ)
    (hmk : m≤k) (hm : 3≤m) (t : ℝ)
    (hw : deriv (hypergeomTiltVariance (k+m+r) k m) t=0) :
    hypergeomTiltVariance (k+m+r) k m t≤
      (m:ℝ)*((k:ℝ)+r)/(4*((k:ℝ)+m+r-1)) := by
  let u := hypergeomTiltMean (k+m+r) k m t
  let v := hypergeomTiltVariance (k+m+r) k m t
  have hbal := hypergeomTiltMeanVariance_balance k m r hmk t
  have hstat := hypergeomTiltVariance_stationary_balance k m r hmk t hw
  have hpoly : stationaryPolynomial (m:ℝ) (k:ℝ) (r:ℝ) u v=0 := by
    apply stationary_elimination (m:ℝ) (k:ℝ) (r:ℝ) u v (Real.exp t)
    · dsimp [u,v] at *
      nlinarith only [hbal]
    · dsimp only at hstat
      change Real.exp t*stationaryDen (m:ℝ) (k:ℝ) u v=v*((r:ℝ)+2*u)
      unfold stationaryDen
      convert hstat using 1 <;> ring
  have hh : 0≤(k:ℝ)-(m:ℝ) := sub_nonneg.mpr (by exact_mod_cast hmk)
  have hj : (3:ℝ)≤m := by exact_mod_cast hm
  have hsum : (m:ℝ)+((k:ℝ)-(m:ℝ))=(k:ℝ) := by ring
  have hpoly' : stationaryPolynomial (m:ℝ) ((m:ℝ)+((k:ℝ)-(m:ℝ))) (r:ℝ) u v=0 := by
    rw [hsum]
    exact hpoly
  have hb := admissible_stationary_sharp_bound (m:ℝ) ((k:ℝ)-(m:ℝ)) (r:ℝ) u v
    hj hh (Nat.cast_nonneg _)
    (hypergeomTiltMean_pos k m r hmk (by omega) t)
    (hypergeomTiltMean_lt k m r hmk (by omega) t)
    (hypergeomTiltVariance_pos k m r hmk (by omega) t)
    (hypergeomTiltVariance_admissible k m r hmk (by omega) t) hpoly'
  convert hb using 1 <;> ring

/-- Every real tilt of a canonical hypergeometric law satisfies the sharp
finite-population curvature bound for support degree at least three. -/
theorem hypergeomTiltVariance_sharp_canonical (k m r : ℕ)
    (hmk : m≤k) (hm : 3≤m) (t : ℝ) :
    hypergeomTiltVariance (k+m+r) k m t≤
      (m:ℝ)*((k:ℝ)+r)/(4*((k:ℝ)+m+r-1)) := by
  have hmc : (3:ℝ)≤m := by exact_mod_cast hm
  have hkc : (m:ℝ)≤k := by exact_mod_cast hmk
  have hden : 0<(k:ℝ)+m+r-1 := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hnum : 0<(k:ℝ)+r := by have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hbound : 0<(m:ℝ)*((k:ℝ)+r)/(4*((k:ℝ)+m+r-1)) := by positivity
  apply global_bound_of_stationary_bound
    (continuous_iff_continuousAt.mpr (fun s =>
      (hypergeomTiltVariance_differentiableAt (k+m+r) k m
        (by omega) (by omega) s).continuousAt)) hbound
    (hypergeomTiltVariance_tendsto_atBot k m r hmk)
    (hypergeomTiltVariance_tendsto_atTop k m r hmk)
    (fun s hs => hypergeomTiltVariance_stationary_sharp k m r hmk hm s hs) t

theorem hypergeomTiltVariance_sharp_of_margins (N k m : ℕ)
    (hmk : m≤k) (hkm : k+m≤N) (hm : 3≤m) (t : ℝ) :
    hypergeomTiltVariance N k m t≤(m:ℝ)*((N:ℝ)-m)/(4*((N:ℝ)-1)) := by
  have hn : k+m+(N-(k+m))=N := Nat.add_sub_of_le hkm
  have hrest : ((N-(k+m):ℕ):ℝ)=(N:ℝ)-k-m := by
    rw [Nat.cast_sub hkm,Nat.cast_add]
    ring
  have h := hypergeomTiltVariance_sharp_canonical k m (N-(k+m)) hmk hm t
  rw [hn,hrest] at h
  convert h using 1 <;> ring

theorem hypergeomLogMGF_sharp_curvature_of_margins (N k m : ℕ)
    (hmk : m≤k) (hkm : k+m≤N) (hm : 3≤m) (t : ℝ) :
    deriv (deriv (fun s => Real.log (hypergeomMGF N k m s))) t≤
      (m:ℝ)*((N:ℝ)-m)/(4*((N:ℝ)-1)) := by
  rw [hypergeomLogMGF_second_deriv_eq_variance N k m (by omega) (by omega) t]
  exact hypergeomTiltVariance_sharp_of_margins N k m hmk hkm hm t

end ExactHoeffding
