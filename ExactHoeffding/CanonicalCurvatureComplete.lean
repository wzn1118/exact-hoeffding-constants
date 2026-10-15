import ExactHoeffding.CanonicalCurvature
import ExactHoeffding.SmallSupportCurvature
import ExactHoeffding.DegenerateCurvature

namespace ExactHoeffding

/-- Every support degree, including zero, in the canonical margin domain. -/
theorem hypergeom_sharp_curvature_canonical_complete (N k m : ℕ)
    (hmk : m≤k) (hkm : k+m≤N) (t : ℝ) :
    deriv (deriv (fun s => Real.log (hypergeomMGF N k m s))) t≤
      (m:ℝ)*((N:ℝ)-m)/(4*((N:ℝ)-1)) := by
  by_cases hm0 : m=0
  · subst m
    rw [hypergeom_curvature_zero_draws]
    simp
  by_cases hm1 : m=1
  · subst m
    have hN : 1<N := by omega
    have hN1 : (N:ℝ)-1≠0 := by
      have hh : (1:ℝ)<N := by exact_mod_cast hN
      linarith
    have h := hypergeom_one_draw_curvature_le N k (by omega) (by omega) t
    convert h using 1
    push_cast
    field_simp
  by_cases hm2 : m=2
  · subst m
    have h := hypergeom_two_draw_curvature_le N k hmk hkm t
    have hN1 : (N:ℝ)-1≠0 := by
      have hh : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
      linarith
    convert h using 1
    push_cast
    field_simp [hN1]
    ring
  exact hypergeomLogMGF_sharp_curvature_of_margins N k m hmk hkm (by omega) t

theorem canonical_margin_product_order (N k m : ℝ)
    (hmk : m≤k) (hkm : k+m≤N) : m*(N-m)≤k*(N-k) := by
  have h := mul_nonneg (sub_nonneg.mpr hmk) (sub_nonneg.mpr hkm)
  nlinarith only [h]

/-- The canonical result already has the manuscript's symmetric minimum. -/
theorem hypergeom_sharp_curvature_canonical_min (N k m : ℕ)
    (hmk : m≤k) (hkm : k+m≤N) (t : ℝ) :
    deriv (deriv (fun s => Real.log (hypergeomMGF N k m s))) t≤
      min ((k:ℝ)*((N:ℝ)-k)) ((m:ℝ)*((N:ℝ)-m))/(4*((N:ℝ)-1)) := by
  have h := canonical_margin_product_order (N:ℝ) (k:ℝ) (m:ℝ)
    (by exact_mod_cast hmk) (by exact_mod_cast hkm)
  rw [min_eq_right h]
  exact hypergeom_sharp_curvature_canonical_complete N k m hmk hkm t

end ExactHoeffding
