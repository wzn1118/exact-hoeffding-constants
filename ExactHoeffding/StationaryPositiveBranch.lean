import ExactHoeffding.StationaryCertificates
import Mathlib.Analysis.Real.Sqrt

/-! # Existence and uniqueness of the admissible positive stationary branch -/
namespace ExactHoeffding
noncomputable section

/-- A concave quadratic with positive constant has precisely one positive root. -/
theorem concave_quadratic_existsUnique_positive_root (T b c:ℝ)
    (hT:0<T) (hc:0<c) : ∃! v:ℝ,0<v ∧ -T*v^2+b*v+c=0 := by
  let s:=Real.sqrt (b^2+4*T*c)
  have hd:0≤b^2+4*T*c := by positivity
  have hs:s^2=b^2+4*T*c := Real.sq_sqrt hd
  have hbs:|b|<s := by
    apply (Real.lt_sqrt (abs_nonneg b)).2
    rw [sq_abs]
    nlinarith [mul_pos hT hc]
  have hnum:0<b+s := by linarith [neg_abs_le b]
  let v:=(b+s)/(2*T)
  have hv:0<v := div_pos hnum (by positivity)
  have heq: -T*v^2+b*v+c=0 := by
    dsimp [v]
    field_simp [hT.ne']
    nlinarith [hs]
  refine ⟨v,⟨hv,heq⟩,?_⟩
  intro w hw
  exact le_antisymm
    (concave_quadratic_positive_root_bound T b c w v hT hc hw.1 hv hw.2 heq.le)
    (concave_quadratic_positive_root_bound T b c v w hT hc hv hw.1 heq hw.2.le)

/-- The manuscript's stationary polynomial has a uniquely determined
positive branch at every admissible real mean. -/
theorem stationaryPolynomial_existsUnique_positive_root (j m r u:ℝ)
    (_hj:1≤j) (hjm:j≤m) (hr:0≤r) (hN:1<j+m+r)
    (hu:0<u) (huj:u<j) :
    ∃! v:ℝ,0<v ∧ stationaryPolynomial j m r u v=0 := by
  have hc:0<u*(j-u)*(r+u)*(m-u) := by
    have hmu:0<m-u := by linarith
    positivity
  obtain ⟨v,hv,hunique⟩ := concave_quadratic_existsUnique_positive_root
    (j+m+r-1)
    (-j*m*r-2*j*m*u+j*m+j*u^2-j*u+m*u^2-m*u+r*u^2+r*u+2*u^2)
    (u*(j-u)*(r+u)*(m-u)) (by linarith only [hN]) hc
  refine ⟨v,⟨hv.1,?_⟩,?_⟩
  · rw [stationary_polynomial_quadratic]
    exact hv.2
  · intro w hw
    apply hunique w
    exact ⟨hw.1,by simpa only [stationary_polynomial_quadratic] using hw.2⟩

end
end ExactHoeffding
