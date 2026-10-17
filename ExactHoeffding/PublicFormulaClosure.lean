import ExactHoeffding.GoalBFixedSample
import ExactHoeffding.StationaryPositiveBranch

/-! # Strict cubic artanh comparison and the explicit stationary root

These public interfaces record the strict inverse-hyperbolic-tangent
comparison and the radical expression of the unique positive stationary
root, using the existing actual calculus and stationary polynomial APIs.
-/

namespace ExactHoeffding
noncomputable section
open Set

/-- The cubic lower estimate is strict at every positive imbalance. -/
theorem real_artanh_cubic_strict_lower (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    d + d ^ 3 / 3 < Real.artanh d := by
  let f : ℝ → ℝ := fun x => Real.artanh x - x - x ^ 3 / 3
  have hf (x : ℝ) (hx : x ∈ Icc (0 : ℝ) d) :
      HasDerivAt f (x ^ 4 / (1 - x ^ 2)) x := by
    have hx' : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 hd1⟩
    have hden : 1 - x ^ 2 ≠ 0 := by nlinarith [hx'.1, hx'.2]
    have h := ((artanh_hasDerivAt_open x hx').sub (hasDerivAt_id x)).sub
      (((hasDerivAt_id x).pow 3).div_const 3)
    apply h.congr_deriv
    dsimp
    field_simp [hden]
    <;> ring
  have hmono : StrictMonoOn f (Icc (0 : ℝ) d) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 d)
    · intro x hx
      exact (hf x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hf x ⟨hx.1.le, hx.2.le⟩).deriv]
      apply div_pos (pow_pos hx.1 4)
      have hx1 : x < 1 := lt_trans hx.2 hd1
      nlinarith [hx.1]
  have h := hmono ⟨le_rfl, hd0.le⟩ ⟨hd0.le, le_rfl⟩ hd0
  dsimp [f] at h
  simpa using (show d + d ^ 3 / 3 < Real.artanh d by
    norm_num at h
    linarith)

/-- The corresponding Bernoulli proxy deficit is also strict. -/
theorem bernoulli_cubic_proxy_strict_upper (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) :
    d / (4 * Real.artanh d) < 1 / (4 * (1 + d ^ 2 / 3)) := by
  have h := real_artanh_cubic_strict_lower d hd0 hd1
  have ha : 0 < Real.artanh d := Real.artanh_pos ⟨hd0, hd1⟩
  have hb : 0 < 1 + d ^ 2 / 3 := by positivity
  apply (div_lt_div_iff₀ (by positivity : 0 < 4 * Real.artanh d)
    (by positivity : 0 < 4 * (1 + d ^ 2 / 3))).2
  nlinarith

/-- Every positive root of the concave quadratic is its positive radical. -/
theorem concave_quadratic_positive_root_eq_radical (T b c v : ℝ)
    (hT : 0 < T) (hc : 0 < c) (hv : 0 < v)
    (hroot : -T * v ^ 2 + b * v + c = 0) :
    v = (b + Real.sqrt (b ^ 2 + 4 * T * c)) / (2 * T) := by
  let s := Real.sqrt (b ^ 2 + 4 * T * c)
  have hdisc : 0 ≤ b ^ 2 + 4 * T * c := by positivity
  have hs : s ^ 2 = b ^ 2 + 4 * T * c := Real.sq_sqrt hdisc
  have hbs : |b| < s := by
    apply (Real.lt_sqrt (abs_nonneg b)).2
    rw [sq_abs]
    nlinarith [mul_pos hT hc]
  have hnum : 0 < b + s := by linarith [neg_abs_le b]
  have hw : 0 < (b + s) / (2 * T) := div_pos hnum (by positivity)
  have hweq : -T * ((b + s) / (2 * T)) ^ 2 + b * ((b + s) / (2 * T)) + c = 0 := by
    field_simp [hT.ne']
    nlinarith [hs]
  obtain ⟨w, _, hunique⟩ := concave_quadratic_existsUnique_positive_root T b c hT hc
  have hvw := hunique v ⟨hv, hroot⟩
  have hww := hunique ((b + s) / (2 * T)) ⟨hw, hweq⟩
  exact hvw.trans hww.symm

/-- The positive stationary branch has exactly the manuscript's radical,
with `N=j+m+r` and the displayed quadratic coefficient. -/
theorem stationaryPolynomial_positive_root_eq_radical (j m r u v : ℝ)
    (_hj : 1 ≤ j) (hjm : j ≤ m) (hr : 0 ≤ r) (hN : 1 < j + m + r)
    (hu : 0 < u) (huj : u < j) (hv : 0 < v)
    (hroot : stationaryPolynomial j m r u v = 0) :
    let N := j + m + r
    let b := (N + 2) * u ^ 2 + (-2 * j * m - j - m + r) * u + j * m * (1 - r)
    v = (b + Real.sqrt (b ^ 2 + 4 * (N - 1) * (u * (j - u) * (r + u) * (m - u)))) /
      (2 * (N - 1)) := by
  dsimp only
  apply concave_quadratic_positive_root_eq_radical
  · linarith
  · have hmu : 0 < m - u := by linarith
    positivity
  · exact hv
  · rw [stationary_polynomial_quadratic] at hroot
    nlinarith only [hroot]

end
end ExactHoeffding
