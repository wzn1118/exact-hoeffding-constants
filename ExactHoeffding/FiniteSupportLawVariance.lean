import ExactHoeffding.FiniteSupportTiltCurveOfLaw
import Mathlib.Tactic.Ring

/-! # Strict tilted variance from a nondegenerate finite law

The positive endpoint atoms in `FiniteSupportLawData` imply strictly positive
variance under every exponential tilt. This removes a regularity hypothesis
from direct finite-law uses of the mean-coordinate comparison. -/

namespace ExactHoeffding
noncomputable section

private lemma finite_sum_center_square_identity {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a x : ι → ℝ) :
    let M := ∑ i ∈ s, a i
    let F := ∑ i ∈ s, a i * x i
    let S := ∑ i ∈ s, a i * x i ^ 2
    ∑ i ∈ s, a i * (M * x i - F) ^ 2 = M ^ 2 * S - M * F ^ 2 := by
  classical
  dsimp
  let M : ℝ := ∑ i ∈ s, a i
  let F : ℝ := ∑ i ∈ s, a i * x i
  let S : ℝ := ∑ i ∈ s, a i * x i ^ 2
  have hterm : ∀ i, a i * (M * x i - F) ^ 2 =
      a i * (M ^ 2 * x i ^ 2) - a i * (2 * M * x i * F) + a i * F ^ 2 := by
    intro i
    ring
  calc
    ∑ i ∈ s, a i * (M * x i - F) ^ 2 =
        ∑ i ∈ s, (a i * (M ^ 2 * x i ^ 2) -
          a i * (2 * M * x i * F) + a i * F ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hterm i
    _ = (∑ i ∈ s, a i * (M ^ 2 * x i ^ 2)) -
        (∑ i ∈ s, a i * (2 * M * x i * F)) +
        (∑ i ∈ s, a i * F ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = M ^ 2 * S - M * F ^ 2 := by
      have hS : (∑ i ∈ s, a i * (M ^ 2 * x i ^ 2)) = M ^ 2 * S := by
        calc
          _ = ∑ i ∈ s, M ^ 2 * (a i * x i ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = M ^ 2 * S := by simp [S, Finset.mul_sum]
      have hF : (∑ i ∈ s, a i * (2 * M * x i * F)) = 2 * M * F ^ 2 := by
        calc
          _ = ∑ i ∈ s, (2 * M * F) * (a i * x i) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = (2 * M * F) * F := by simp [F, Finset.mul_sum]
          _ = 2 * M * F ^ 2 := by ring
      have hM : (∑ i ∈ s, a i * F ^ 2) = F ^ 2 * M := by
        calc
          _ = ∑ i ∈ s, F ^ 2 * a i := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = F ^ 2 * M := by simp [M, Finset.mul_sum]
      rw [hS, hF, hM]
      ring

/-- The log-MGF curvature of a finite law with two distinct positive endpoint
atoms is strictly positive at every real tilt. -/
theorem FiniteSupportLawData.variance_pos
    {ι : Type*} [DecidableEq ι] (L : FiniteSupportLawData ι) (t : ℝ) :
    0 < L.variance t := by
  let a : ι → ℝ := fun i =>
    L.weight i * Real.exp (t * L.centeredValue i)
  let M : ℝ := ∑ i ∈ L.support, a i
  let F : ℝ := ∑ i ∈ L.support, a i * L.centeredValue i
  let S : ℝ := ∑ i ∈ L.support, a i * L.centeredValue i ^ 2
  have hM : 0 < M := by
    dsimp [M, a, finiteMGF]
    exact finiteMGF_pos_of_normalized L.support L.weight L.centeredValue
      L.weight_nonneg L.weight_total t
  have hM_eq : M = finiteMGF L.support L.weight L.centeredValue t := by
    rfl
  have hF_eq : F = finiteTiltFirst L.support L.weight L.centeredValue t := by
    dsimp [F, a, finiteTiltFirst]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hS_eq : S = finiteTiltSecond L.support L.weight L.centeredValue t := by
    dsimp [S, a, finiteTiltSecond]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hmean := finiteSupportLawData_mean_mem_Ioo L t
  have hFmean : F = M * L.mean t := by
    rw [hM_eq, hF_eq]
    unfold FiniteSupportLawData.mean finiteEnvelopeTiltMean
    have hmgf : finiteMGF L.support L.weight L.centeredValue t ≠ 0 :=
      ne_of_gt (by rw [← hM_eq]; exact hM)
    field_simp [hmgf]
  have hnonneg : ∀ i ∈ L.support,
      0 ≤ a i * (M * L.centeredValue i - F) ^ 2 := by
    intro i hi
    exact mul_nonneg (mul_nonneg (L.weight_nonneg i hi)
      (Real.exp_pos _).le) (sq_nonneg _)
  have hpositive : 0 < a L.hiIndex *
      (M * L.centeredValue L.hiIndex - F) ^ 2 := by
    have ha : 0 < a L.hiIndex := by
      dsimp [a]
      exact mul_pos L.hi_weight_pos (Real.exp_pos _)
    have hgap : 0 < L.centeredValue L.hiIndex - L.mean t := by
      have := hmean.2
      dsimp [FiniteSupportLawData.centeredValue] at this ⊢
      linarith
    rw [hFmean]
    rw [show M * L.centeredValue L.hiIndex - M * L.mean t =
      M * (L.centeredValue L.hiIndex - L.mean t) by ring]
    exact mul_pos ha (sq_pos_of_pos (mul_pos hM hgap))
  have hsum : 0 < ∑ i ∈ L.support,
      a i * (M * L.centeredValue i - F) ^ 2 := by
    apply Finset.sum_pos'
    · exact hnonneg
    · exact ⟨L.hiIndex, L.hi_mem, hpositive⟩
  have hidentity := finite_sum_center_square_identity
    L.support a L.centeredValue
  have hidentity' :
      (∑ i ∈ L.support, a i * (M * L.centeredValue i - F) ^ 2) =
        M ^ 2 * S - M * F ^ 2 := by
    simpa [M, F, S] using hidentity
  have hnum : 0 < S * M - F ^ 2 := by
    have heq : M ^ 2 * S - M * F ^ 2 = M * (S * M - F ^ 2) := by ring
    rw [heq] at hidentity'
    have hprod : 0 < M * (S * M - F ^ 2) := by
      rw [← hidentity']
      exact hsum
    nlinarith
  unfold FiniteSupportLawData.variance finiteEnvelopeTiltVariance
  rw [finiteLogMGF_second_deriv L.support L.weight L.centeredValue
    L.weight_nonneg L.weight_total t]
  rw [← hM_eq, ← hF_eq, ← hS_eq]
  have hden : 0 < M ^ 2 := sq_pos_of_pos hM
  have hnum' : 0 < S * M - F * F := by nlinarith [hnum]
  exact div_pos hnum' hden

end
end ExactHoeffding
