import ExactHoeffding.AnalyticTiltPartial
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-! # A real-analytic implicit branch for a scalar tilt equation -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

theorem analytic_implicit_tilt (F : ℝ × ℝ → ℝ)
    (hF : AnalyticAt ℝ F (0, 0)) (hzero : F (0, 0) = 0)
    (htilt : tiltPartial F (0, 0) ≠ 0) :
    ∃ τ : ℝ → ℝ, AnalyticAt ℝ τ 0 ∧ τ 0 = 0 ∧
      (∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0), F u = 0 ↔ τ u.1 = u.2) := by
  have hinv : (fderiv ℝ F (0, 0) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ).IsInvertible := by
    let a : ℝ := tiltPartial F (0, 0)
    let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 a htilt)
    refine ⟨e, ?_⟩
    change (e : ℝ →L[ℝ] ℝ) = fderiv ℝ F (0, 0) ∘L ContinuousLinearMap.inr ℝ ℝ ℝ
    apply ContinuousLinearMap.ext
    intro x
    change x * a = fderiv ℝ F (0, 0) (0, x)
    rw [show ((0, x) : ℝ × ℝ) = x • ((0, 1) : ℝ × ℝ) by ext <;> simp]
    rw [map_smul, smul_eq_mul]
    rfl
  let φ := hF.hasStrictFDerivAt.implicitFunctionDataOfProdDomain hinv
  have hprod : AnalyticAt ℝ φ.prodFun φ.pt := by
    exact hF.prod analyticAt_fst
  have hprodderiv : fderiv ℝ φ.toOpenPartialHomeomorph φ.pt =
      (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
        φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker :
          (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) := φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have haninv : AnalyticAt ℝ φ.toOpenPartialHomeomorph.symm
      (φ.toOpenPartialHomeomorph φ.pt) :=
    φ.toOpenPartialHomeomorph.analyticAt_symm' φ.pt_mem_toOpenPartialHomeomorph_source
      hprod hprodderiv
  let τ := hF.hasStrictFDerivAt.implicitFunctionOfProdDomain hinv
  have hτ : AnalyticAt ℝ τ 0 := by
    have hpoint : φ.toOpenPartialHomeomorph φ.pt = ((0 : ℝ), (0 : ℝ)) := by
      change (F (0, 0), (0 : ℝ)) = (0, 0)
      rw [hzero]
    rw [hpoint] at haninv
    have hs : AnalyticAt ℝ (fun e : ℝ => φ.toOpenPartialHomeomorph.symm (0, e)) 0 :=
      haninv.comp_of_eq (f := fun e : ℝ => ((0 : ℝ), e))
        (analyticAt_const.prod analyticAt_id) rfl
    have hτeq : τ = fun e : ℝ => (φ.toOpenPartialHomeomorph.symm (0, e)).2 := by
      funext e
      change (φ.implicitFunction (F (0, 0)) e).2 = _
      rw [hzero]
      rfl
    rw [hτeq]
    exact analyticAt_snd.comp_of_eq hs rfl
  have heq : ∀ᶠ u : ℝ × ℝ in 𝓝 (0, 0), F u = 0 ↔ τ u.1 = u.2 := by
    simpa only [hzero] using
      hF.hasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  exact ⟨τ, hτ, heq.self_of_nhds.mp hzero, heq⟩

end

end ExactHoeffding
