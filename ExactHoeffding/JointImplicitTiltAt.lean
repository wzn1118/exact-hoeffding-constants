import ExactHoeffding.JointImplicitTilt

/-! # The analytic two-parameter implicit theorem at an arbitrary base point -/

namespace ExactHoeffding
noncomputable section
open Filter
open scoped Topology

theorem analytic_implicit_joint_tilt_at (F : (ℝ × ℝ) × ℝ → ℝ)
    (p₀ : ℝ × ℝ) (t₀ : ℝ)
    (hF : AnalyticAt ℝ F (p₀, t₀)) (hzero : F (p₀, t₀) = 0)
    (htilt : jointTiltPartial F (p₀, t₀) ≠ 0) :
    ∃ τ : ℝ × ℝ → ℝ, AnalyticAt ℝ τ p₀ ∧ τ p₀ = t₀ ∧
      (∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 (p₀, t₀), F u = 0 ↔ τ u.1 = u.2) := by
  have hinv : (fderiv ℝ F (p₀, t₀) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    let a : ℝ := jointTiltPartial F (p₀, t₀)
    let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 a htilt)
    refine ⟨e, ?_⟩
    change (e : ℝ →L[ℝ] ℝ) = fderiv ℝ F (p₀, t₀) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ
    apply ContinuousLinearMap.ext
    intro x
    change x * a = fderiv ℝ F (p₀, t₀) ((0, 0), x)
    rw [show (((0, 0), x) : (ℝ × ℝ) × ℝ) =
      x • (((0, 0), 1) : (ℝ × ℝ) × ℝ) by ext <;> simp]
    rw [map_smul, smul_eq_mul]
    rfl
  let φ := hF.hasStrictFDerivAt.implicitFunctionDataOfProdDomain hinv
  have hprod : AnalyticAt ℝ φ.prodFun φ.pt := hF.prod analyticAt_fst
  have hprodderiv : fderiv ℝ φ.toOpenPartialHomeomorph φ.pt =
      (φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
        φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker :
          ((ℝ × ℝ) × ℝ) →L[ℝ] (ℝ × (ℝ × ℝ))) :=
    φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  have haninv : AnalyticAt ℝ φ.toOpenPartialHomeomorph.symm
      (φ.toOpenPartialHomeomorph φ.pt) :=
    φ.toOpenPartialHomeomorph.analyticAt_symm' φ.pt_mem_toOpenPartialHomeomorph_source
      hprod hprodderiv
  let τ := hF.hasStrictFDerivAt.implicitFunctionOfProdDomain hinv
  have hτ : AnalyticAt ℝ τ p₀ := by
    have hpoint : φ.toOpenPartialHomeomorph φ.pt = ((0 : ℝ), p₀) := by
      change (F (p₀, t₀), p₀) = (0, p₀)
      rw [hzero]
    rw [hpoint] at haninv
    have hs : AnalyticAt ℝ
        (fun p : ℝ × ℝ => φ.toOpenPartialHomeomorph.symm (0, p)) p₀ :=
      haninv.comp_of_eq (f := fun p : ℝ × ℝ => ((0 : ℝ), p))
        (analyticAt_const.prod analyticAt_id) rfl
    have hτeq : τ = fun p : ℝ × ℝ => (φ.toOpenPartialHomeomorph.symm (0, p)).2 := by
      funext p
      change (φ.implicitFunction (F (p₀, t₀)) p).2 = _
      rw [hzero]
      rfl
    rw [hτeq]
    exact analyticAt_snd.comp_of_eq hs rfl
  have heq : ∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 (p₀, t₀), F u = 0 ↔ τ u.1 = u.2 := by
    simpa only [hzero] using
      hF.hasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  exact ⟨τ, hτ, heq.self_of_nhds.mp hzero, heq⟩

end
end ExactHoeffding
