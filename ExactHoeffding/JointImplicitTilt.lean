import ExactHoeffding.AnalyticImplicitTilt

/-! # Analytic implicit tilt with two independent parameters -/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

/-- Derivative in the scalar tilt coordinate, with both parameters held fixed. -/
def jointTiltPartial (F : (ℝ × ℝ) × ℝ → ℝ) (u : (ℝ × ℝ) × ℝ) : ℝ :=
  fderiv ℝ F u ((0, 0), 1)

theorem analyticAt_jointTiltPartial (F : (ℝ × ℝ) × ℝ → ℝ)
    (u : (ℝ × ℝ) × ℝ) (hF : AnalyticAt ℝ F u) :
    AnalyticAt ℝ (jointTiltPartial F) u := by
  exact (ContinuousLinearMap.apply ℝ ℝ (((0, 0), 1) : (ℝ × ℝ) × ℝ)).analyticAt _
    |>.comp_of_eq hF.fderiv rfl

theorem jointTiltPartial_eq_deriv (F : (ℝ × ℝ) × ℝ → ℝ)
    (u : (ℝ × ℝ) × ℝ) (hF : AnalyticAt ℝ F u) :
    jointTiltPartial F u = deriv (fun t => F (u.1, t)) u.2 := by
  have hins : HasDerivAt (fun t : ℝ => (u.1, t)) ((0, 0), 1) u.2 :=
    (hasDerivAt_const u.2 u.1).prodMk (hasDerivAt_id u.2)
  have hcomp := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq u.2 hins
    (show u = (u.1, u.2) by rfl)
  exact hcomp.deriv.symm

theorem jointTiltPartial2_eq_iteratedDeriv2 (F : (ℝ × ℝ) × ℝ → ℝ)
    (u : (ℝ × ℝ) × ℝ) (hF : AnalyticAt ℝ F u) :
    jointTiltPartial (jointTiltPartial F) u =
      iteratedDeriv 2 (fun t => F (u.1, t)) u.2 := by
  have hins : ContinuousAt (fun t : ℝ => (u.1, t)) u.2 :=
    continuousAt_const.prodMk continuousAt_id
  have heq : (fun t => jointTiltPartial F (u.1, t)) =ᶠ[𝓝 u.2]
      deriv (fun t => F (u.1, t)) := by
    filter_upwards [hins.eventually hF.eventually_analyticAt] with t ht
    exact jointTiltPartial_eq_deriv F (u.1, t) ht
  rw [jointTiltPartial_eq_deriv (jointTiltPartial F) u
      (analyticAt_jointTiltPartial F u hF),
    heq.deriv_eq, show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]

/-- A nondegenerate analytic scalar equation has an analytic critical branch
jointly in the two independent parameters, locally exhausting its zero set. -/
theorem analytic_implicit_joint_tilt (F : (ℝ × ℝ) × ℝ → ℝ)
    (hF : AnalyticAt ℝ F ((0, 0), 0)) (hzero : F ((0, 0), 0) = 0)
    (htilt : jointTiltPartial F ((0, 0), 0) ≠ 0) :
    ∃ τ : ℝ × ℝ → ℝ, AnalyticAt ℝ τ (0, 0) ∧ τ (0, 0) = 0 ∧
      (∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0), F u = 0 ↔ τ u.1 = u.2) := by
  have hinv : (fderiv ℝ F ((0, 0), 0) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ).IsInvertible := by
    let a : ℝ := jointTiltPartial F ((0, 0), 0)
    let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 a htilt)
    refine ⟨e, ?_⟩
    change (e : ℝ →L[ℝ] ℝ) = fderiv ℝ F ((0, 0), 0) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ
    apply ContinuousLinearMap.ext
    intro x
    change x * a = fderiv ℝ F ((0, 0), 0) ((0, 0), x)
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
  have hτ : AnalyticAt ℝ τ (0, 0) := by
    have hpoint : φ.toOpenPartialHomeomorph φ.pt = ((0 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
      change (F ((0, 0), 0), ((0 : ℝ), (0 : ℝ))) = (0, (0, 0))
      rw [hzero]
    rw [hpoint] at haninv
    have hs : AnalyticAt ℝ
        (fun p : ℝ × ℝ => φ.toOpenPartialHomeomorph.symm (0, p)) (0, 0) :=
      haninv.comp_of_eq (f := fun p : ℝ × ℝ => ((0 : ℝ), p))
        (analyticAt_const.prod analyticAt_id) rfl
    have hτeq : τ = fun p : ℝ × ℝ => (φ.toOpenPartialHomeomorph.symm (0, p)).2 := by
      funext p
      change (φ.implicitFunction (F ((0, 0), 0)) p).2 = _
      rw [hzero]
      rfl
    rw [hτeq]
    exact analyticAt_snd.comp_of_eq hs rfl
  have heq : ∀ᶠ u : (ℝ × ℝ) × ℝ in 𝓝 ((0, 0), 0), F u = 0 ↔ τ u.1 = u.2 := by
    simpa only [hzero] using
      hF.hasStrictFDerivAt.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv
  exact ⟨τ, hτ, heq.self_of_nhds.mp hzero, heq⟩

end

end ExactHoeffding
