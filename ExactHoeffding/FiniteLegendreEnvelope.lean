import ExactHoeffding.FiniteVarianceEnvelope

namespace ExactHoeffding
noncomputable section

open Set

/-- The Legendre rate of a normalized finite law in a centered mean
coordinate. -/
def finiteLegendreRate {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (v : ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ =>
    t * v - Real.log (finiteMGF s w x t)))

/-- The Legendre rate obtained by replacing the true centered log-MGF by the
integrated variance envelope along its actual tilted mean curve. -/
def finiteEnvelopeLegendreRate {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (Q : ℝ → ℝ) (v : ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ =>
    t * v - t ^ 2 * ∫ u : ℝ in (0 : ℝ)..1,
      (1 - u) * Q (finiteEnvelopeTiltMean s w x (u * t))))

/-- The finite-law Legendre rate dominates the rate obtained from any valid
variance envelope.  The proof compares every tilt candidate before taking
both suprema; no target rate comparison is assumed. -/
theorem finiteLegendreRate_ge_finiteEnvelopeLegendreRate
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * x i = 0)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hV : ∀ u : ℝ,
      finiteEnvelopeTiltVariance s w x u ≤
        Q (finiteEnvelopeTiltMean s w x u))
    (v : ℝ)
    (hI : BddAbove (Set.range (fun t : ℝ =>
      t * v - Real.log (finiteMGF s w x t)))) :
    finiteEnvelopeLegendreRate s w x Q v ≤ finiteLegendreRate s w x v := by
  unfold finiteEnvelopeLegendreRate finiteLegendreRate
  apply csSup_le
  · refine ⟨0, ?_⟩
    refine ⟨0, ?_⟩
    simp
  · rintro y ⟨t, rfl⟩
    have hlog := finiteLogMGF_variance_envelope_integral
      s w x hw hs hmean Q hQ hV t
    have henv : t * v - t ^ 2 *
        ∫ u : ℝ in (0 : ℝ)..1,
          (1 - u) * Q (finiteEnvelopeTiltMean s w x (u * t)) ≤
        t * v - Real.log (finiteMGF s w x t) := by
      linarith
    have hrate := le_csSup hI ⟨t, rfl⟩
    exact henv.trans hrate

end
end ExactHoeffding
