import ExactHoeffding.RealMarginGlobalOptimizer
import ExactHoeffding.OptimalProxy

/-! # An actual maximizing tilt realizes the least global quadratic proxy -/
namespace ExactHoeffding
noncomputable section
open Filter
open scoped Topology

/-- The completed actual objective bounds every quadratic proxy also at the
removable origin, by continuity from nonzero tilts. -/
theorem realMarginProxy_le_of_quadratic (N m:ℕ) (hN:5≤N) (hNm:2*m≤N)
    (d:ℝ) (hcont:ContinuousAt (realMarginProxy N m d) 0) (D:ℝ)
    (hD:IsQuadraticProxy (realMarginCenteredLogMGF N m d) D) (t:ℝ) :
    realMarginProxy N m d t≤D := by
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have hnonzero (u:ℝ) (hu:u≠0) : realMarginProxy N m d u≤D := by
    rw [realMarginProxy_eq_quotient N m d u hden hu]
    apply (div_le_iff₀ (sq_pos_of_ne_zero hu)).mpr
    have h:=hD u
    nlinarith
  by_cases ht:t=0
  · subst t
    have hlim : Tendsto (realMarginProxy N m d) (𝓝[≠] (0:ℝ))
        (𝓝 (realMarginProxy N m d 0)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    exact le_of_tendsto hlim (by
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hnonzero u hu)
  · exact hnonzero t ht

/-- A true actual global maximum is the sharp quadratic proxy. -/
theorem realMarginProxy_isOptimal_of_global (N m:ℕ) (hN:5≤N) (hNm:2*m≤N)
    (d t:ℝ) (hcont:ContinuousAt (realMarginProxy N m d) 0)
    (hmax:∀u:ℝ,realMarginProxy N m d u≤realMarginProxy N m d t) :
    IsOptimalQuadraticProxy (realMarginCenteredLogMGF N m d) (realMarginProxy N m d t) := by
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  refine ⟨?_,fun D hD=>realMarginProxy_le_of_quadratic N m hN hNm d hcont D hD t⟩
  intro u
  rw [realMarginProxy_factor N m d u hden]
  nlinarith [mul_le_mul_of_nonneg_left (hmax u) (sq_nonneg u)]

/-- The actual constructed analytic branch gives the least proxy itself,
including imbalances at which its maximizing tilt is zero. -/
theorem realMarginProxy_optimal_value_eventually (N m:ℕ) (hN:5≤N) (hNm:2*m≤N)
    (τ:ℝ→ℝ) (hglobal:∀ᶠ d in 𝓝 (0:ℝ),∀t:ℝ,
      (∀u:ℝ,realMarginProxy N m d u≤realMarginProxy N m d t) ↔ t=τ d) :
    ∀ᶠ d in 𝓝 (0:ℝ),
      IsOptimalQuadraticProxy (realMarginCenteredLogMGF N m d) (realMarginProxy N m d (τ d)) ∧
      optimalProxy (realMarginCenteredLogMGF N m d)=realMarginProxy N m d (τ d) := by
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  have ha := realMarginProxy_joint_analytic N m hden
  have hins : ContinuousAt (fun d:ℝ=>(d,(0:ℝ))) 0 := continuousAt_id.prodMk continuousAt_const
  filter_upwards [hglobal,hins.eventually ha.eventually_analyticAt] with d hg hd
  have hc : ContinuousAt (realMarginProxy N m d) 0 :=
    (hd.comp_of_eq (f:=fun t:ℝ=>(d,t)) (analyticAt_const.prod analyticAt_id) rfl).continuousAt
  have hopt := realMarginProxy_isOptimal_of_global N m hN hNm d (τ d) hc ((hg (τ d)).mpr rfl)
  refine ⟨hopt,optimalProxy_eq_of_optimal _ ?_ _ hopt⟩
  rw [realMarginProxy_factor N m d 0 hden]
  ring

end
end ExactHoeffding
