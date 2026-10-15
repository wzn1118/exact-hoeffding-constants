import ExactHoeffding.RealMarginGlobalOptimizer
import ExactHoeffding.JointParameterSymmetry

/-! # Exact imbalance reflection of actual fixed-population optimizers -/
namespace ExactHoeffding
noncomputable section
open Filter
open scoped Topology

/-- Complement symmetry for the entire actual removable objective. -/
theorem realMarginProxy_reflection (N m:ℕ) (hN:5≤N) (hNm:2*m≤N)
    (d:ℝ) (hd:|d|<1/(N:ℝ)) (t:ℝ) :
    realMarginProxy N m (-d) t = realMarginProxy N m d (-t) := by
  have hden := (realMarginPopulationDenom_pos N m (by omega) (by omega)).ne'
  by_cases ht:t=0
  · subst t
    rw [neg_zero,realMarginProxy_zero N m (-d) hden,realMarginProxy_zero N m d hden,
      margin_cumulant2_closed N m hN,margin_cumulant2_closed N m hN]
    ring
  obtain ⟨hw,hs⟩ := realMarginMass_near_balanced_probability N m (by omega) hNm d hd
  have hM := finiteMGF_pos_of_normalized (Finset.range (m+1))
    (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) (fun i=>(i:ℝ)) hw hs (-t)
  have href := realMarginMGF_reflection m (1/(N:ℝ)) ((1-d)/2) t
  have hp : 1-(1-d)/2=(1-(-d))/2 := by ring
  rw [hp] at href
  rw [realMarginProxy_eq_quotient N m (-d) t hden ht,
    realMarginProxy_eq_quotient N m d (-t) hden (neg_ne_zero.mpr ht)]
  unfold realMarginCenteredLogMGF
  rw [href,Real.log_mul (Real.exp_ne_zero _) hM.ne',Real.log_exp]
  ring

/-- The actual unique global branch is odd in real imbalance. -/
theorem realMarginProxy_global_branch_odd (N m:ℕ) (hN:5≤N) (hNm:2*m≤N)
    (τ:ℝ→ℝ)
    (hglobal:∀ᶠ d in 𝓝 (0:ℝ), ∀t:ℝ,
      (∀u:ℝ,realMarginProxy N m d u≤realMarginProxy N m d t) ↔ t=τ d) :
    ∀ᶠ d in 𝓝 (0:ℝ), τ (-d) = -τ d := by
  have hd : ∀ᶠ d in 𝓝 (0:ℝ), |d|<1/(N:ℝ) :=
    continuousAt_id.abs.eventually_lt continuousAt_const (by
      have : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
      simpa only [id_eq, abs_zero] using (show (0:ℝ)<1/(N:ℝ) by positivity))
  have hneg : Tendsto (fun d:ℝ=> -d) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun d:ℝ=> -d) 0 := by fun_prop
    simpa only [neg_zero] using hc.tendsto
  filter_upwards [hglobal,hneg.eventually hglobal,hd] with d hg hng hd
  have hm : ∀u:ℝ,realMarginProxy N m (-d) u≤realMarginProxy N m (-d) (-τ d) := by
    intro u
    rw [realMarginProxy_reflection N m hN hNm d hd u,
      realMarginProxy_reflection N m hN hNm d hd (-τ d),neg_neg]
    exact (hg (τ d)).mpr rfl (-u)
  exact ((hng (-τ d)).mp hm).symm

/-- Reflection makes the actual optimized value an even analytic germ. -/
theorem realMarginProxy_optimized_value_even (N m:ℕ) (hN:5≤N) (hNm:2*m≤N)
    (τ:ℝ→ℝ) (hodd:∀ᶠ d in 𝓝 (0:ℝ),τ (-d)= -τ d) :
    ∀ᶠ d in 𝓝 (0:ℝ),realMarginProxy N m (-d) (τ (-d))=realMarginProxy N m d (τ d) := by
  have hd : ∀ᶠ d in 𝓝 (0:ℝ), |d|<1/(N:ℝ) :=
    continuousAt_id.abs.eventually_lt continuousAt_const (by
      have : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
      simpa only [id_eq, abs_zero] using (show (0:ℝ)<1/(N:ℝ) by positivity))
  filter_upwards [hodd,hd] with d ho hd
  rw [ho,realMarginProxy_reflection N m hN hNm d hd (-τ d),neg_neg]

end
end ExactHoeffding
