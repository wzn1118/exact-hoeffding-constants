import ExactHoeffding.JointCoordinateFactor

/-! # Continuous removal of a population coordinate along a whole parameter axis -/

namespace ExactHoeffding
noncomputable section
open Filter Set Metric
open scoped Topology

/-- The population quotient with its actual directional derivative on the axis. -/
def populationSlope (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1=0 then parameterPartial F (1,0) p else F p/p.1

theorem continuous_germ_extension_at (G : ℝ × ℝ → ℝ) (p₀ : ℝ × ℝ)
    (hG : ∀ᶠ p in 𝓝 p₀, ContinuousAt G p) :
    ∃ g : ℝ × ℝ → ℝ, Continuous g ∧ g =ᶠ[𝓝 p₀] G := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hG
  let K : Set (ℝ × ℝ) := closedBall p₀ (r/2)
  have hK : ∀ p ∈ K, ContinuousAt G p := by
    intro p hp
    exact hball (lt_of_le_of_lt hp (half_lt_self hr))
  let f : C(K,ℝ) := ⟨fun p => G p,continuousOn_iff_continuous_domRestrict.mp
    (fun p hp => (hK p hp).continuousWithinAt)⟩
  obtain ⟨g,hg⟩ := f.exists_restrict_eq isClosed_closedBall
  refine ⟨g,g.continuous,?_⟩
  filter_upwards [closedBall_mem_nhds p₀ (half_pos hr)] with p hp
  exact congrArg (fun h : C(K,ℝ) => h ⟨p,hp⟩) hg

theorem population_grid_eventually (P : ℝ × ℝ → Prop) (d₀ : ℝ)
    (hP : ∀ᶠ p in 𝓝 ((0 : ℝ),d₀), P p) :
    ∀ᶠ p in 𝓝 ((0 : ℝ),d₀), ∀ r ∈ Icc (0 : ℝ) 1, P (r*p.1,p.2) := by
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro r _
  have hc : ContinuousAt (fun u : (ℝ × ℝ) × ℝ => (u.2*u.1.1,u.1.2)) ((0,d₀),r) := by
    fun_prop
  have ht : Tendsto (fun u : (ℝ × ℝ) × ℝ => (u.2*u.1.1,u.1.2))
      (𝓝 ((0,d₀),r)) (𝓝 (0,d₀)) := by
    simpa only [mul_zero] using hc.tendsto
  exact ht.eventually hP

/-- Joint analyticity and exact axis cancellation remove division by the
population coordinate continuously, including parameter variation along the axis. -/
theorem populationSlope_continuousAt_axis (F : ℝ × ℝ → ℝ) (d₀ : ℝ)
    (hF : AnalyticAt ℝ F (0,d₀))
    (haxis : ∀ᶠ d in 𝓝 d₀, F (0,d)=0) :
    ContinuousAt (populationSlope F) (0,d₀) := by
  obtain ⟨g,hg,hgerm⟩ := continuous_germ_extension_at (parameterPartial F (1,0)) (0,d₀)
    (hF.eventually_analyticAt.mono fun p hp => (parameterPartial_analytic F _ p hp).continuousAt)
  let J : ℝ × ℝ → ℝ := fun p => ∫ r in (0 : ℝ)..1, g (r*p.1,p.2)
  have hJ : Continuous J := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hg.comp (by fun_prop)
  apply hJ.continuousAt.congr_of_eventuallyEq
  have hA := population_grid_eventually _ d₀ hF.eventually_analyticAt
  have hG := population_grid_eventually _ d₀ hgerm
  have hZ : ∀ᶠ p in 𝓝 ((0 : ℝ),d₀), F (0,p.2)=0 :=
    (continuousAt_snd : ContinuousAt (fun p : ℝ × ℝ => p.2) (0,d₀)).tendsto.eventually haxis
  filter_upwards [hA,hG,hZ] with p hp hgp hz
  symm
  have hid : p.1*J p=F p := by
    have hcont : ContinuousOn (fun r : ℝ => parameterPartial F (1,0) (r*p.1,p.2)) (Icc 0 1) := by
      intro r hr
      exact ((parameterPartial_analytic F _ _ (hp r hr)).continuousAt.comp_of_eq
        (by fun_prop : ContinuousAt (fun x : ℝ => (x*p.1,p.2)) r) rfl).continuousWithinAt
    have hder : ∀ r ∈ Icc (0 : ℝ) 1,
        HasDerivAt (fun e : ℝ => F (e,p.2)) (parameterPartial F (1,0) (r*p.1,p.2)) (r*p.1) := by
      intro r hr
      exact (hp r hr).differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq _
        ((hasDerivAt_id _).prodMk (hasDerivAt_const _ _)) rfl
    have h := intervalIntegral.integral_unitInterval_deriv_eq_sub
      (z₀ := (0 : ℝ)) (z₁ := p.1) (f := fun e => F (e,p.2))
      (f' := fun e => parameterPartial F (1,0) (e,p.2))
      (by simpa only [zero_add,smul_eq_mul] using hcont)
      (by simpa only [zero_add,smul_eq_mul] using hder)
    simp only [zero_add,hz,sub_zero,smul_eq_mul] at h
    rw [← h]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    exact hgp r (by simpa only [uIcc_of_le zero_le_one] using hr)
  unfold populationSlope
  split_ifs with he
  · dsimp [J]
    have hconst : (fun r : ℝ => g (r*p.1,p.2)) = fun _ => parameterPartial F (1,0) p := by
      funext r
      rw [he,mul_zero]
      have h := hgp 0 (by simp)
      have hpz : p=((0 : ℝ),p.2) := by ext <;> simp only [he]
      rw [hpz]
      simpa only [zero_mul] using h
    rw [hconst]
    simp
  · exact (eq_div_iff he).mpr (by simpa only [mul_comm] using hid)

end
end ExactHoeffding
