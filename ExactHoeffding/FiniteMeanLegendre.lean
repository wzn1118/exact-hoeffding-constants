import ExactHoeffding.RealRecurrenceEquality
import ExactHoeffding.TiltedEndpoints
import ExactHoeffding.FiniteVarianceEnvelope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith

/-!
# Tilted-mean parametrization and exact finite Legendre optimizers

For a positive finite law on the ordered support `0,...,degree`, the tilted
mean is a strictly increasing bijection from `ℝ` onto the open support
interval.  The inverse is used to identify the optimizing tilt in the finite
Legendre transform.  Endpoint limits are retained explicitly, since they are
needed when the rate is evaluated at a support endpoint.
-/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- The uncentered finite Legendre transform of a positive recurrence law. -/
noncomputable def recurrenceLegendreRate (L : RealRecurrenceLaw) (v : ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ => t * v - Real.log (L.mgf t)))

private theorem recurrence_candidate_le_endpoint
    (L : RealRecurrenceLaw) (v t : ℝ) (hv0 : 0 ≤ v)
    (hvd : v ≤ (L.degree : ℝ)) :
    t * v - Real.log (L.mgf t) ≤
      max (-Real.log (L.mass 0)) (-Real.log (L.mass L.degree)) := by
  have h0 : 0 < L.mass 0 := L.mass_pos 0 (by omega)
  have hd : 0 < L.mass L.degree := L.mass_pos L.degree le_rfl
  have hmgf : 0 < L.mgf t := L.mgf_pos t
  by_cases ht : 0 ≤ t
  · have hterm : L.mass L.degree * Real.exp (t * (L.degree : ℝ)) ≤ L.mgf t := by
      unfold RealRecurrenceLaw.mgf finiteMGF
      change L.mass L.degree * Real.exp (t * (L.degree : ℝ)) ≤
        ∑ i ∈ Finset.range (L.degree + 1), L.mass i * Real.exp (t * (i : ℝ))
      have h := Finset.single_le_sum
        (s := Finset.range (L.degree + 1))
        (f := fun i : ℕ => L.mass i * Real.exp (t * (i : ℝ)))
        (fun i hi => mul_nonneg (L.mass_nonneg i hi) (Real.exp_pos _).le)
        (a := L.degree) (Finset.mem_range.mpr (by omega))
      simpa using h
    have hlog := Real.log_le_log
      (mul_pos hd (Real.exp_pos (t * (L.degree : ℝ)))) hterm
    rw [Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
    have htv : t * v ≤ t * (L.degree : ℝ) :=
      mul_le_mul_of_nonneg_left hvd ht
    have hbound : t * v - Real.log (L.mgf t) ≤ -Real.log (L.mass L.degree) := by
      linarith
    exact hbound.trans (le_max_right _ _)
  · have hterm : L.mass 0 ≤ L.mgf t := by
      unfold RealRecurrenceLaw.mgf finiteMGF
      change L.mass 0 ≤
        ∑ i ∈ Finset.range (L.degree + 1), L.mass i * Real.exp (t * (i : ℝ))
      have h0mem : 0 ∈ Finset.range (L.degree + 1) := Finset.mem_range.mpr (by omega)
      have h := Finset.single_le_sum
        (s := Finset.range (L.degree + 1))
        (f := fun i : ℕ => L.mass i * Real.exp (t * (i : ℝ)))
        (fun i hi => mul_nonneg (L.mass_nonneg i hi) (Real.exp_pos _).le)
        (a := 0) h0mem
      simpa only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] using h
    have hlog := Real.log_le_log h0 hterm
    have htv : t * v ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) hv0
    have hbound : t * v - Real.log (L.mgf t) ≤ -Real.log (L.mass 0) := by
      have hzero : Real.log (L.mass 0) ≤ Real.log (L.mgf t) := hlog
      linarith
    exact hbound.trans (le_max_left _ _)

/-- The finite Legendre candidates are bounded above on the closed support. -/
theorem recurrenceLegendreRate_bddAbove
    (L : RealRecurrenceLaw) (v : ℝ) (hv0 : 0 ≤ v)
    (hvd : v ≤ (L.degree : ℝ)) :
    BddAbove (Set.range (fun t : ℝ => t * v - Real.log (L.mgf t))) := by
  exact ⟨max (-Real.log (L.mass 0)) (-Real.log (L.mass L.degree)), by
    rintro z ⟨t, rfl⟩
    exact recurrence_candidate_le_endpoint L v t hv0 hvd⟩

private theorem recurrence_mgf_tendsto_atBot (L : RealRecurrenceLaw) :
    Tendsto L.mgf atBot (𝓝 (L.mass 0)) := by
  have h := finite_exp_sum_tendsto_atBot
    (Finset.range (L.degree + 1)) L.mass (fun i : ℕ => (i : ℝ)) 0
    (Finset.mem_range.mpr (by omega))
    (by
      intro i hi hne
      have hi0 : 0 < i := Nat.pos_of_ne_zero hne
      exact_mod_cast hi0)
  change Tendsto
    (fun t : ℝ => ∑ i ∈ Finset.range (L.degree + 1),
      L.mass i * Real.exp (t * (i : ℝ))) atBot (𝓝 (L.mass 0))
  convert h using 1
  · funext t
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    ring

private theorem recurrence_mgf_shifted_tendsto_atTop (L : RealRecurrenceLaw) :
    Tendsto
      (fun t : ℝ => L.mgf t * Real.exp (-t * (L.degree : ℝ)))
      atTop (𝓝 (L.mass L.degree)) := by
  let a : ℕ → ℝ := fun i => L.mass i
  let x : ℕ → ℝ := fun i => (i : ℝ)
  have h := finite_exp_sum_tendsto_atTop
    (Finset.range (L.degree + 1)) a x L.degree
    (Finset.mem_range.mpr (by omega))
    (by
      intro i hi hne
      have hiR : (i : ℝ) < (L.degree : ℝ) := by
        exact_mod_cast (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ
          (Finset.mem_range.mp hi)) hne)
      exact hiR)
  have hshift (t : ℝ) :
      (∑ i ∈ Finset.range (L.degree + 1), L.mass i *
          Real.exp (t * ((i : ℝ) - (L.degree : ℝ)))) =
        L.mgf t * Real.exp (-t * (L.degree : ℝ)) := by
    unfold RealRecurrenceLaw.mgf finiteMGF
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show t * ((i : ℝ) - (L.degree : ℝ)) =
      t * (i : ℝ) + (-t * (L.degree : ℝ)) by ring, Real.exp_add]
    ring
  have heq :
      (fun t : ℝ => L.mgf t * Real.exp (-t * (L.degree : ℝ))) =
        (fun t : ℝ => ∑ i ∈ Finset.range (L.degree + 1), L.mass i *
          Real.exp (t * ((i : ℝ) - (L.degree : ℝ)))) := by
    funext t
    exact (hshift t).symm
  rw [heq]
  simpa [a, x, id_eq] using h

private theorem recurrence_rate_candidate_tendsto_atBot (L : RealRecurrenceLaw) :
    Tendsto
      (fun t : ℝ => t * (0 : ℝ) - Real.log (L.mgf t))
      atBot (𝓝 (-Real.log (L.mass 0))) := by
  have h := (recurrence_mgf_tendsto_atBot L).log
    (L.mass_pos 0 (by omega)).ne'
  simpa using h.neg

private theorem recurrence_rate_candidate_tendsto_atTop (L : RealRecurrenceLaw) :
    Tendsto
      (fun t : ℝ => t * (L.degree : ℝ) - Real.log (L.mgf t))
      atTop (𝓝 (-Real.log (L.mass L.degree))) := by
  have h := (recurrence_mgf_shifted_tendsto_atTop L).log
    (L.mass_pos L.degree le_rfl).ne'
  have h' := h.neg
  have hid (t : ℝ) :
      -(Real.log (L.mgf t * Real.exp (-t * (L.degree : ℝ)))) =
        t * (L.degree : ℝ) - Real.log (L.mgf t) := by
    rw [Real.log_mul (ne_of_gt (L.mgf_pos t)) (Real.exp_pos _).ne', Real.log_exp]
    ring
  simpa only [hid] using h'

/-- The endpoint values of the finite Legendre transform are the negative logs
of the endpoint masses. -/
theorem recurrenceLegendreRate_zero
    (L : RealRecurrenceLaw) :
    recurrenceLegendreRate L 0 = -Real.log (L.mass 0) := by
  have hB : BddAbove (Set.range (fun t : ℝ =>
      t * (0 : ℝ) - Real.log (L.mgf t))) :=
    recurrenceLegendreRate_bddAbove L 0 (by norm_num) (by positivity)
  have hup : recurrenceLegendreRate L 0 ≤ -Real.log (L.mass 0) := by
    apply csSup_le
    · refine ⟨0, ⟨0, ?_⟩⟩
      change 0 * (0 : ℝ) - Real.log (L.mgf 0) = 0
      rw [L.mgf_zero, Real.log_one]
      norm_num
    · rintro z ⟨t, rfl⟩
      have h0 : 0 < L.mass 0 := L.mass_pos 0 (by omega)
      have hterm : L.mass 0 ≤ L.mgf t := by
        unfold RealRecurrenceLaw.mgf finiteMGF
        change L.mass 0 ≤
          ∑ i ∈ Finset.range (L.degree + 1), L.mass i * Real.exp (t * (i : ℝ))
        have h := Finset.single_le_sum
          (s := Finset.range (L.degree + 1))
          (f := fun i : ℕ => L.mass i * Real.exp (t * (i : ℝ)))
          (fun i hi => mul_nonneg (L.mass_nonneg i hi) (Real.exp_pos _).le)
          (a := 0) (Finset.mem_range.mpr (by omega))
        simpa using h
      have hlog := Real.log_le_log h0 hterm
      have : t * (0 : ℝ) - Real.log (L.mgf t) ≤ -Real.log (L.mass 0) := by
        linarith
      exact this
  have hlo : -Real.log (L.mass 0) ≤ recurrenceLegendreRate L 0 := by
    exact le_of_tendsto (recurrence_rate_candidate_tendsto_atBot L)
      (Filter.Eventually.of_forall (fun t =>
        le_csSup hB ⟨t, rfl⟩))
  exact le_antisymm hup hlo

/-- The upper endpoint value of the finite Legendre transform. -/
theorem recurrenceLegendreRate_degree
    (L : RealRecurrenceLaw) :
    recurrenceLegendreRate L (L.degree : ℝ) = -Real.log (L.mass L.degree) := by
  have hB : BddAbove (Set.range (fun t : ℝ =>
      t * (L.degree : ℝ) - Real.log (L.mgf t))) :=
    recurrenceLegendreRate_bddAbove L (L.degree : ℝ) (by positivity) le_rfl
  have hup : recurrenceLegendreRate L (L.degree : ℝ) ≤
      -Real.log (L.mass L.degree) := by
    apply csSup_le
    · refine ⟨0, ⟨0, ?_⟩⟩
      change 0 * (L.degree : ℝ) - Real.log (L.mgf 0) = 0
      rw [L.mgf_zero, Real.log_one]
      norm_num
    · rintro z ⟨t, rfl⟩
      have hd : 0 < L.mass L.degree := L.mass_pos L.degree le_rfl
      have hterm : L.mass L.degree * Real.exp (t * (L.degree : ℝ)) ≤ L.mgf t := by
        unfold RealRecurrenceLaw.mgf finiteMGF
        change L.mass L.degree * Real.exp (t * (L.degree : ℝ)) ≤
          ∑ i ∈ Finset.range (L.degree + 1), L.mass i * Real.exp (t * (i : ℝ))
        have h := Finset.single_le_sum
          (s := Finset.range (L.degree + 1))
          (f := fun i : ℕ => L.mass i * Real.exp (t * (i : ℝ)))
          (fun i hi => mul_nonneg (L.mass_nonneg i hi) (Real.exp_pos _).le)
          (a := L.degree) (Finset.mem_range.mpr (by omega))
        simpa using h
      have hlog := Real.log_le_log
        (mul_pos hd (Real.exp_pos (t * (L.degree : ℝ)))) hterm
      rw [Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
      linarith
  have hlo : -Real.log (L.mass L.degree) ≤
      recurrenceLegendreRate L (L.degree : ℝ) := by
    exact le_of_tendsto (recurrence_rate_candidate_tendsto_atTop L)
      (Filter.Eventually.of_forall (fun t =>
        le_csSup hB ⟨t, rfl⟩))
  exact le_antisymm hup hlo

/-- The tilted mean is strictly increasing on the whole real line. -/
theorem RealRecurrenceLaw.mean_strictMono
    (L : RealRecurrenceLaw) (hm : 0 < L.degree) : StrictMono L.mean := by
  exact strictMono_of_hasDerivAt_pos L.mean_hasDerivAt
    (fun t => L.variance_pos hm t)

/-- The tilted mean has the exact two endpoint limits. -/
theorem RealRecurrenceLaw.mean_tendsto_atBot
    (L : RealRecurrenceLaw) (hm : 0 < L.degree) :
    Tendsto L.mean atBot (𝓝 0) := by
  have h := L.expectation_tendsto_atBot (fun i => (i : ℝ))
  have heq : L.mean = (fun t : ℝ => L.expectation t (fun i => (i : ℝ))) := by
    funext t
    rfl
  rw [heq]
  simpa only [Nat.cast_zero] using h

/-- The tilted mean has the exact upper endpoint limit. -/
theorem RealRecurrenceLaw.mean_tendsto_atTop
    (L : RealRecurrenceLaw) (hm : 0 < L.degree) :
    Tendsto L.mean atTop (𝓝 (L.degree : ℝ)) := by
  have h := L.expectation_tendsto_atTop (fun i => (i : ℝ))
  have heq : L.mean = (fun t : ℝ => L.expectation t (fun i => (i : ℝ))) := by
    funext t
    rfl
  rw [heq]
  exact h

/-- The tilted mean is onto the open support interval. -/
theorem RealRecurrenceLaw.exists_unique_mean
    (L : RealRecurrenceLaw) (hm : 0 < L.degree) {u : ℝ}
    (hu0 : 0 < u) (hud : u < (L.degree : ℝ)) :
    ∃! t : ℝ, L.mean t = u := by
  have hcont : Continuous L.mean := continuous_iff_continuousAt.mpr
    (fun t => (L.mean_hasDerivAt t).continuousAt)
  have hbot := (tendsto_order.1 (L.mean_tendsto_atBot hm)).2 u hu0
  have htop := (tendsto_order.1 (L.mean_tendsto_atTop hm)).1 u hud
  obtain ⟨a, ha⟩ := eventually_atBot.mp hbot
  obtain ⟨b, hb⟩ := eventually_atTop.mp htop
  let left : ℝ := a
  let right : ℝ := max b (a + 1)
  have hleft : L.mean left < u := ha left le_rfl
  have hright : u < L.mean right := by
    have hbr : b ≤ right := le_max_left _ _
    exact hb right hbr
  have hlr : left ≤ right := by
    dsimp [left, right]
    have haa : a ≤ a + 1 := by linarith
    exact le_trans haa (le_max_right _ _)
  have him := intermediate_value_Icc hlr hcont.continuousOn
    ⟨le_of_lt hleft, le_of_lt hright⟩
  obtain ⟨t, ht, htu⟩ := him
  refine ⟨t, htu, ?_⟩
  intro s hs
  exact (L.mean_strictMono hm).injective (hs.trans htu.symm)

/-- The inverse tilted mean on the open support interval. -/
noncomputable def RealRecurrenceLaw.meanInverse
    (L : RealRecurrenceLaw) (u : ℝ) : ℝ :=
  if hu : u ∈ Ioo (0 : ℝ) (L.degree : ℝ) then
    Classical.choose (L.exists_unique_mean (by
      have hdegR : (0 : ℝ) < (L.degree : ℝ) := lt_trans hu.1 hu.2
      exact_mod_cast hdegR) hu.1 hu.2)
  else 0

@[simp] theorem RealRecurrenceLaw.meanInverse_spec
    (L : RealRecurrenceLaw) (hm : 0 < L.degree) {u : ℝ}
    (hu0 : 0 < u) (hud : u < (L.degree : ℝ)) :
    L.mean (L.meanInverse u) = u := by
  dsimp [RealRecurrenceLaw.meanInverse]
  rw [dif_pos ⟨hu0, hud⟩]
  exact (Classical.choose_spec
    (L.exists_unique_mean hm hu0 hud)).1

theorem RealRecurrenceLaw.meanInverse_unique
    (L : RealRecurrenceLaw) (hm : 0 < L.degree) {u : ℝ}
    (hu0 : 0 < u) (hud : u < (L.degree : ℝ)) {t : ℝ} :
    L.mean t = u ↔ t = L.meanInverse u := by
  constructor
  · intro ht
    exact (L.mean_strictMono hm).injective (ht.trans
      (L.meanInverse_spec hm hu0 hud).symm)
  · intro ht
    rw [ht, L.meanInverse_spec hm hu0 hud]

/-- The derivative of the Legendre candidate is the target mean minus the
current tilted mean. -/
private theorem recurrenceLegendreCandidate_hasDerivAt
    (L : RealRecurrenceLaw) (u s : ℝ) :
    HasDerivAt (fun z : ℝ => z * u - Real.log (L.mgf z))
      (u - L.mean s) s := by
  have hlog := finiteLogMGF_hasDerivAt
    (Finset.range (L.degree + 1)) L.mass (fun i => (i : ℝ))
    L.mass_nonneg L.mass_total s
  have h := (hasDerivAt_id s).const_mul u |>.sub hlog
  have hfun :
      (fun z : ℝ => z * u - Real.log (L.mgf z)) =
        ((fun y : ℝ => u * id y) -
          (fun y => Real.log (finiteMGF (Finset.range (L.degree + 1))
            L.mass (fun i => (i : ℝ)) y))) := by
    funext z
    dsimp [RealRecurrenceLaw.mgf]
    ring
  have hderiv : u - L.mean s =
      u * 1 - finiteTiltFirst (Finset.range (L.degree + 1)) L.mass
        (fun i => (i : ℝ)) s /
          finiteMGF (Finset.range (L.degree + 1)) L.mass
            (fun i => (i : ℝ)) s := by
    dsimp [RealRecurrenceLaw.mean, RealRecurrenceLaw.mgf]
    ring
  rw [hfun]
  exact h.congr_deriv hderiv.symm

private theorem recurrenceLegendreCandidate_continuous
    (L : RealRecurrenceLaw) (u : ℝ) :
    Continuous (fun s : ℝ => s * u - Real.log (L.mgf s)) := by
  have hlog : Continuous (fun s : ℝ => Real.log (L.mgf s)) :=
    continuous_iff_continuousAt.mpr (fun s =>
      (finiteLogMGF_hasDerivAt
        (Finset.range (L.degree + 1)) L.mass (fun i => (i : ℝ))
        L.mass_nonneg L.mass_total s).continuousAt)
  exact (continuous_id.mul continuous_const).sub hlog

/-- Every finite Legendre candidate is maximized at the tilt producing its
interior target mean. -/
theorem recurrenceLegendreCandidate_max_at_mean
    (L : RealRecurrenceLaw) (hm : 0 < L.degree) {u : ℝ}
    (hu0 : 0 < u) (hud : u < (L.degree : ℝ)) :
    ∀ s : ℝ,
      s * u - Real.log (L.mgf s) ≤
        L.meanInverse u * u - Real.log (L.mgf (L.meanInverse u)) := by
  let t₀ : ℝ := L.meanInverse u
  have htmean : L.mean t₀ = u := L.meanInverse_spec hm hu0 hud
  have hFc : Continuous (fun s : ℝ => s * u - Real.log (L.mgf s)) :=
    recurrenceLegendreCandidate_continuous L u
  have hleft : MonotoneOn
      (fun s : ℝ => s * u - Real.log (L.mgf s)) (Iic t₀) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic t₀) hFc.continuousOn
      (fun s hs => (recurrenceLegendreCandidate_hasDerivAt L u s).hasDerivWithinAt)
    intro s hs
    rw [interior_Iic] at hs
    have hmono := L.mean_strictMono hm
    have hmean : L.mean s ≤ u := by
      exact (hmono hs).le.trans_eq htmean
    linarith
  have hright : AntitoneOn
      (fun s : ℝ => s * u - Real.log (L.mgf s)) (Ici t₀) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici t₀) hFc.continuousOn
      (fun s hs => (recurrenceLegendreCandidate_hasDerivAt L u s).hasDerivWithinAt)
    intro s hs
    rw [interior_Ici] at hs
    have hmono := L.mean_strictMono hm
    have hmean : u ≤ L.mean s := by
      exact htmean ▸ (hmono hs).le
    linarith
  intro s
  by_cases hs : s ≤ t₀
  · exact hleft (mem_Iic.mpr hs) (mem_Iic.mpr le_rfl) hs
  · have hst : t₀ ≤ s := le_of_not_ge hs
    exact hright (mem_Ici.mpr le_rfl) (mem_Ici.mpr hst) hst

/-- The interior finite Legendre rate is attained at the unique inverse tilted
mean, with no assumed rate comparison. -/
theorem recurrenceLegendreRate_at_mean
    (L : RealRecurrenceLaw) (hm : 0 < L.degree) {u : ℝ}
    (hu0 : 0 < u) (hud : u < (L.degree : ℝ)) :
    recurrenceLegendreRate L u =
      L.meanInverse u * u - Real.log (L.mgf (L.meanInverse u)) := by
  have hB := recurrenceLegendreRate_bddAbove L u hu0.le hud.le
  apply le_antisymm
  · apply csSup_le
    · refine ⟨0, ⟨0, ?_⟩⟩
      change 0 * u - Real.log (L.mgf 0) = 0
      rw [L.mgf_zero, Real.log_one]
      ring
    · rintro z ⟨s, rfl⟩
      exact recurrenceLegendreCandidate_max_at_mean L hm hu0 hud s
  · exact le_csSup hB ⟨L.meanInverse u, rfl⟩


/-- The mean-coordinate envelope rate on the upper side of the ordinary mean. -/
noncomputable def recurrenceMeanEnvelopeRateRight
    (L : RealRecurrenceLaw) (Q : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ s : ℝ in L.mean 0..u, (u - s) / Q s

/-- A valid positive tilted-variance envelope gives the full upper-side
mean-coordinate Legendre comparison.  The proof uses the actual inverse tilt,
then changes variables from tilt to tilted mean; the target integral is not
assumed. -/
theorem recurrenceLegendreRate_ge_meanEnvelopeRateRight
    (L : RealRecurrenceLaw) (hm : 0 < L.degree)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ s ∈ Icc (0 : ℝ) (L.degree : ℝ), 0 < Q s)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    {u : ℝ} (hu0 : 0 < u) (hud : u < (L.degree : ℝ))
    (hμu : L.mean 0 ≤ u) :
    recurrenceMeanEnvelopeRateRight L Q u ≤ recurrenceLegendreRate L u := by
  let t : ℝ := L.meanInverse u
  have htmean : L.mean t = u := L.meanInverse_spec hm hu0 hud
  have ht0 : 0 ≤ t := by
    by_contra hnt
    have hlt : t < 0 := lt_of_not_ge hnt
    have hmono := L.mean_strictMono hm
    have hmeanlt : L.mean t < L.mean 0 := hmono hlt
    linarith [hμu, htmean]
  have hmean_cont : Continuous L.mean := continuous_iff_continuousAt.mpr
    (fun s => (L.mean_hasDerivAt s).continuousAt)
  have hvar_cont : Continuous L.variance := continuous_iff_continuousAt.mpr
    (fun s => (L.variance_differentiableAt s).continuousAt)
  let A : ℝ → ℝ := fun s =>
    ((u - L.mean s) / Q (L.mean s)) * L.variance s
  let B : ℝ → ℝ := fun s => u - L.mean s
  have hAB : ∀ s ∈ Icc (0 : ℝ) t, A s ≤ B s := by
    intro s hs
    have hms0 : 0 ≤ L.mean s := (L.mean_pos hm s).le
    have hmsd : L.mean s ≤ (L.degree : ℝ) := (L.mean_lt hm s).le
    have hq : 0 < Q (L.mean s) := hQpos _ ⟨hms0, hmsd⟩
    have hdiff : 0 ≤ u - L.mean s := by
      have hmono := L.mean_strictMono hm
      have hle : s ≤ t := hs.2
      have hmean : L.mean s ≤ L.mean t := hmono.monotone hle
      linarith [htmean]
    have hv := hV s
    dsimp [A, B]
    have hdiv : (u - L.mean s) * L.variance s / Q (L.mean s) ≤
        u - L.mean s := by
      apply (div_le_iff₀ hq).2
      exact mul_le_mul_of_nonneg_left hv hdiff
    calc
      (u - L.mean s) / Q (L.mean s) * L.variance s =
          (u - L.mean s) * L.variance s / Q (L.mean s) := by ring
      _ ≤ u - L.mean s := hdiv
  have hAcont : ContinuousOn A (Icc (0 : ℝ) t) := by
    have hmc : ContinuousOn (fun s : ℝ => Q (L.mean s)) (Icc (0 : ℝ) t) :=
      hQ.continuousOn.comp hmean_cont.continuousOn (fun s hs => mem_univ _)
    have hqne : ∀ s ∈ Icc (0 : ℝ) t, Q (L.mean s) ≠ 0 := by
      intro s hs
      exact ne_of_gt (hQpos _ ⟨(L.mean_pos hm s).le, (L.mean_lt hm s).le⟩)
    have hquot : ContinuousOn
        (fun s => (u - L.mean s) / Q (L.mean s)) (Icc (0 : ℝ) t) :=
      (continuousOn_const.sub hmean_cont.continuousOn).div hmc hqne
    exact hquot.mul hvar_cont.continuousOn
  have hBcont : ContinuousOn B (Icc (0 : ℝ) t) := by
    exact continuousOn_const.sub hmean_cont.continuousOn
  have hAcont' : ContinuousOn A (uIcc (0 : ℝ) t) := by
    rw [uIcc_of_le ht0]
    exact hAcont
  have hBcont' : ContinuousOn B (uIcc (0 : ℝ) t) := by
    rw [uIcc_of_le ht0]
    exact hBcont
  have hAi : IntervalIntegrable A MeasureTheory.volume 0 t :=
    hAcont'.intervalIntegrable
  have hBi : IntervalIntegrable B MeasureTheory.volume 0 t :=
    hBcont'.intervalIntegrable
  have hineq :
      (∫ s : ℝ in (0 : ℝ)..t, A s) ≤
        ∫ s : ℝ in (0 : ℝ)..t, B s := by
    apply intervalIntegral.integral_mono_on ht0 hAi hBi
    exact hAB
  have hchange0 := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := t) (f := L.mean) (f' := L.variance)
    (g := fun s : ℝ => (u - s) / Q s)
    hmean_cont.continuousOn
    (fun s hs => L.mean_hasDerivAt s)
    (fun s hs => (L.variance_pos hm s).le)
  have hchange :
      recurrenceMeanEnvelopeRateRight L Q u =
        ∫ s : ℝ in (0 : ℝ)..t, A s := by
    dsimp [recurrenceMeanEnvelopeRateRight, A]
    calc
      (∫ s : ℝ in L.mean 0..u, (u - s) / Q s) =
          ∫ s : ℝ in L.mean 0..L.mean t, (u - s) / Q s := by rw [htmean]
      _ = ∫ s : ℝ in (0 : ℝ)..t,
          ((fun r : ℝ => (u - r) / Q r) ∘ L.mean) s * L.variance s :=
        hchange0.symm
      _ = ∫ s : ℝ in (0 : ℝ)..t,
          ((u - L.mean s) / Q (L.mean s)) * L.variance s := by
        rfl
  have hGint : IntervalIntegrable B MeasureTheory.volume 0 t := hBi
  have hfund0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => recurrenceLegendreCandidate_hasDerivAt L u s) hGint
  have hfund :
      (∫ s : ℝ in (0 : ℝ)..t, B s) =
        t * u - Real.log (L.mgf t) := by
    dsimp [B] at hfund0 ⊢
    rw [hfund0, L.mgf_zero, Real.log_one]
    ring
  have hrate : t * u - Real.log (L.mgf t) ≤ recurrenceLegendreRate L u := by
    exact le_csSup (recurrenceLegendreRate_bddAbove L u hu0.le hud.le) ⟨t, rfl⟩
  calc
    recurrenceMeanEnvelopeRateRight L Q u = ∫ s : ℝ in (0 : ℝ)..t, A s := hchange
    _ ≤ ∫ s : ℝ in (0 : ℝ)..t, B s := hineq
    _ = t * u - Real.log (L.mgf t) := hfund
    _ ≤ recurrenceLegendreRate L u := hrate


/-- The mean-coordinate envelope rate on the lower side of the ordinary mean. -/
noncomputable def recurrenceMeanEnvelopeRateLeft
    (L : RealRecurrenceLaw) (Q : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ s : ℝ in u..L.mean 0, (s - u) / Q s

/-- The lower-side mean-coordinate comparison, including the reversed tilt
orientation. -/
theorem recurrenceLegendreRate_ge_meanEnvelopeRateLeft
    (L : RealRecurrenceLaw) (hm : 0 < L.degree)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ s ∈ Icc (0 : ℝ) (L.degree : ℝ), 0 < Q s)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    {u : ℝ} (hu0 : 0 < u) (hud : u < (L.degree : ℝ))
    (hμu : u ≤ L.mean 0) :
    recurrenceMeanEnvelopeRateLeft L Q u ≤ recurrenceLegendreRate L u := by
  let t : ℝ := L.meanInverse u
  have htmean : L.mean t = u := L.meanInverse_spec hm hu0 hud
  have ht0 : t ≤ 0 := by
    by_contra hnt
    have hgt : 0 < t := lt_of_not_ge hnt
    have hmono := L.mean_strictMono hm
    have hmeanlt : L.mean 0 < L.mean t := hmono hgt
    linarith [hμu, htmean]
  have hmean_cont : Continuous L.mean := continuous_iff_continuousAt.mpr
    (fun s => (L.mean_hasDerivAt s).continuousAt)
  have hvar_cont : Continuous L.variance := continuous_iff_continuousAt.mpr
    (fun s => (L.variance_differentiableAt s).continuousAt)
  let A : ℝ → ℝ := fun s =>
    ((L.mean s - u) / Q (L.mean s)) * L.variance s
  let B : ℝ → ℝ := fun s => L.mean s - u
  have hAB : ∀ s ∈ Icc t (0 : ℝ), A s ≤ B s := by
    intro s hs
    have hms0 : 0 ≤ L.mean s := (L.mean_pos hm s).le
    have hmsd : L.mean s ≤ (L.degree : ℝ) := (L.mean_lt hm s).le
    have hq : 0 < Q (L.mean s) := hQpos _ ⟨hms0, hmsd⟩
    have hdiff : 0 ≤ L.mean s - u := by
      have hmono := L.mean_strictMono hm
      have hle : t ≤ s := hs.1
      have hmean : L.mean t ≤ L.mean s := hmono.monotone hle
      linarith [htmean]
    have hv := hV s
    dsimp [A, B]
    have hdiv : (L.mean s - u) * L.variance s / Q (L.mean s) ≤
        L.mean s - u := by
      apply (div_le_iff₀ hq).2
      exact mul_le_mul_of_nonneg_left hv hdiff
    calc
      (L.mean s - u) / Q (L.mean s) * L.variance s =
          (L.mean s - u) * L.variance s / Q (L.mean s) := by ring
      _ ≤ L.mean s - u := hdiv
  have hAcont : ContinuousOn A (Icc t (0 : ℝ)) := by
    have hmc : ContinuousOn (fun s => Q (L.mean s)) (Icc t (0 : ℝ)) :=
      hQ.continuousOn.comp hmean_cont.continuousOn (fun s hs => mem_univ _)
    have hqne : ∀ s ∈ Icc t (0 : ℝ), Q (L.mean s) ≠ 0 := by
      intro s hs
      exact ne_of_gt (hQpos _ ⟨(L.mean_pos hm s).le, (L.mean_lt hm s).le⟩)
    have hquot : ContinuousOn
        (fun s => (L.mean s - u) / Q (L.mean s)) (Icc t (0 : ℝ)) :=
      (hmean_cont.continuousOn.sub continuousOn_const).div hmc hqne
    exact hquot.mul hvar_cont.continuousOn
  have hBcont : ContinuousOn B (Icc t (0 : ℝ)) := by
    exact hmean_cont.continuousOn.sub continuousOn_const
  have hAcont' : ContinuousOn A (uIcc t (0 : ℝ)) := by
    rw [uIcc_of_le ht0]
    exact hAcont
  have hBcont' : ContinuousOn B (uIcc t (0 : ℝ)) := by
    rw [uIcc_of_le ht0]
    exact hBcont
  have hAi : IntervalIntegrable A MeasureTheory.volume t 0 :=
    hAcont'.intervalIntegrable
  have hBi : IntervalIntegrable B MeasureTheory.volume t 0 :=
    hBcont'.intervalIntegrable
  have hineq :
      (∫ s : ℝ in t..(0 : ℝ), A s) ≤
        ∫ s : ℝ in t..(0 : ℝ), B s := by
    apply intervalIntegral.integral_mono_on (by linarith) hAi hBi
    exact hAB
  have hchange0 := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := t) (b := (0 : ℝ)) (f := L.mean) (f' := L.variance)
    (g := fun s : ℝ => (s - u) / Q s)
    hmean_cont.continuousOn
    (fun s hs => L.mean_hasDerivAt s)
    (fun s hs => (L.variance_pos hm s).le)
  have hchange :
      recurrenceMeanEnvelopeRateLeft L Q u =
        ∫ s : ℝ in t..(0 : ℝ), A s := by
    dsimp [recurrenceMeanEnvelopeRateLeft, A]
    calc
      (∫ s : ℝ in u..L.mean 0, (s - u) / Q s) =
          ∫ s : ℝ in L.mean t..L.mean 0, (s - u) / Q s := by rw [htmean]
      _ = ∫ s : ℝ in t..(0 : ℝ),
          ((fun r : ℝ => (r - u) / Q r) ∘ L.mean) s * L.variance s :=
        hchange0.symm
      _ = ∫ s : ℝ in t..(0 : ℝ),
          ((L.mean s - u) / Q (L.mean s)) * L.variance s := by
        rfl
  have hUi : IntervalIntegrable (fun s : ℝ => u - L.mean s)
      MeasureTheory.volume t 0 := by
    convert hBi.neg using 1
    funext s
    dsimp [B]
    ring
  have hfund0 := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => recurrenceLegendreCandidate_hasDerivAt L u s) hUi
  have hfund :
      (∫ s : ℝ in t..(0 : ℝ), B s) =
        t * u - Real.log (L.mgf t) := by
    have hneg :
        (∫ s : ℝ in t..(0 : ℝ), B s) =
          - (∫ s : ℝ in t..(0 : ℝ), u - L.mean s) := by
      simp only [B]
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext s
      ring
    rw [hneg, hfund0, L.mgf_zero, Real.log_one]
    ring
  have hrate : t * u - Real.log (L.mgf t) ≤ recurrenceLegendreRate L u := by
    exact le_csSup (recurrenceLegendreRate_bddAbove L u hu0.le hud.le) ⟨t, rfl⟩
  calc
    recurrenceMeanEnvelopeRateLeft L Q u = ∫ s : ℝ in t..(0 : ℝ), A s := hchange
    _ ≤ ∫ s : ℝ in t..(0 : ℝ), B s := hineq
    _ = t * u - Real.log (L.mgf t) := hfund
    _ ≤ recurrenceLegendreRate L u := hrate

end
end ExactHoeffding
