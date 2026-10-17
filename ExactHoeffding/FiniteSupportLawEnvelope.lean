import ExactHoeffding.FiniteSupportOpenEnvelope
import ExactHoeffding.FiniteSupportMeanEnvelopeStrict
import ExactHoeffding.FiniteSupportEndpointEnvelope
import ExactHoeffding.FiniteSupportTiltCurveOfLaw
import ExactHoeffding.FiniteSupportLawVariance

/-! # Direct finite-law interfaces for the mean-coordinate envelope theorem

The abstract change-of-variables proof is instantiated here at an actual
finite weighted probability law. Positive mass at two distinct endpoint atoms
proves strict positivity of every tilted variance; endpoint statements retain
the explicit one-sided limit hypotheses from the manuscript. -/

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- Direct right-interior comparison for an actual finite weighted law. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateRight
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc (L.value L.loIndex - L.mean0)
        (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    {v : ℝ} (hv0 : 0 ≤ v) (hvhi : v < L.value L.hiIndex - L.mean0) :
    finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q v ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v := by
  exact finiteSupportLegendreRate_ge_meanEnvelopeRateRight
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hv0 hvhi

/-- Direct left-interior comparison for an actual finite weighted law. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateLeft
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc (L.value L.loIndex - L.mean0)
        (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    {v : ℝ} (hvlo : L.value L.loIndex - L.mean0 < v) (hv0 : v ≤ 0) :
    finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q v ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v := by
  exact finiteSupportLegendreRate_ge_meanEnvelopeRateLeft
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hvlo hv0

/-- Direct strict right comparison for an actual finite weighted law. -/
theorem finiteSupportLawData_rate_gt_meanEnvelopeRateRight
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc (L.value L.loIndex - L.mean0)
        (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    {v : ℝ} (hv0 : 0 < v) (hvhi : v < L.value L.hiIndex - L.mean0)
    (hstrict : ∃ c ∈ Ioo (0 : ℝ)
        (finiteSupportMeanInverse (L.toTiltCurve L.variance_pos) v),
      L.variance c < Q (L.mean c)) :
    finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q v <
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v := by
  exact finiteSupportLegendreRate_gt_meanEnvelopeRateRight_of_strict
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hv0 hvhi hstrict

/-- Direct strict left comparison for an actual finite weighted law. -/
theorem finiteSupportLawData_rate_gt_meanEnvelopeRateLeft
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι)
    (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc (L.value L.loIndex - L.mean0)
        (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    {v : ℝ} (hvlo : L.value L.loIndex - L.mean0 < v) (hv0 : v < 0)
    (hstrict : ∃ c ∈ Ioo (finiteSupportMeanInverse (L.toTiltCurve L.variance_pos) v) 0,
      L.variance c < Q (L.mean c)) :
    finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q v <
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v := by
  exact finiteSupportLegendreRate_gt_meanEnvelopeRateLeft_of_strict
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hvlo hv0 hstrict

private theorem finiteSupportLawData_legendre_candidate_le_hi
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (t : ℝ) :
    t * (L.value L.hiIndex - L.mean0) - L.logMGF t ≤
      -Real.log (L.weight L.hiIndex) := by
  have hterm : L.weight L.hiIndex *
      Real.exp (t * L.centeredValue L.hiIndex) ≤
      finiteMGF L.support L.weight L.centeredValue t := by
    unfold finiteMGF
    exact Finset.single_le_sum
      (s := L.support)
      (f := fun i => L.weight i * Real.exp (t * L.centeredValue i))
      (fun i hi => mul_nonneg (L.weight_nonneg i hi) (Real.exp_pos _).le)
      (a := L.hiIndex) L.hi_mem
  have hlog := Real.log_le_log
    (mul_pos L.hi_weight_pos (Real.exp_pos _)) hterm
  rw [Real.log_mul L.hi_weight_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  change t * L.centeredValue L.hiIndex -
    Real.log (finiteMGF L.support L.weight L.centeredValue t) ≤
    -Real.log (L.weight L.hiIndex)
  linarith

private theorem finiteSupportLawData_legendre_candidate_le_lo
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (t : ℝ) :
    t * (L.value L.loIndex - L.mean0) - L.logMGF t ≤
      -Real.log (L.weight L.loIndex) := by
  have hterm : L.weight L.loIndex *
      Real.exp (t * L.centeredValue L.loIndex) ≤
      finiteMGF L.support L.weight L.centeredValue t := by
    unfold finiteMGF
    exact Finset.single_le_sum
      (s := L.support)
      (f := fun i => L.weight i * Real.exp (t * L.centeredValue i))
      (fun i hi => mul_nonneg (L.weight_nonneg i hi) (Real.exp_pos _).le)
      (a := L.loIndex) L.lo_mem
  have hlog := Real.log_le_log
    (mul_pos L.lo_weight_pos (Real.exp_pos _)) hterm
  rw [Real.log_mul L.lo_weight_pos.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  change t * L.centeredValue L.loIndex -
    Real.log (finiteMGF L.support L.weight L.centeredValue t) ≤
    -Real.log (L.weight L.loIndex)
  linarith

private theorem finiteSupportLawData_legendre_bddAbove_hi
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) :
    BddAbove (Set.range (fun t : ℝ =>
      t * (L.value L.hiIndex - L.mean0) - L.logMGF t)) := by
  refine ⟨-Real.log (L.weight L.hiIndex), ?_⟩
  rintro y ⟨t, rfl⟩
  exact finiteSupportLawData_legendre_candidate_le_hi L t

private theorem finiteSupportLawData_legendre_bddAbove_lo
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) :
    BddAbove (Set.range (fun t : ℝ =>
      t * (L.value L.loIndex - L.mean0) - L.logMGF t)) := by
  refine ⟨-Real.log (L.weight L.loIndex), ?_⟩
  rintro y ⟨t, rfl⟩
  exact finiteSupportLawData_legendre_candidate_le_lo L t

/-- On the upper half of the support, the actual finite-law Legendre rate is
bounded by its endpoint value. The comparison follows from the unique tilted
mean optimizer and the positive sign of its tilt. -/
theorem finiteSupportLawData_legendreRate_le_hi
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) {v : ℝ}
    (hv0 : 0 ≤ v) (hvhi : v < L.value L.hiIndex - L.mean0) :
    finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.hiIndex - L.mean0) := by
  let D := L.toTiltCurve L.variance_pos
  let t := finiteSupportMeanInverse D v
  have hvlo : D.lo < v := lt_of_lt_of_le D.hlomu hv0
  have htmean : D.mean t = v := finiteSupportMeanInverse_spec D hvlo hvhi
  have hmean0 : D.mean 0 = 0 := by
    simpa [D, FiniteSupportLawData.toTiltCurve] using D.mean_zero
  have ht0 : 0 ≤ t := by
    by_contra h
    have htneg : t < 0 := lt_of_not_ge h
    have hmono : StrictMono D.mean :=
      strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
    have hless := hmono htneg
    linarith [hmean0, htmean, hv0]
  have hrate := finiteSupportLegendreRate_at_mean D hvlo hvhi
  have hcandidate : t * v - D.logMGF t ≤
      t * (L.value L.hiIndex - L.mean0) - D.logMGF t := by
    have htv := mul_le_mul_of_nonneg_left (le_of_lt hvhi) ht0
    linarith
  have hBdd : BddAbove (Set.range (fun s : ℝ =>
      s * D.hi - D.logMGF s)) := by
    simpa [D, FiniteSupportLawData.toTiltCurve,
      FiniteSupportLawData.logMGF] using
        finiteSupportLawData_legendre_bddAbove_hi L
  have hsup : t * D.hi - D.logMGF t ≤
      finiteSupportLegendreRate D D.hi := by
    exact le_csSup hBdd ⟨t, by simp [D, FiniteSupportLawData.toTiltCurve]⟩
  rw [hrate]
  have hvalue : D.hi = L.value L.hiIndex - L.mean0 := by
    rfl
  simpa [hvalue] using hcandidate.trans hsup

/-- On the lower half of the support, the actual finite-law Legendre rate is
bounded by its endpoint value. The optimizer tilt is nonpositive. -/
theorem finiteSupportLawData_legendreRate_le_lo
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) {v : ℝ}
    (hvlo : L.value L.loIndex - L.mean0 < v) (hv0 : v ≤ 0) :
    finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.loIndex - L.mean0) := by
  let D := L.toTiltCurve L.variance_pos
  let t := finiteSupportMeanInverse D v
  have hvhi : v < D.hi := lt_of_le_of_lt hv0 D.hmuhi
  have htmean : D.mean t = v := finiteSupportMeanInverse_spec D hvlo hvhi
  have hmean0 : D.mean 0 = 0 := by
    simpa [D, FiniteSupportLawData.toTiltCurve] using D.mean_zero
  have ht0 : t ≤ 0 := by
    by_contra h
    have htpos : 0 < t := lt_of_not_ge h
    have hmono : StrictMono D.mean :=
      strictMono_of_hasDerivAt_pos D.mean_deriv D.variance_pos
    have hless := hmono htpos
    linarith [hmean0, htmean, hv0]
  have hrate := finiteSupportLegendreRate_at_mean D hvlo hvhi
  have htv := mul_le_mul_of_nonpos_left hvlo.le ht0
  have hcandidate : t * v - D.logMGF t ≤
      t * (L.value L.loIndex - L.mean0) - D.logMGF t := by
    linarith
  have hBdd : BddAbove (Set.range (fun s : ℝ =>
      s * D.lo - D.logMGF s)) := by
    simpa [D, FiniteSupportLawData.toTiltCurve,
      FiniteSupportLawData.logMGF] using
        finiteSupportLawData_legendre_bddAbove_lo L
  have hsup : t * D.lo - D.logMGF t ≤
      finiteSupportLegendreRate D D.lo := by
    exact le_csSup hBdd ⟨t, by simp [D, FiniteSupportLawData.toTiltCurve]⟩
  rw [hrate]
  have hvalue : D.lo = L.value L.loIndex - L.mean0 := by
    rfl
  simpa [hvalue] using hcandidate.trans hsup

/-- Right-endpoint continuation for a finite law. The rate comparison at the
endpoint follows from the actual finite-law optimizer; only the displayed
one-sided limit of the envelope integral is retained as a hypothesis. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateRight_endpoint_of_limit
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc
      (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    (hJ : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) Q v)
      (𝓝[<] (L.value L.hiIndex - L.mean0))
      (𝓝 (finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) Q
        (L.value L.hiIndex - L.mean0)))) :
    finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q
        (L.value L.hiIndex - L.mean0) ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.hiIndex - L.mean0) := by
  have hmean0 : L.mean 0 = 0 := by
    change (L.toTiltCurve L.variance_pos).mean 0 = 0
    exact (L.toTiltCurve L.variance_pos).mean_zero
  have h0hi : 0 < L.value L.hiIndex - L.mean0 := by
    rw [← hmean0]
    exact (finiteSupportLawData_mean_mem_Ioo L 0).2
  have hinner : ∀ᶠ v in 𝓝[<] (L.value L.hiIndex - L.mean0),
      finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q v ≤
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.hiIndex - L.mean0) := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Ioi_mem_nhds h0hi] with v hv
    intro hvhi
    have hpoint := finiteSupportLawData_rate_ge_meanEnvelopeRateRight
      L Q hQ hQpos hV hv.le hvhi
    have hend := finiteSupportLawData_legendreRate_le_hi L hv.le hvhi
    exact hpoint.trans hend
  have hdiff : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) Q v -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.hiIndex - L.mean0))
      (𝓝[<] (L.value L.hiIndex - L.mean0))
      (𝓝 (finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) Q
        (L.value L.hiIndex - L.mean0) -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.hiIndex - L.mean0))) := by
    exact hJ.sub tendsto_const_nhds
  have hnonpos : ∀ᶠ v in 𝓝[<] (L.value L.hiIndex - L.mean0),
      finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q v -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.hiIndex - L.mean0) ≤ 0 :=
    hinner.mono (fun v hv => sub_nonpos.mpr hv)
  have hlim := le_of_tendsto hdiff hnonpos
  linarith

/-- Right-endpoint continuation for a finite law, with the one-sided limits
required by the manuscript stated explicitly. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateRight_endpoint
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc
      (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    (hRate : Tendsto
      (fun v : ℝ => finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v)
      (𝓝[<] (L.value L.hiIndex - L.mean0))
      (𝓝 (finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.hiIndex - L.mean0))))
    (hJ : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) Q v)
      (𝓝[<] (L.value L.hiIndex - L.mean0))
      (𝓝 (finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) Q
        (L.value L.hiIndex - L.mean0)))) :
    finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q
        (L.value L.hiIndex - L.mean0) ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.hiIndex - L.mean0) := by
  exact finiteSupportLegendreRate_ge_meanEnvelopeRateRight_endpoint
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hRate hJ

/-- Left-endpoint continuation for a finite law, with the one-sided limits
required by the manuscript stated explicitly. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateLeft_endpoint
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc
      (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    (hRate : Tendsto
      (fun v : ℝ => finiteSupportLegendreRate (L.toTiltCurve L.variance_pos) v)
      (𝓝[>] (L.value L.loIndex - L.mean0))
      (𝓝 (finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.loIndex - L.mean0))))
    (hJ : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) Q v)
      (𝓝[>] (L.value L.loIndex - L.mean0))
      (𝓝 (finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) Q
        (L.value L.loIndex - L.mean0)))) :
    finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q
        (L.value L.loIndex - L.mean0) ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.loIndex - L.mean0) := by
  exact finiteSupportLegendreRate_ge_meanEnvelopeRateLeft_endpoint
    (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hRate hJ

/-- Left-endpoint continuation for a finite law. Only the displayed
one-sided limit of the envelope integral is needed; the endpoint rate bound
comes from the actual nonpositive optimizing tilt. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateLeft_endpoint_of_limit
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hQpos : ∀ u ∈ Icc
      (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    (hJ : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) Q v)
      (𝓝[>] (L.value L.loIndex - L.mean0))
      (𝓝 (finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) Q
        (L.value L.loIndex - L.mean0)))) :
    finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q
        (L.value L.loIndex - L.mean0) ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.loIndex - L.mean0) := by
  have hmean0 : L.mean 0 = 0 := by
    change (L.toTiltCurve L.variance_pos).mean 0 = 0
    exact (L.toTiltCurve L.variance_pos).mean_zero
  have hlo0 : L.value L.loIndex - L.mean0 < 0 := by
    rw [← hmean0]
    exact (finiteSupportLawData_mean_mem_Ioo L 0).1
  have hinner : ∀ᶠ v in 𝓝[>] (L.value L.loIndex - L.mean0),
      finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q v ≤
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.loIndex - L.mean0) := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Iio_mem_nhds hlo0] with v hv
    intro hvlo
    have hpoint := finiteSupportLawData_rate_ge_meanEnvelopeRateLeft
      L Q hQ hQpos hV hvlo hv.le
    have hend := finiteSupportLawData_legendreRate_le_lo L hvlo hv.le
    exact hpoint.trans hend
  have hdiff : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) Q v -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.loIndex - L.mean0))
      (𝓝[>] (L.value L.loIndex - L.mean0))
      (𝓝 (finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) Q
        (L.value L.loIndex - L.mean0) -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.loIndex - L.mean0))) := by
    exact hJ.sub tendsto_const_nhds
  have hnonpos : ∀ᶠ v in 𝓝[>] (L.value L.loIndex - L.mean0),
      finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q v -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.loIndex - L.mean0) ≤ 0 :=
    hinner.mono (fun v hv => sub_nonpos.mpr hv)
  have hlim := le_of_tendsto hdiff hnonpos
  linarith


/-- Right-endpoint continuation for a finite law. The rate comparison at the
endpoint follows from the actual finite-law optimizer; only the displayed
one-sided limit of the envelope integral is retained as a hypothesis. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateRight_endpoint_of_limit_open
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo
      (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0)))
    (hQpos : ∀ u ∈ Ioo
      (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    (Jlim : ℝ)
    (hJ : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) Q v)
      (𝓝[<] (L.value L.hiIndex - L.mean0))
      (𝓝 Jlim)) :
    Jlim ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.hiIndex - L.mean0) := by
  have hmean0 : L.mean 0 = 0 := by
    change (L.toTiltCurve L.variance_pos).mean 0 = 0
    exact (L.toTiltCurve L.variance_pos).mean_zero
  have h0hi : 0 < L.value L.hiIndex - L.mean0 := by
    rw [← hmean0]
    exact (finiteSupportLawData_mean_mem_Ioo L 0).2
  have hinner : ∀ᶠ v in 𝓝[<] (L.value L.hiIndex - L.mean0),
      finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q v ≤
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.hiIndex - L.mean0) := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Ioi_mem_nhds h0hi] with v hv
    intro hvhi
    have hpoint := finiteSupportLegendreRate_ge_meanEnvelopeRateRight_open
      (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hv.le hvhi
    have hend := finiteSupportLawData_legendreRate_le_hi L hv.le hvhi
    exact hpoint.trans hend
  have hdiff : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateRight
        (L.toTiltCurve L.variance_pos) Q v -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.hiIndex - L.mean0))
      (𝓝[<] (L.value L.hiIndex - L.mean0))
      (𝓝 (Jlim -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.hiIndex - L.mean0))) := by
    exact hJ.sub tendsto_const_nhds
  have hnonpos : ∀ᶠ v in 𝓝[<] (L.value L.hiIndex - L.mean0),
      finiteSupportMeanEnvelopeRateRight (L.toTiltCurve L.variance_pos) Q v -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.hiIndex - L.mean0) ≤ 0 :=
    hinner.mono (fun v hv => sub_nonpos.mpr hv)
  have hlim := le_of_tendsto hdiff hnonpos
  linarith


/-- Left-endpoint continuation for a finite law. Only the displayed
one-sided limit of the envelope integral is needed; the endpoint rate bound
comes from the actual nonpositive optimizing tilt. -/
theorem finiteSupportLawData_rate_ge_meanEnvelopeRateLeft_endpoint_of_limit_open
    {ι : Type*} [DecidableEq ι]
    (L : FiniteSupportLawData ι) (Q : ℝ → ℝ)
    (hQ : ContinuousOn Q (Ioo
      (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0)))
    (hQpos : ∀ u ∈ Ioo
      (L.value L.loIndex - L.mean0) (L.value L.hiIndex - L.mean0), 0 < Q u)
    (hV : ∀ t : ℝ, L.variance t ≤ Q (L.mean t))
    (Jlim : ℝ)
    (hJ : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) Q v)
      (𝓝[>] (L.value L.loIndex - L.mean0))
      (𝓝 Jlim)) :
    Jlim ≤
      finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
        (L.value L.loIndex - L.mean0) := by
  have hmean0 : L.mean 0 = 0 := by
    change (L.toTiltCurve L.variance_pos).mean 0 = 0
    exact (L.toTiltCurve L.variance_pos).mean_zero
  have hlo0 : L.value L.loIndex - L.mean0 < 0 := by
    rw [← hmean0]
    exact (finiteSupportLawData_mean_mem_Ioo L 0).1
  have hinner : ∀ᶠ v in 𝓝[>] (L.value L.loIndex - L.mean0),
      finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q v ≤
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.loIndex - L.mean0) := by
    apply eventually_nhdsWithin_iff.2
    filter_upwards [Iio_mem_nhds hlo0] with v hv
    intro hvlo
    have hpoint := finiteSupportLegendreRate_ge_meanEnvelopeRateLeft_open
      (L.toTiltCurve L.variance_pos) Q hQ hQpos hV hvlo hv.le
    have hend := finiteSupportLawData_legendreRate_le_lo L hvlo hv.le
    exact hpoint.trans hend
  have hdiff : Tendsto
      (fun v : ℝ => finiteSupportMeanEnvelopeRateLeft
        (L.toTiltCurve L.variance_pos) Q v -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.loIndex - L.mean0))
      (𝓝[>] (L.value L.loIndex - L.mean0))
      (𝓝 (Jlim -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.loIndex - L.mean0))) := by
    exact hJ.sub tendsto_const_nhds
  have hnonpos : ∀ᶠ v in 𝓝[>] (L.value L.loIndex - L.mean0),
      finiteSupportMeanEnvelopeRateLeft (L.toTiltCurve L.variance_pos) Q v -
        finiteSupportLegendreRate (L.toTiltCurve L.variance_pos)
          (L.value L.loIndex - L.mean0) ≤ 0 :=
    hinner.mono (fun v hv => sub_nonpos.mpr hv)
  have hlim := le_of_tendsto hdiff hnonpos
  linarith


end
end ExactHoeffding
