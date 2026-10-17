import ExactHoeffding.Cumulant23Taylor
import ExactHoeffding.RescaledHigherTiltInputs
import ExactHoeffding.RescaledFourthTiltInput
import ExactHoeffding.RescaledFourthPopulationInputs
import ExactHoeffding.RescaledActualProxy
import ExactHoeffding.RescaledTiltCoefficient
import ExactHoeffding.AnalyticCoordinateJets
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Joint local fourth-order Taylor formula for the actual proxy

The coefficients below are the actual factorial-moment cumulants of the
rescaled finite law.  A fifth-derivative integral represents the remainder;
clamping outside a local analytic neighborhood gives a globally continuous
extension of that remainder without changing it on the local parameter box.
-/

namespace ExactHoeffding

noncomputable section

open Filter
open scoped Topology

private theorem rescaledMean_eq_rescaledMoment_one (m : ℕ) (s e : ℝ) :
    rescaledMean m s e = hypergeomRescaledMoment m 1 s e := by
  rw [← rescaledFactorialMoment_degree_one, rescaledFactorialMoment_eq_highCumulants]
  simp [hypergeomRescaledMoment, momentFromFactorials]

private theorem rescaledMoment_two_eq_factorial_moments (m : ℕ) (s e : ℝ) :
    hypergeomRescaledMoment m 2 s e =
      rescaledFactorialMoment m s 2 e + rescaledMean m s e := by
  simp only [hypergeomRescaledMoment, momentFromFactorials]
  rw [← rescaledFactorialMoment_eq_highCumulants m 2 s e,
    ← rescaledFactorialMoment_eq_highCumulants m 1 s e,
    rescaledFactorialMoment_degree_one]

private theorem rescaledMoment_three_eq_factorial_moments (m : ℕ) (s e : ℝ) :
    hypergeomRescaledMoment m 3 s e =
      rescaledFactorialMoment m s 3 e + 3 * rescaledFactorialMoment m s 2 e +
        rescaledMean m s e := by
  simp only [hypergeomRescaledMoment, momentFromFactorials]
  rw [← rescaledFactorialMoment_eq_highCumulants m 3 s e,
    ← rescaledFactorialMoment_eq_highCumulants m 2 s e,
    ← rescaledFactorialMoment_eq_highCumulants m 1 s e,
    rescaledFactorialMoment_degree_one]

/-- The zero-tilt coefficient in the proxy expansion is the second
factorial-family cumulant. -/
theorem rescaledProxyExtension_coefficient_zero (m : ℕ) (s e : ℝ) :
    rescaledProxyExtension m s e 0 = hypergeomRescaledCumulant2 m s e := by
  unfold hypergeomRescaledCumulant2
  rw [rescaledProxyExtension_tilt_zero,
    rescaledMean_eq_rescaledMoment_one,
    rescaledMoment_two_eq_factorial_moments,
    rescaledMean_eq_rescaledMoment_one]
  ring

/-- The linear Taylor coefficient is one third of the actual third
factorial-family cumulant. -/
theorem rescaledProxyExtension_coefficient_one (m : ℕ) (s e : ℝ) :
    deriv (rescaledProxyExtension m s e) 0 = hypergeomRescaledCumulant3 m s e / 3 := by
  rw [rescaledProxyExtension_hasDerivAt_tilt_zero m s e |>.deriv]
  unfold hypergeomRescaledCumulant3
  rw [rescaledMean_eq_rescaledMoment_one,
    rescaledMoment_two_eq_factorial_moments,
    rescaledMoment_three_eq_factorial_moments,
    rescaledMean_eq_rescaledMoment_one]
  ring

/-- The quadratic Taylor coefficient is one twelfth of the fourth
factorial-family cumulant. -/
theorem rescaledProxyExtension_coefficient_two (m : ℕ) (s e : ℝ) :
    iteratedDeriv 2 (rescaledProxyExtension m s e) 0 =
      hypergeomRescaledCumulant4 m s e / 6 := by
  rw [rescaledProxyExtension_deriv2_tilt_zero,
    rescaledFourthCumulantPolynomial_eq_highCumulants]

/-- The cubic Taylor coefficient is one sixtieth of the fifth cumulant. -/
theorem rescaledProxyExtension_coefficient_three (m : ℕ) (hm : 1 ≤ m) (s e : ℝ) :
    iteratedDeriv 3 (rescaledProxyExtension m s e) 0 =
      hypergeomRescaledCumulant5 m s e / 10 :=
  rescaledProxyExtension_deriv3_tilt_zero m hm s e

/-- The quartic Taylor coefficient is one three-hundred-sixtieth of the
sixth cumulant. -/
theorem rescaledProxyExtension_coefficient_four (m : ℕ) (hm : 1 ≤ m) (s e : ℝ) :
    iteratedDeriv 4 (rescaledProxyExtension m s e) 0 =
      hypergeomRescaledCumulant6 m s e / 15 :=
  rescaledProxyExtension_deriv4_tilt_zero m hm s e

private def proxyTiltPartial5 (m : ℕ) (s : ℝ) : ℝ × ℝ → ℝ :=
  (tiltPartial^[5]) (fun z : ℝ × ℝ => rescaledProxyExtension m s z.1 z.2)

private def proxyTaylorClamp (δ x : ℝ) : ℝ := max (-δ) (min δ x)

private theorem proxyTaylorClamp_abs_le {δ x : ℝ} (hδ : 0 ≤ δ) :
    |proxyTaylorClamp δ x| ≤ δ := by
  apply abs_le.mpr
  constructor
  · have hlo : -δ ≤ proxyTaylorClamp δ x := by
      dsimp [proxyTaylorClamp]
      exact le_max_left _ _
    linarith
  · dsimp [proxyTaylorClamp]
    exact max_le_iff.mpr ⟨by linarith, min_le_left _ _⟩

private theorem proxyTaylorClamp_continuous (δ : ℝ) :
    Continuous (proxyTaylorClamp δ) := by
  change Continuous (fun x : ℝ => max (-δ) (min δ x))
  exact continuous_const.max (continuous_const.min continuous_id)

private theorem proxyTaylorClamp_eq_self {δ x : ℝ} (hx : |x| ≤ δ) :
    proxyTaylorClamp δ x = x := by
  dsimp [proxyTaylorClamp]
  rw [min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]

/-- The actual proxy has a continuous local fourth-order Taylor expansion
with a remainder jointly continuous in inverse population size and tilt.
The single positive radius is uniform over both parameters. -/
theorem rescaledProxyExtension_joint_uniform_taylor (m : ℕ) (hm : 1 ≤ m) (s : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ × ℝ → ℝ,
      Continuous R ∧
      ∀ e t : ℝ, |e| < δ → |t| < δ →
        rescaledProxyExtension m s e t =
          hypergeomRescaledCumulant2 m s e +
          hypergeomRescaledCumulant3 m s e / 3 * t +
          hypergeomRescaledCumulant4 m s e / 12 * t ^ 2 +
          hypergeomRescaledCumulant5 m s e / 60 * t ^ 3 +
          hypergeomRescaledCumulant6 m s e / 360 * t ^ 4 +
          t ^ 5 * R (e, t) := by
  let Q : ℝ × ℝ → ℝ := fun z => rescaledProxyExtension m s z.1 z.2
  have hQ : AnalyticAt ℝ Q (0, 0) := rescaledProxyExtension_joint_analytic m s
  have hQev : ∀ᶠ z : ℝ × ℝ in 𝓝 (0, 0), AnalyticAt ℝ Q z := hQ.eventually_analyticAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hQev
  let δ := r / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδr : δ < r := by dsimp [δ]; linarith
  have hQball : ∀ z ∈ Metric.ball (0, 0) r, AnalyticAt ℝ Q z := by
    intro z hz
    exact hball (by simpa only [Metric.mem_ball] using hz)
  have hQ5ball : AnalyticOnNhd ℝ (proxyTiltPartial5 m s) (Metric.ball (0, 0) r) := by
    intro z hz
    exact analyticAt_iterate_tiltPartial 5 Q z (hQball z hz)
  have hQ5cont : ContinuousOn (proxyTiltPartial5 m s) (Metric.ball (0, 0) r) :=
    hQ5ball.continuousOn
  let cl : ℝ → ℝ := proxyTaylorClamp δ
  have hclcont : Continuous cl := proxyTaylorClamp_continuous δ
  have hclabs (x : ℝ) : |cl x| ≤ δ := proxyTaylorClamp_abs_le hδ.le
  let ψ : ((ℝ × ℝ) × ℝ) → ℝ × ℝ := fun z =>
    (cl z.1.1, cl (z.2 * cl z.1.2))
  have hψcont : Continuous ψ := by
    change Continuous (fun z : ((ℝ × ℝ) × ℝ) =>
      (cl z.1.1, cl (z.2 * cl z.1.2)))
    apply Continuous.prodMk
    · exact hclcont.comp (continuous_fst.comp continuous_fst)
    · exact hclcont.comp
        (continuous_snd.mul (hclcont.comp (continuous_snd.comp continuous_fst)))
  have hψball : Set.MapsTo ψ Set.univ (Metric.ball (0, 0) r) := by
    intro z _
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
    exact ⟨lt_of_le_of_lt (hclabs z.1.1) hδr,
      lt_of_le_of_lt (hclabs (z.2 * cl z.1.2)) hδr⟩
  let G : ((ℝ × ℝ) × ℝ) → ℝ := fun z =>
    (1 - z.2) ^ 4 / 24 * proxyTiltPartial5 m s (ψ z)
  have hG : Continuous G := by
    have hcomp : Continuous (fun z => proxyTiltPartial5 m s (ψ z)) := by
      rw [← continuousOn_univ]
      exact hQ5cont.comp hψcont.continuousOn hψball
    have hweight : Continuous (fun z : ((ℝ × ℝ) × ℝ) => (1 - z.2) ^ 4 / 24) := by
      fun_prop
    change Continuous (fun z => (1 - z.2) ^ 4 / 24 * proxyTiltPartial5 m s (ψ z))
    exact hweight.mul hcomp
  let R : ℝ × ℝ → ℝ := fun z => ∫ u in (0 : ℝ)..1, G (z, u)
  have hR : Continuous R := by
    dsimp [R]
    have huncurry : Continuous
        (Function.uncurry (fun z : ℝ × ℝ => fun u : ℝ => G (z, u))) := by
      convert hG using 1 <;> funext p <;> cases p <;> rfl
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      huncurry 0 1
  refine ⟨δ, hδ, R, hR, ?_⟩
  intro e t he ht
  have he' : cl e = e := proxyTaylorClamp_eq_self (le_of_lt he)
  have ht' : cl t = t := proxyTaylorClamp_eq_self (le_of_lt ht)
  have hbox (x : ℝ) (hx : x ∈ Set.Ioo (-δ) δ) :
      AnalyticAt ℝ Q (e, x) := by
    apply hQball
    simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
    exact ⟨lt_trans he hδr, lt_trans (abs_lt.mpr hx) hδr⟩
  have hslice (x : ℝ) (hx : x ∈ Set.Ioo (-δ) δ) :
      AnalyticAt ℝ (fun y => Q (e, y)) x := by
    exact (hbox x hx).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hsliceCD : ContDiffOn ℝ 5 (fun y => Q (e, y)) (Set.Ioo (-δ) δ) := by
    apply isOpen_Ioo.contDiffOn_iff.mpr
    intro x hx
    exact (hslice x hx).contDiffAt
  have htmem : t ∈ Set.Ioo (-δ) δ := abs_lt.mp ht
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-δ) δ := by constructor <;> linarith
  have hseg : Set.uIcc (0 : ℝ) t ⊆ Set.Ioo (-δ) δ := by
    intro x hx
    rcases le_total (0 : ℝ) t with h0t | ht0
    · rw [Set.uIcc_of_le h0t] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2, (abs_lt.mp ht).2]⟩
    · rw [Set.uIcc_of_ge ht0] at hx
      exact ⟨by linarith [hx.1, (abs_lt.mp ht).1], by linarith [hx.2]⟩
  by_cases htz : t = 0
  · subst t
    rw [rescaledProxyExtension_coefficient_zero]
    simp
  · have huniq : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) t) :=
      uniqueDiffOn_uIcc (Ne.symm htz)
    have hwithin (j : ℕ) :
        iteratedDerivWithin j (fun y => Q (e, y)) (Set.uIcc (0 : ℝ) t) 0 =
          iteratedDeriv j (fun y => Q (e, y)) 0 :=
      iteratedDerivWithin_eq_iteratedDeriv huniq (hslice 0 h0mem).contDiffAt
        Set.left_mem_uIcc
    have hpoly : taylorWithinEval (fun y => Q (e, y)) 4 (Set.uIcc (0 : ℝ) t) 0 t =
        hypergeomRescaledCumulant2 m s e +
          hypergeomRescaledCumulant3 m s e / 3 * t +
          hypergeomRescaledCumulant4 m s e / 12 * t ^ 2 +
          hypergeomRescaledCumulant5 m s e / 60 * t ^ 3 +
          hypergeomRescaledCumulant6 m s e / 360 * t ^ 4 := by
      rw [taylor_within_apply]
      simp only [sub_zero, smul_eq_mul, hwithin, iteratedDeriv_zero, iteratedDeriv_one]
      norm_num [Finset.sum_range_succ]
      simp only [Q]
      rw [rescaledProxyExtension_coefficient_zero,
        rescaledProxyExtension_coefficient_one,
        rescaledProxyExtension_coefficient_two,
        rescaledProxyExtension_coefficient_three m hm,
        rescaledProxyExtension_coefficient_four m hm]
      ring
    have hsliceCDseg : ContDiffOn ℝ (4 + 1) (fun y => Q (e, y)) (Set.uIcc 0 t) := by
      convert hsliceCD.mono hseg using 1 <;> norm_num
    have hTaylor0 := taylor_integral_remainder (f := fun y => Q (e, y))
      (x₀ := (0 : ℝ)) (x := t) (n := 4) hsliceCDseg
    have hTaylor : Q (e,t) - taylorWithinEval (fun y => Q (e,y)) 4
        (Set.uIcc (0:ℝ) t) 0 t =
        ∫ u in (0:ℝ)..t, ((t-u)^4/(Nat.factorial 4 : ℝ)) *
          iteratedDerivWithin 5 (fun y => Q (e,y)) (Set.uIcc (0:ℝ) t) u := by
      simpa only [smul_eq_mul] using hTaylor0
    have hpair (x : ℝ) (hx : x ∈ Set.uIcc (0 : ℝ) t) : AnalyticAt ℝ Q (e, x) := by
      apply hQball
      simp only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
      have hdist : |x| ≤ |t| := by
        have hd := Real.dist_le_of_mem_uIcc hx Set.left_mem_uIcc
        simpa [Real.dist_eq] using hd
      exact ⟨lt_trans he hδr, lt_of_le_of_lt hdist (lt_trans ht hδr)⟩
    have hseg5 (u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) t) :
        iteratedDerivWithin 5 (fun y => Q (e, y)) (Set.uIcc (0 : ℝ) t) u =
          proxyTiltPartial5 m s (e, u) := by
      have huopen : u ∈ Set.Ioo (-δ) δ := by
        have hd := Real.dist_le_of_mem_uIcc hu Set.left_mem_uIcc
        have habs : |u| ≤ |t| := by simpa [Real.dist_eq] using hd
        have huB : -|t| ≤ u ∧ u ≤ |t| := abs_le.mp habs
        exact ⟨(neg_lt_neg ht).trans_le huB.1, huB.2.trans_lt ht⟩
      rw [iteratedDerivWithin_eq_iteratedDeriv huniq
        (hslice u huopen).contDiffAt hu]
      exact (iterate_tiltPartial_eq_iteratedDeriv 5 Q (e, u) (hpair u hu)).symm
    have hRlocal : R (e, t) = ∫ u in (0 : ℝ)..1,
        (1 - u) ^ 4 / 24 * proxyTiltPartial5 m s (e, u * t) := by
      dsimp [R, G]
      apply intervalIntegral.integral_congr
      intro u hu
      have hu01 : 0 ≤ u ∧ u ≤ 1 := by simpa using hu
      have habsu : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu01.1], by linarith [hu01.2]⟩
      have hmul : |u * t| ≤ δ := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right habsu (abs_nonneg t)).trans
          (by rw [one_mul]; exact le_of_lt ht)
      have hclx : cl (u * cl t) = u * t := by
        rw [ht']
        change proxyTaylorClamp δ (u * t) = u * t
        exact proxyTaylorClamp_eq_self hmul
      simp [ψ, he', hclx]
    have hsub : (∫ u in (0 : ℝ)..t,
        ((t - u) ^ 4 / (Nat.factorial 4 : ℝ)) *
          iteratedDerivWithin 5 (fun y => Q (e, y)) (Set.uIcc (0 : ℝ) t) u) =
        t ^ 5 * R (e, t) := by
      calc
        _ = t * ∫ u in (0 : ℝ)..1,
            ((t - u*t) ^ 4 / (Nat.factorial 4 : ℝ)) *
              iteratedDerivWithin 5 (fun y => Q (e, y)) (Set.uIcc (0 : ℝ) t) (u*t) := by
          symm
          simpa only [zero_mul, one_mul, smul_eq_mul] using
            (intervalIntegral.smul_integral_comp_mul_right
              (a := (0 : ℝ)) (b := (1 : ℝ))
              (fun u => ((t-u)^4/(Nat.factorial 4 : ℝ)) *
                iteratedDerivWithin 5 (fun y => Q (e,y)) (Set.uIcc (0:ℝ) t) u) t)
        _ = t ^ 5 * R (e, t) := by
          rw [show (Nat.factorial 4 : ℝ) = 24 by norm_num]
          rw [hRlocal]
          have huPoint (u : ℝ) (hu : u ∈ Set.uIcc (0 : ℝ) 1) :
              u * t ∈ Set.uIcc (0 : ℝ) t := by
            have hu01 : 0 ≤ u ∧ u ≤ 1 := by simpa using hu
            by_cases htpos : 0 ≤ t
            · exact Set.mem_uIcc_of_le (mul_nonneg hu01.1 htpos)
                (by nlinarith [mul_le_mul_of_nonneg_left hu01.2 htpos])
            · have htneg : t ≤ 0 := le_of_not_ge htpos
              exact Set.mem_uIcc_of_ge
                (by nlinarith [mul_le_mul_of_nonpos_right hu01.2 htneg])
                (mul_nonpos_of_nonneg_of_nonpos hu01.1 htneg)
          have hinter : (∫ u in (0 : ℝ)..1,
              ((t - u*t) ^ 4 / 24) *
                iteratedDerivWithin 5 (fun y => Q (e,y)) (Set.uIcc (0:ℝ) t) (u*t)) =
              t ^ 4 * ∫ u in (0 : ℝ)..1,
                (1-u)^4 / 24 * proxyTiltPartial5 m s (e,u*t) := by
            calc
              _ = ∫ u in (0 : ℝ)..1,
                  t ^ 4 * ((1-u)^4 / 24 * proxyTiltPartial5 m s (e,u*t)) := by
                apply intervalIntegral.integral_congr
                intro u hu
                have hu01' : 0 ≤ u ∧ u ≤ 1 := by simpa using hu
                have huI : u ∈ Set.uIcc (0:ℝ) 1 :=
                  Set.mem_uIcc_of_le hu01'.1 hu01'.2
                change ((t-u*t)^4/24) *
                    iteratedDerivWithin 5 (fun y => Q (e,y)) (Set.uIcc (0:ℝ) t) (u*t) =
                  t^4 * ((1-u)^4/24 * proxyTiltPartial5 m s (e,u*t))
                rw [hseg5 (u*t) (huPoint u huI)]
                ring
              _ = t ^ 4 * ∫ u in (0 : ℝ)..1,
                  (1-u)^4 / 24 * proxyTiltPartial5 m s (e,u*t) := by
                rw [intervalIntegral.integral_const_mul]
          rw [hinter]
          rw [show t * (t ^ 4 * ∫ u in (0 : ℝ)..1,
              (1-u)^4/24 * proxyTiltPartial5 m s (e,u*t)) =
              t ^ 5 * (∫ u in (0 : ℝ)..1,
                (1-u)^4/24 * proxyTiltPartial5 m s (e,u*t)) by ring]
    have hTaylorEq : Q (e,t) =
        taylorWithinEval (fun y => Q (e,y)) 4 (Set.uIcc (0:ℝ) t) 0 t +
          ∫ u in (0:ℝ)..t, ((t-u)^4/(Nat.factorial 4 : ℝ)) *
            iteratedDerivWithin 5 (fun y => Q (e,y)) (Set.uIcc (0:ℝ) t) u := by
      linarith [hTaylor]
    change Q (e,t) = _
    rw [hTaylorEq, hpoly, hsub]

end
end ExactHoeffding
