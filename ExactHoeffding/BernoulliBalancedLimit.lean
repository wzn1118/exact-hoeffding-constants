import ExactHoeffding.BernoulliRiccati
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Topology.Piecewise

open Filter Set
open scoped Topology

namespace ExactHoeffding

/-- A twice differentiable function with a double zero has the corresponding
quadratic quotient limit. Only the second derivative at the origin is needed. -/
theorem quadratic_quotient_limit
    {f df : ℝ → ℝ} {L : ℝ}
    (hd : ∀ x, HasDerivAt f (df x) x) (hdd : HasDerivAt df L 0)
    (hf0 : f 0 = 0) (hdf0 : df 0 = 0) :
    Tendsto (fun x => f x / x^2) (𝓝[≠] (0 : ℝ)) (𝓝 (L/2)) := by
  have hslope : Tendsto (fun x => df x / x) (𝓝[≠] (0 : ℝ)) (𝓝 L) := by
    have heq : slope df 0 = (fun x => df x / x) := by
      funext x
      simp only [slope_def_field, hdf0, sub_zero]
    rw [← heq]
    exact hdd.tendsto_slope
  have hratio : Tendsto (fun x => df x / (2*x)) (𝓝[≠] (0 : ℝ)) (𝓝 (L/2)) := by
    convert hslope.div_const 2 using 1
    funext x
    ring
  apply HasDerivAt.lhopital_zero_nhdsNE
    (Filter.Eventually.of_forall hd)
    (f' := df) (g := fun x : ℝ => x^2) (g' := fun x : ℝ => 2*x)
  · exact Filter.Eventually.of_forall fun x => by
      have hpow : HasDerivAt (fun y : ℝ => y^2) (2*x) x := by
        simpa using! ((hasDerivAt_id x).fun_pow 2)
      exact hpow
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) hx
  · simpa only [hf0] using (hd 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · have hc : ContinuousAt (fun x : ℝ => x^2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds :
      𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  · exact hratio

/-- The scale-zero value is the genuine two-sided limit of the scaled
Bernoulli log-Laplace envelope. -/
theorem scaledBernoulliLogLaplace_tendsto_scale_zero
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (M t : ℝ) :
    Tendsto (fun a => scaledBernoulliLogLaplace M p a t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (balancedBernoulliLogLaplace M p t)) := by
  let f : ℝ → ℝ := fun a => scaledBernoulliLogLaplace 1 p 1 (a*t)
  let df : ℝ → ℝ := fun a => scaledBernoulliMean 1 p 1 (a*t) * t
  have hd : ∀ a, HasDerivAt f (df a) a := by
    intro a
    have ha : HasDerivAt (fun a : ℝ => a*t) t a := hasDerivAt_mul_const t
    simpa only [f, df, Function.comp_def] using
      (scaledBernoulliLogLaplace_hasDerivAt (M := 1) (a := 1)
        one_ne_zero hp0 hp1 (a*t)).comp a ha
  have hdd : HasDerivAt df (p*(1-p)*t^2) 0 := by
    have ha : HasDerivAt (fun a : ℝ => a*t) t 0 := hasDerivAt_mul_const t
    have hbase := scaledBernoulliMean_hasDerivAt (M := 1) (a := 1)
      one_ne_zero one_ne_zero hp0 hp1 (0*t)
    have hcalc := (hbase.comp 0 ha).mul_const t
    simp only [zero_mul, scaledBernoulliMean_zero, mul_zero, sub_zero, add_zero,
      one_mul, one_pow, div_one, zero_pow (by norm_num : (2:ℕ)≠0)] at hcalc
    exact hcalc.congr_deriv (by ring)
  have hf0 : f 0 = 0 := by simp [f]
  have hdf0 : df 0 = 0 := by simp [df]
  have hlim := (quadratic_quotient_limit hd hdd hf0 hdf0).const_mul M
  have heq : (fun a => scaledBernoulliLogLaplace M p a t) =
      (fun a => M*(f a/a^2)) := by
    funext a
    dsimp [scaledBernoulliLogLaplace, scaledBernoulliDenom, f]
    simp only [one_pow, div_one, one_mul]
    ring
  have hval : balancedBernoulliLogLaplace M p t = M*(p*(1-p)*t^2/2) := by
    unfold balancedBernoulliLogLaplace
    ring
  rw [heq, hval]
  exact hlim

/-- Updating the scale-zero value by its Gaussian limit gives a continuous
extension, in the standard topology rather than a punctured limit only. -/
theorem scaledBernoulliLogLaplace_continuous_extension
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (M t : ℝ) :
    ContinuousAt (Function.update (fun a => scaledBernoulliLogLaplace M p a t)
      0 (balancedBernoulliLogLaplace M p t)) 0 := by
  exact continuousAt_update_same.mpr
    (scaledBernoulliLogLaplace_tendsto_scale_zero hp0 hp1 M t)

/-- The scale-zero limit also includes deterministic Bernoulli endpoints. -/
theorem scaledBernoulliLogLaplace_tendsto_scale_zero_closed
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (M t : ℝ) :
    Tendsto (fun a => scaledBernoulliLogLaplace M p a t)
      (𝓝[≠] (0 : ℝ)) (𝓝 (balancedBernoulliLogLaplace M p t)) := by
  rcases hp0.eq_or_lt with hzero | hpos
  · subst p
    simpa only [scaledBernoulliLogLaplace_probability_zero, balancedBernoulliLogLaplace,
      mul_zero, zero_mul, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] (0 : ℝ)) (𝓝 0))
  · rcases hp1.lt_or_eq with hlt | hone
    · exact scaledBernoulliLogLaplace_tendsto_scale_zero hpos hlt M t
    · subst p
      simpa only [scaledBernoulliLogLaplace_probability_one, balancedBernoulliLogLaplace,
        sub_self, mul_zero, zero_mul, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] (0 : ℝ)) (𝓝 0))

theorem scaledBernoulliLogLaplace_continuous_extension_closed
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (M t : ℝ) :
    ContinuousAt (Function.update (fun a => scaledBernoulliLogLaplace M p a t)
      0 (balancedBernoulliLogLaplace M p t)) 0 := by
  exact continuousAt_update_same.mpr
    (scaledBernoulliLogLaplace_tendsto_scale_zero_closed hp0 hp1 M t)


end ExactHoeffding
