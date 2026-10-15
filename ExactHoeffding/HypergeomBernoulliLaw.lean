import ExactHoeffding.BernoulliProductLaw
import ExactHoeffding.HypergeomBernoulliMGF

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal unitInterval

namespace ExactHoeffding

def hypergeomTiltMass (N k m : ℕ) (t : ℝ) (i : Fin (m + 1)) : ℝ :=
  hypergeomMass N k m i * Real.exp (t * (i : ℝ)) / hypergeomMGF N k m t

theorem hypergeomTiltMass_nonneg (N k m : ℕ) (t : ℝ) (i : Fin (m + 1)) :
    0 ≤ hypergeomTiltMass N k m t i := by
  exact div_nonneg (mul_nonneg (hypergeomMass_nonneg N k m i) (Real.exp_pos _).le)
    (hypergeomMGF_nonneg N k m t)

theorem hypergeomTiltMass_total (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    ∑ i, hypergeomTiltMass N k m t i = 1 := by
  simp only [hypergeomTiltMass, ← Finset.sum_div]
  have he : (∑ i : Fin (m+1), hypergeomMass N k m i * Real.exp (t * (i : ℝ))) =
      hypergeomMGF N k m t := by
    simpa only [hypergeomMGF, finiteMGF] using
      (Fin.sum_univ_eq_sum_range (fun i : ℕ => hypergeomMass N k m i * Real.exp (t * (i : ℝ)))
        (n := m+1))
  rw [he]
  exact div_self (ne_of_gt (hypergeomMGF_pos N k m hk hm t))

/-- The actual exponentially tilted hypergeometric probability measure. -/
def hypergeomTiltMeasure (N k m : ℕ) (t : ℝ) : Measure (Fin (m + 1)) :=
  ∑ i, ENNReal.ofReal (hypergeomTiltMass N k m t i) • Measure.dirac i

theorem hypergeomTiltMeasure_probability (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N)
    (t : ℝ) : IsProbabilityMeasure (hypergeomTiltMeasure N k m t) := by
  constructor
  simp only [hypergeomTiltMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hypergeomTiltMass_nonneg N k m t i),
    hypergeomTiltMass_total N k m hk hm t, ENNReal.ofReal_one]

instance hypergeomTiltMeasure_finite (N k m : ℕ) (t : ℝ) :
    IsFiniteMeasure (hypergeomTiltMeasure N k m t) := by
  constructor
  simp only [hypergeomTiltMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.ofReal_lt_top)

theorem hypergeomTiltMeasure_integral (N k m : ℕ) (t : ℝ)
    (f : Fin (m + 1) → ℝ) :
    (∫ i, f i ∂hypergeomTiltMeasure N k m t) =
      ∑ i, hypergeomTiltMass N k m t i * f i := by
  unfold hypergeomTiltMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by simp) : Integrable f (Measure.dirac i)).smul_measure
      ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal (hypergeomTiltMass_nonneg N k m t _), smul_eq_mul]

theorem hypergeomTiltMeasure_mgf (N k m : ℕ) (_hk : k ≤ N) (_hm : m ≤ N)
    (t u : ℝ) :
    mgf (fun i : Fin (m + 1) => (i : ℝ)) (hypergeomTiltMeasure N k m t) u =
      hypergeomMGF N k m (t + u) / hypergeomMGF N k m t := by
  rw [mgf, hypergeomTiltMeasure_integral]
  simp only [hypergeomTiltMass]
  calc
    _ = (∑ i : Fin (m+1), hypergeomMass N k m i *
        Real.exp ((t + u) * (i : ℝ))) / hypergeomMGF N k m t := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [add_mul, Real.exp_add]
      ring
    _ = _ := by
      congr 1
      simpa only [hypergeomMGF, finiteMGF] using
        (Fin.sum_univ_eq_sum_range
          (fun i : ℕ => hypergeomMass N k m i * Real.exp ((t + u) * (i : ℝ)))
          (n := m+1))

def boundedShiftedBernoulliCount (m b j : ℕ) (h : b + j ≤ m)
    (x : Fin j → ℝ) : Fin (m + 1) :=
  ⟨b + (bernoulliSuccessCount x : ℕ), by have := (bernoulliSuccessCount x).isLt; omega⟩

theorem boundedShiftedBernoulliCount_measurable (m b j : ℕ) (h : b + j ≤ m) :
    Measurable (boundedShiftedBernoulliCount m b j h) := by
  exact (measurable_of_finite (fun a : Fin (j + 1) =>
    (⟨b + (a : ℕ), by have := a.isLt; omega⟩ : Fin (m + 1)))).comp
      bernoulliSuccessCount_measurable

theorem boundedShiftedBernoulliCount_eq_sum_ae (m b j : ℕ) (h : b + j ≤ m)
    (p : Fin j → unitInterval) :
    (fun x => (boundedShiftedBernoulliCount m b j h x : ℝ))
      =ᵐ[independentBernoulliMeasure p]
      (fun x : Fin j → ℝ => (b : ℝ) + ∑ i, x i) := by
  filter_upwards [bernoulliSuccessCount_eq_sum_ae p] with x hx
  change ((b + (bernoulliSuccessCount x : ℕ) : ℕ) : ℝ) = _
  push_cast
  rw [hx]

/-- Every tilted hypergeometric law is the law of its lower-support shift
plus a sum of independent Bernoulli variables on a genuine product space.
The number of variables is exactly the support width, including width zero. -/
theorem hypergeom_tilted_law_eq_shifted_independent_bernoulli
    (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    ∃ p : Fin (min (min k (N-k)) (min m (N-m))) → unitInterval,
      (∀ i, 0 < (p i : ℝ) ∧ (p i : ℝ) < 1) ∧
      (hypergeomTiltMeasure N k m t).map (fun i : Fin (m+1) => (i : ℝ)) =
        (independentBernoulliMeasure p).map (fun x =>
          ((k + m - N : ℕ) : ℝ) + ∑ i, x i) := by
  let j := min (min k (N-k)) (min m (N-m))
  let b := k + m - N
  obtain ⟨p, hp, hmgf⟩ := hypergeom_tilted_shifted_bernoulli_mgf N k m hk hm t
  let q : Fin j → unitInterval := fun i => ⟨p i, (hp i).1.le, (hp i).2.le⟩
  refine ⟨q, fun i => hp i, ?_⟩
  have hb : b + j ≤ m := by dsimp [b, j]; omega
  have hsum := boundedShiftedBernoulliCount_eq_sum_ae m b j hb q
  have hlaw := finite_pushforward_real_law_eq_of_mgf_eq
    (hypergeomTiltMeasure N k m t) (independentBernoulliMeasure q)
    (fun i : Fin (m+1) => i) (boundedShiftedBernoulliCount m b j hb)
    measurable_id (boundedShiftedBernoulliCount_measurable m b j hb) (fun u => by
      rw [hypergeomTiltMeasure_mgf N k m hk hm,
        mgf_congr hsum, independentBernoulli_shifted_sum_mgf]
      exact hmgf u)
  exact hlaw.trans (Measure.map_congr hsum)

end ExactHoeffding
