import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Independent Bernoulli product laws

The Bernoulli parameters determine a genuine product probability measure.  Its
coordinate maps are independent and its sum has the expected finite-product
moment-generating function.  Finite lattice laws are identified by their PGFs.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval ENNReal NNReal

namespace ExactHoeffding

def independentBernoulliMeasure {j : ℕ} (p : Fin j → unitInterval) :
    Measure (Fin j → ℝ) :=
  Measure.pi (fun i => bernoulliMeasure (1 : ℝ) 0 (p i))

instance independentBernoulliMeasure_probability {j : ℕ} (p : Fin j → unitInterval) :
    IsProbabilityMeasure (independentBernoulliMeasure p) := by
  unfold independentBernoulliMeasure
  infer_instance

theorem independentBernoulli_coordinate_law {j : ℕ} (p : Fin j → unitInterval)
    (i : Fin j) :
    (independentBernoulliMeasure p).map (fun x => x i) =
      bernoulliMeasure (1 : ℝ) 0 (p i) := by
  exact (measurePreserving_eval (fun i => bernoulliMeasure (1 : ℝ) 0 (p i)) i).map_eq

theorem independentBernoulli_coordinates {j : ℕ} (p : Fin j → unitInterval) :
    iIndepFun (fun i (x : Fin j → ℝ) => x i) (independentBernoulliMeasure p) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)

theorem bernoulli_coordinate_mgf (p : unitInterval) (t : ℝ) :
    mgf id (bernoulliMeasure (1 : ℝ) 0 p) t =
      1 - (p : ℝ) + (p : ℝ) * Real.exp t := by
  rw [mgf, integral_bernoulliMeasure]
  simp only [id_eq, mul_one, mul_zero, Real.exp_zero, smul_eq_mul, mul_one]
  ring

theorem independentBernoulli_sum_mgf {j : ℕ} (p : Fin j → unitInterval) (t : ℝ) :
    mgf (fun x : Fin j → ℝ => ∑ i, x i) (independentBernoulliMeasure p) t =
      ∏ i, (1 - (p i : ℝ) + (p i : ℝ) * Real.exp t) := by
  unfold mgf independentBernoulliMeasure
  simp_rw [Finset.mul_sum, Real.exp_sum]
  calc
    _ = ∏ i, ∫ x : ℝ, Real.exp (t * x) ∂bernoulliMeasure (1 : ℝ) 0 (p i) :=
      integral_fintype_prod_eq_prod (fun (_ : Fin j) (x : ℝ) => Real.exp (t * x))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact bernoulli_coordinate_mgf (p i) t

theorem independentBernoulli_shifted_sum_mgf {j : ℕ} (p : Fin j → unitInterval)
    (b t : ℝ) :
    mgf (fun x : Fin j → ℝ => b + ∑ i, x i) (independentBernoulliMeasure p) t =
      Real.exp (b * t) * ∏ i, (1 - (p i : ℝ) + (p i : ℝ) * Real.exp t) := by
  unfold mgf
  simp_rw [mul_add, Real.exp_add]
  rw [integral_const_mul]
  simpa [mgf, mul_comm b t] using
    congrArg (Real.exp (t * b) * ·) (independentBernoulli_sum_mgf p t)

/-- A finite lattice measure, including zero masses and the empty lattice. -/
def finiteLatticeMeasure (n : ℕ) (w : Fin n → ℝ≥0) : Measure ℝ :=
  ∑ i, (w i : ℝ≥0∞) • Measure.dirac (i : ℝ)

def finiteLatticePGF (n : ℕ) (w : Fin n → ℝ≥0) : Polynomial ℝ :=
  ∑ i : Fin n, Polynomial.monomial (i : ℕ) (w i : ℝ)

theorem finiteLatticePGF_eval (n : ℕ) (w : Fin n → ℝ≥0) (z : ℝ) :
    (finiteLatticePGF n w).eval z = ∑ i, (w i : ℝ) * z ^ (i : ℕ) := by
  simp [finiteLatticePGF, Polynomial.eval_finsetSum]

theorem finiteLatticePGF_coeff (n : ℕ) (w : Fin n → ℝ≥0) (i : Fin n) :
    (finiteLatticePGF n w).coeff (i : ℕ) = (w i : ℝ) := by
  classical
  simp only [finiteLatticePGF, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hbi
    simp [show (b : ℕ) ≠ (i : ℕ) from fun h => hbi (Fin.ext h)]
  · simp

theorem finiteLatticeMeasure_eq_of_pgf_eq (n : ℕ) (w v : Fin n → ℝ≥0)
    (h : finiteLatticePGF n w = finiteLatticePGF n v) :
    finiteLatticeMeasure n w = finiteLatticeMeasure n v := by
  have hwv : w = v := by
    funext i
    apply NNReal.coe_injective
    simpa only [finiteLatticePGF_coeff] using congrArg (fun P => P.coeff (i : ℕ)) h
  rw [hwv]

theorem finiteLatticePGF_eq_of_positive_eval_eq (n : ℕ) (w v : Fin n → ℝ≥0)
    (h : ∀ z : ℝ, 0 < z →
      (finiteLatticePGF n w).eval z = (finiteLatticePGF n v).eval z) :
    finiteLatticePGF n w = finiteLatticePGF n v := by
  apply Polynomial.eq_of_infinite_eval_eq
  exact (Set.Ioi_infinite (0 : ℝ)).mono (fun z hz => h z hz)

theorem finiteLatticeMeasure_eq_of_positive_pgf_eq (n : ℕ) (w v : Fin n → ℝ≥0)
    (h : ∀ z : ℝ, 0 < z →
      (finiteLatticePGF n w).eval z = (finiteLatticePGF n v).eval z) :
    finiteLatticeMeasure n w = finiteLatticeMeasure n v :=
  finiteLatticeMeasure_eq_of_pgf_eq n w v
    (finiteLatticePGF_eq_of_positive_eval_eq n w v h)

/-- The PGF of a finite-valued law is formed from its actual singleton masses. -/
def finiteLawPGF {n : ℕ} (μ : Measure (Fin n)) : Polynomial ℝ :=
  finiteLatticePGF n (fun i => (μ {i}).toNNReal)

theorem finiteLawPGF_eq_implies_law_eq {n : ℕ} (μ ν : Measure (Fin n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : finiteLawPGF μ = finiteLawPGF ν) : μ = ν := by
  apply Measure.ext_of_singleton
  intro i
  have hi : (μ {i}).toNNReal = (ν {i}).toNNReal := by
    apply NNReal.coe_injective
    simpa only [finiteLawPGF, finiteLatticePGF_coeff] using
      congrArg (fun P => P.coeff (i : ℕ)) h
  rw [← ENNReal.coe_toNNReal (measure_ne_top μ {i}),
    ← ENNReal.coe_toNNReal (measure_ne_top ν {i}), hi]

theorem finiteLawPGF_eval_eq_integral {n : ℕ} (μ : Measure (Fin n))
    [IsFiniteMeasure μ] (z : ℝ) :
    (finiteLawPGF μ).eval z = ∫ i, z ^ (i : ℕ) ∂μ := by
  have hint : Integrable (fun i : Fin n => z ^ (i : ℕ)) μ := by
    simpa only [integrableOn_univ] using
      (IntegrableOn.of_finite (Set.finite_univ : (Set.univ : Set (Fin n)).Finite) :
        IntegrableOn (fun i : Fin n => z ^ (i : ℕ)) Set.univ μ)
  rw [integral_fintype hint, finiteLawPGF, finiteLatticePGF_eval]
  rfl

theorem finite_law_eq_of_positive_pgf_integrals {n : ℕ} (μ ν : Measure (Fin n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ z : ℝ, 0 < z →
      (∫ i, z ^ (i : ℕ) ∂μ) = ∫ i, z ^ (i : ℕ) ∂ν) : μ = ν := by
  apply finiteLawPGF_eq_implies_law_eq
  apply finiteLatticePGF_eq_of_positive_eval_eq
  intro z hz
  change (finiteLawPGF μ).eval z = (finiteLawPGF ν).eval z
  simpa only [finiteLawPGF_eval_eq_integral] using h z hz

/-- PGF equality identifies actual pushforward laws, not just parameter lists. -/
theorem finite_pushforward_law_eq_of_positive_pgf_integrals
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {n : ℕ}
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (X : Ω → Fin n) (Y : Ω' → Fin n)
    (h : ∀ z : ℝ, 0 < z →
      (∫ i, z ^ (i : ℕ) ∂μ.map X) = ∫ i, z ^ (i : ℕ) ∂ν.map Y) :
    μ.map X = ν.map Y :=
  finite_law_eq_of_positive_pgf_integrals (μ.map X) (ν.map Y) h

theorem finiteLawPGF_eval_exp_eq_mgf {n : ℕ} (μ : Measure (Fin n))
    [IsFiniteMeasure μ] (t : ℝ) :
    (finiteLawPGF μ).eval (Real.exp t) = mgf (fun i : Fin n => (i : ℝ)) μ t := by
  rw [finiteLawPGF_eval_eq_integral]
  unfold mgf
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun i => by
    simp only [← Real.exp_nat_mul, mul_comm t (i : ℝ)])

theorem finite_law_eq_of_mgf_eq {n : ℕ} (μ ν : Measure (Fin n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, mgf (fun i : Fin n => (i : ℝ)) μ t =
      mgf (fun i : Fin n => (i : ℝ)) ν t) : μ = ν := by
  apply finiteLawPGF_eq_implies_law_eq
  apply finiteLatticePGF_eq_of_positive_eval_eq
  intro z hz
  change (finiteLawPGF μ).eval z = (finiteLawPGF ν).eval z
  rw [← Real.exp_log hz, finiteLawPGF_eval_exp_eq_mgf,
    finiteLawPGF_eval_exp_eq_mgf]
  exact h (Real.log z)

/-- Equality of exponential transforms identifies the real-valued laws of
two finite-lattice random variables on arbitrary probability spaces. -/
theorem finite_pushforward_real_law_eq_of_mgf_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {n : ℕ}
    (μ : Measure Ω) (ν : Measure Ω') [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (X : Ω → Fin n) (Y : Ω' → Fin n) (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ t : ℝ, mgf (fun ω => (X ω : ℝ)) μ t =
      mgf (fun ω => (Y ω : ℝ)) ν t) :
    μ.map (fun ω => (X ω : ℝ)) = ν.map (fun ω => (Y ω : ℝ)) := by
  have hlaw : μ.map X = ν.map Y := by
    apply finite_law_eq_of_mgf_eq
    intro t
    rw [mgf_map hX.aemeasurable (by fun_prop),
      mgf_map hY.aemeasurable (by fun_prop)]
    exact h t
  have hcast : Measurable (fun i : Fin n => (i : ℝ)) := measurable_of_finite _
  calc
    _ = (μ.map X).map (fun i : Fin n => (i : ℝ)) :=
      (Measure.map_map hcast hX).symm
    _ = (ν.map Y).map (fun i : Fin n => (i : ℝ)) := by rw [hlaw]
    _ = _ := Measure.map_map hcast hY

end ExactHoeffding
