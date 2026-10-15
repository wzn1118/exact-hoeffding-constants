import ExactHoeffding.Cumulants
import ExactHoeffding.TiltedVariance
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Actual finite MGF and log-MGF derivatives

All derivative identities below concern the finite exponential sum itself.
In particular, the cumulant polynomials from `Cumulants` are identified with
the actual iterated derivatives of its logarithm, rather than assumed to be
derivatives by definition. The hypergeometric specializations include every
valid finite population, including the degenerate populations of sizes zero
and one.
-/

namespace ExactHoeffding

noncomputable section

open scoped Topology

/-- The unnormalized tilted raw moment of degree `r`. -/
def finiteTiltMoment {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w x : ι → ℝ) (r : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, (x i ^ r * w i) * Real.exp (t * x i)

theorem finiteTiltMoment_order_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) :
    finiteTiltMoment s w x 0 = finiteMGF s w x := by
  funext t
  simp [finiteTiltMoment, finiteMGF]

theorem finiteTiltMoment_at_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (r : ℕ) :
    finiteTiltMoment s w x r 0 = finiteRawMoment s x w r := by
  simp [finiteTiltMoment, finiteRawMoment]

/-- Differentiating a finite tilted moment raises its degree by one. -/
theorem finiteTiltMoment_hasDerivAt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (r : ℕ) (t : ℝ) :
    HasDerivAt (finiteTiltMoment s w x r)
      (finiteTiltMoment s w x (r + 1) t) t := by
  have hi (i : ι) :
      HasDerivAt (fun u : ℝ => (x i ^ r * w i) * Real.exp (u * x i))
        ((x i ^ (r + 1) * w i) * Real.exp (t * x i)) t := by
    have hinner : HasDerivAt (fun u : ℝ => u * x i) (x i) t := by
      simpa using (hasDerivAt_id t).mul_const (x i)
    simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
      hinner.exp.const_mul (x i ^ r * w i)
  exact HasDerivAt.fun_sum (fun i _ => hi i)

/-- Every iterated derivative of the actual finite MGF is its tilted moment. -/
theorem finiteMGF_iteratedDeriv {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (r : ℕ) :
    iteratedDeriv r (finiteMGF s w x) = finiteTiltMoment s w x r := by
  induction r with
  | zero =>
      rw [iteratedDeriv_zero, finiteTiltMoment_order_zero]
  | succ r ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact (finiteTiltMoment_hasDerivAt s w x r t).deriv

/-- At zero the actual MGF derivatives are the ordinary raw moments. -/
theorem finiteMGF_iteratedDeriv_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (r : ℕ) :
    iteratedDeriv r (finiteMGF s w x) 0 = finiteRawMoment s x w r := by
  rw [finiteMGF_iteratedDeriv, finiteTiltMoment_at_zero]

theorem hypergeomMGF_iteratedDeriv_zero (N k m r : ℕ) :
    iteratedDeriv r (hypergeomMGF N k m) 0 = hypergeomRawMoment N k m r := by
  exact finiteMGF_iteratedDeriv_zero (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ)) r

theorem finiteTiltMoment_contDiff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (r n : ℕ) :
    ContDiff ℝ n (finiteTiltMoment s w x r) := by
  unfold finiteTiltMoment
  apply ContDiff.sum
  intro i hi
  exact contDiff_const.mul ((contDiff_id.mul contDiff_const).exp)

/-- The normalized raw moment after exponential tilting. -/
def finiteTiltedRawMoment {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (w x : ι → ℝ) (r : ℕ) (t : ℝ) : ℝ :=
  finiteTiltMoment s w x r t / finiteMGF s w x t

theorem finiteTiltedRawMoment_at_zero {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (hs : ∑ i ∈ s, w i = 1) (r : ℕ) :
    finiteTiltedRawMoment s w x r 0 = finiteRawMoment s x w r := by
  rw [finiteTiltedRawMoment, finiteTiltMoment_at_zero,
    finiteMGF_zero_of_normalized s w x hs, div_one]

/-- The exact differential recursion for the tilted raw moments. -/
theorem finiteTiltedRawMoment_hasDerivAt {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (r : ℕ) (t : ℝ) :
    HasDerivAt (finiteTiltedRawMoment s w x r)
      (finiteTiltedRawMoment s w x (r + 1) t -
        finiteTiltedRawMoment s w x r t * finiteTiltedRawMoment s w x 1 t) t := by
  have hM : HasDerivAt (finiteMGF s w x) (finiteTiltMoment s w x 1 t) t := by
    simpa only [finiteTiltMoment_order_zero] using
      finiteTiltMoment_hasDerivAt s w x 0 t
  have hne := ne_of_gt (finiteMGF_pos_of_normalized s w x hw hs t)
  have hquot := (finiteTiltMoment_hasDerivAt s w x r t).div hM hne
  change HasDerivAt
    (fun u => finiteTiltMoment s w x r u / finiteMGF s w x u) _ t
  apply hquot.congr_deriv
  dsimp [finiteTiltedRawMoment]
  field_simp [hne]

private def finiteLogDerivative2 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  finiteTiltedRawMoment s w x 2 t - finiteTiltedRawMoment s w x 1 t ^ 2

private def finiteLogDerivative3 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  finiteTiltedRawMoment s w x 3 t -
    3 * finiteTiltedRawMoment s w x 2 t * finiteTiltedRawMoment s w x 1 t +
    2 * finiteTiltedRawMoment s w x 1 t ^ 3

private def finiteLogDerivative4 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  finiteTiltedRawMoment s w x 4 t -
    4 * finiteTiltedRawMoment s w x 3 t * finiteTiltedRawMoment s w x 1 t -
    3 * finiteTiltedRawMoment s w x 2 t ^ 2 +
    12 * finiteTiltedRawMoment s w x 2 t * finiteTiltedRawMoment s w x 1 t ^ 2 -
    6 * finiteTiltedRawMoment s w x 1 t ^ 4

private theorem finiteLog_deriv1 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (fun u => Real.log (finiteMGF s w x u))
      (finiteTiltedRawMoment s w x 1 t) t := by
  have hM : HasDerivAt (finiteMGF s w x) (finiteTiltMoment s w x 1 t) t := by
    simpa only [finiteTiltMoment_order_zero] using
      finiteTiltMoment_hasDerivAt s w x 0 t
  exact hM.log (ne_of_gt (finiteMGF_pos_of_normalized s w x hw hs t))

private theorem finiteLog_deriv2 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (finiteTiltedRawMoment s w x 1)
      (finiteLogDerivative2 s w x t) t := by
  simpa only [finiteLogDerivative2, pow_two] using
    finiteTiltedRawMoment_hasDerivAt s w x hw hs 1 t

private theorem finiteLog_deriv3 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (finiteLogDerivative2 s w x) (finiteLogDerivative3 s w x t) t := by
  have h1 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 1 t
  have h2 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 2 t
  change HasDerivAt
    (fun u => finiteTiltedRawMoment s w x 2 u -
      finiteTiltedRawMoment s w x 1 u ^ 2) _ t
  apply (h2.sub (h1.pow 2)).congr_deriv
  dsimp [finiteLogDerivative3]
  norm_num
  ring

private theorem finiteLog_deriv4 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (finiteLogDerivative3 s w x) (finiteLogDerivative4 s w x t) t := by
  have h1 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 1 t
  have h2 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 2 t
  have h3 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 3 t
  change HasDerivAt
    (fun u => finiteTiltedRawMoment s w x 3 u -
      3 * finiteTiltedRawMoment s w x 2 u * finiteTiltedRawMoment s w x 1 u +
      2 * finiteTiltedRawMoment s w x 1 u ^ 3) _ t
  apply ((h3.sub ((h2.const_mul 3).mul h1)).add
    ((h1.pow 3).const_mul 2)).congr_deriv
  dsimp [finiteLogDerivative4]
  ring

private theorem finiteLog_iteratedDeriv1 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 1 (fun t => Real.log (finiteMGF s w x t)) =
      finiteTiltedRawMoment s w x 1 := by
  rw [iteratedDeriv_one]
  funext t
  exact (finiteLog_deriv1 s w x hw hs t).deriv

private theorem finiteLog_iteratedDeriv2 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 2 (fun t => Real.log (finiteMGF s w x t)) =
      finiteLogDerivative2 s w x := by
  rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ,
    finiteLog_iteratedDeriv1 s w x hw hs]
  funext t
  exact (finiteLog_deriv2 s w x hw hs t).deriv

private theorem finiteLog_iteratedDeriv3 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 3 (fun t => Real.log (finiteMGF s w x t)) =
      finiteLogDerivative3 s w x := by
  rw [show 3 = 2 + 1 by rfl, iteratedDeriv_succ,
    finiteLog_iteratedDeriv2 s w x hw hs]
  funext t
  exact (finiteLog_deriv3 s w x hw hs t).deriv

private theorem finiteLog_iteratedDeriv4 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 4 (fun t => Real.log (finiteMGF s w x t)) =
      finiteLogDerivative4 s w x := by
  rw [show 4 = 3 + 1 by rfl, iteratedDeriv_succ,
    finiteLog_iteratedDeriv3 s w x hw hs]
  funext t
  exact (finiteLog_deriv4 s w x hw hs t).deriv

/-- The actual first logarithmic derivative at zero is the first cumulant. -/
theorem finiteLogMGF_deriv1_zero_cumulant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 1 (fun t => Real.log (finiteMGF s w x t)) 0 =
      finiteCumulant1 s x w := by
  rw [finiteLog_iteratedDeriv1 s w x hw hs,
    finiteTiltedRawMoment_at_zero s w x hs]
  rfl

theorem finiteLogMGF_deriv2_zero_cumulant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 2 (fun t => Real.log (finiteMGF s w x t)) 0 =
      finiteCumulant2 s x w := by
  rw [finiteLog_iteratedDeriv2 s w x hw hs]
  simp only [finiteLogDerivative2, finiteTiltedRawMoment_at_zero s w x hs,
    finiteCumulant2]

theorem finiteLogMGF_deriv3_zero_cumulant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 3 (fun t => Real.log (finiteMGF s w x t)) 0 =
      finiteCumulant3 s x w := by
  rw [finiteLog_iteratedDeriv3 s w x hw hs]
  simp only [finiteLogDerivative3, finiteTiltedRawMoment_at_zero s w x hs,
    finiteCumulant3]

theorem finiteLogMGF_deriv4_zero_cumulant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 4 (fun t => Real.log (finiteMGF s w x t)) 0 =
      finiteCumulant4 s x w := by
  rw [finiteLog_iteratedDeriv4 s w x hw hs]
  simp only [finiteLogDerivative4, finiteTiltedRawMoment_at_zero s w x hs,
    finiteCumulant4]

theorem finiteLogMGF_contDiff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (n : ℕ) :
    ContDiff ℝ n (fun t => Real.log (finiteMGF s w x t)) := by
  have hM : ContDiff ℝ n (finiteMGF s w x) := by
    simpa only [finiteTiltMoment_order_zero] using
      finiteTiltMoment_contDiff s w x 0 n
  exact hM.log (fun t => ne_of_gt (finiteMGF_pos_of_normalized s w x hw hs t))

theorem hypergeom_logMGF_deriv1_zero (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    iteratedDeriv 1 (fun t => Real.log (hypergeomMGF N k m t)) 0 =
      hypergeomCumulant1 N k m := by
  exact finiteLogMGF_deriv1_zero_cumulant (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i) (hypergeomMass_total N k m hk hm)

theorem hypergeom_logMGF_deriv2_zero (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    iteratedDeriv 2 (fun t => Real.log (hypergeomMGF N k m t)) 0 =
      hypergeomCumulant2 N k m := by
  exact finiteLogMGF_deriv2_zero_cumulant (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i) (hypergeomMass_total N k m hk hm)

theorem hypergeom_logMGF_deriv3_zero (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    iteratedDeriv 3 (fun t => Real.log (hypergeomMGF N k m t)) 0 =
      hypergeomCumulant3 N k m := by
  exact finiteLogMGF_deriv3_zero_cumulant (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i) (hypergeomMass_total N k m hk hm)

theorem hypergeom_logMGF_deriv4_zero (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    iteratedDeriv 4 (fun t => Real.log (hypergeomMGF N k m t)) 0 =
      hypergeomCumulant4 N k m := by
  exact finiteLogMGF_deriv4_zero_cumulant (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i) (hypergeomMass_total N k m hk hm)

theorem hypergeom_logMGF_contDiff (N k m n : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    ContDiff ℝ n (fun t => Real.log (hypergeomMGF N k m t)) := by
  exact finiteLogMGF_contDiff (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i) (hypergeomMass_total N k m hk hm) n

end

end ExactHoeffding
