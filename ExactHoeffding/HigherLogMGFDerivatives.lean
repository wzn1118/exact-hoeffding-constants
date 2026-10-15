import ExactHoeffding.MGFDerivatives
import ExactHoeffding.HighCumulants

/-!
# Fifth and sixth derivatives of finite log-MGFs

The identities here continue the actual finite tilted-moment calculation to
orders five and six.  They are stated for arbitrary finite weighted laws and
then specialized to the hypergeometric mass function.
-/

namespace ExactHoeffding

noncomputable section

open scoped Topology

/-- The fifth logarithmic derivative polynomial evaluated at tilted raw moments. -/
def higherFiniteLogDerivative5 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  cumulant5Polynomial
    (finiteTiltedRawMoment s w x 1 t)
    (finiteTiltedRawMoment s w x 2 t)
    (finiteTiltedRawMoment s w x 3 t)
    (finiteTiltedRawMoment s w x 4 t)
    (finiteTiltedRawMoment s w x 5 t)

/-- The sixth logarithmic derivative polynomial evaluated at tilted raw moments. -/
def higherFiniteLogDerivative6 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  cumulant6Polynomial
    (finiteTiltedRawMoment s w x 1 t)
    (finiteTiltedRawMoment s w x 2 t)
    (finiteTiltedRawMoment s w x 3 t)
    (finiteTiltedRawMoment s w x 4 t)
    (finiteTiltedRawMoment s w x 5 t)
    (finiteTiltedRawMoment s w x 6 t)

private def higherFiniteLogDerivative2 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  finiteTiltedRawMoment s w x 2 t - finiteTiltedRawMoment s w x 1 t ^ 2

private def higherFiniteLogDerivative3 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  finiteTiltedRawMoment s w x 3 t -
    3 * finiteTiltedRawMoment s w x 2 t * finiteTiltedRawMoment s w x 1 t +
    2 * finiteTiltedRawMoment s w x 1 t ^ 3

private def higherFiniteLogDerivative4 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ) (t : ℝ) : ℝ :=
  finiteTiltedRawMoment s w x 4 t -
    4 * finiteTiltedRawMoment s w x 3 t * finiteTiltedRawMoment s w x 1 t -
    3 * finiteTiltedRawMoment s w x 2 t ^ 2 +
    12 * finiteTiltedRawMoment s w x 2 t * finiteTiltedRawMoment s w x 1 t ^ 2 -
    6 * finiteTiltedRawMoment s w x 1 t ^ 4

private theorem higherFiniteLog_deriv1 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (fun u => Real.log (finiteMGF s w x u))
      (finiteTiltedRawMoment s w x 1 t) t := by
  have hM : HasDerivAt (finiteMGF s w x) (finiteTiltMoment s w x 1 t) t := by
    simpa only [finiteTiltMoment_order_zero] using
      finiteTiltMoment_hasDerivAt s w x 0 t
  exact hM.log (ne_of_gt (finiteMGF_pos_of_normalized s w x hw hs t))

private theorem higherFiniteLog_deriv2 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (finiteTiltedRawMoment s w x 1)
      (higherFiniteLogDerivative2 s w x t) t := by
  simpa only [higherFiniteLogDerivative2, pow_two] using
    finiteTiltedRawMoment_hasDerivAt s w x hw hs 1 t

private theorem higherFiniteLog_deriv3 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (higherFiniteLogDerivative2 s w x)
      (higherFiniteLogDerivative3 s w x t) t := by
  have h1 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 1 t
  have h2 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 2 t
  change HasDerivAt
    (fun u => finiteTiltedRawMoment s w x 2 u -
      finiteTiltedRawMoment s w x 1 u ^ 2) _ t
  apply (h2.sub (h1.pow 2)).congr_deriv
  dsimp [higherFiniteLogDerivative3]
  norm_num
  ring

private theorem higherFiniteLog_deriv4 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (higherFiniteLogDerivative3 s w x)
      (higherFiniteLogDerivative4 s w x t) t := by
  have h1 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 1 t
  have h2 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 2 t
  have h3 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 3 t
  change HasDerivAt
    (fun u => finiteTiltedRawMoment s w x 3 u -
      3 * finiteTiltedRawMoment s w x 2 u * finiteTiltedRawMoment s w x 1 u +
      2 * finiteTiltedRawMoment s w x 1 u ^ 3) _ t
  apply ((h3.sub ((h2.const_mul 3).mul h1)).add
    ((h1.pow 3).const_mul 2)).congr_deriv
  dsimp [higherFiniteLogDerivative4]
  ring

private theorem higherFiniteLog_deriv5 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (higherFiniteLogDerivative4 s w x)
      (higherFiniteLogDerivative5 s w x t) t := by
  have h1 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 1 t
  have h2 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 2 t
  have h3 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 3 t
  have h4 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 4 t
  change HasDerivAt
    (fun u => finiteTiltedRawMoment s w x 4 u -
      4 * finiteTiltedRawMoment s w x 3 u * finiteTiltedRawMoment s w x 1 u -
      3 * finiteTiltedRawMoment s w x 2 u ^ 2 +
      12 * finiteTiltedRawMoment s w x 2 u * finiteTiltedRawMoment s w x 1 u ^ 2 -
      6 * finiteTiltedRawMoment s w x 1 u ^ 4) _ t
  have hp := ((h4.sub ((h3.const_mul 4).mul h1)).sub
      ((h2.pow 2).const_mul 3)).add
    (((h2.mul (h1.pow 2)).const_mul 12).sub
      ((h1.pow 4).const_mul 6))
  have hpd : HasDerivAt
      (((finiteTiltedRawMoment s w x 4 -
          (fun y => 4 * finiteTiltedRawMoment s w x 3 y) *
            finiteTiltedRawMoment s w x 1 -
          (fun y => 3 * (finiteTiltedRawMoment s w x 2 ^ 2) y)) +
        ((fun y => 12 *
            (finiteTiltedRawMoment s w x 2 * finiteTiltedRawMoment s w x 1 ^ 2) y) -
          (fun y => 6 * (finiteTiltedRawMoment s w x 1 ^ 4) y))))
      (higherFiniteLogDerivative5 s w x t) t := by
    apply hp.congr_deriv
    dsimp [higherFiniteLogDerivative5, cumulant5Polynomial]
    ring
  apply hpd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun u => by
    dsimp [higherFiniteLogDerivative4]
    ring)

private theorem higherFiniteLog_deriv6 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) (t : ℝ) :
    HasDerivAt (higherFiniteLogDerivative5 s w x)
      (higherFiniteLogDerivative6 s w x t) t := by
  have h1 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 1 t
  have h2 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 2 t
  have h3 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 3 t
  have h4 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 4 t
  have h5 := finiteTiltedRawMoment_hasDerivAt s w x hw hs 5 t
  change HasDerivAt
    (fun u =>
      finiteTiltedRawMoment s w x 5 u -
        5 * finiteTiltedRawMoment s w x 4 u * finiteTiltedRawMoment s w x 1 u -
        10 * finiteTiltedRawMoment s w x 3 u * finiteTiltedRawMoment s w x 2 u +
        20 * finiteTiltedRawMoment s w x 3 u * finiteTiltedRawMoment s w x 1 u ^ 2 +
        30 * finiteTiltedRawMoment s w x 2 u ^ 2 * finiteTiltedRawMoment s w x 1 u -
        60 * finiteTiltedRawMoment s w x 2 u * finiteTiltedRawMoment s w x 1 u ^ 3 +
        24 * finiteTiltedRawMoment s w x 1 u ^ 5) _ t
  have hp := h5.sub ((h4.const_mul 5).mul h1)
  have hp := hp.sub ((h3.const_mul 10).mul h2)
  have hp := hp.add ((h3.mul (h1.pow 2)).const_mul 20)
  have hp := hp.add (((h2.pow 2).mul h1).const_mul 30)
  have hp := hp.sub ((h2.mul (h1.pow 3)).const_mul 60)
  have hp := hp.add ((h1.pow 5).const_mul 24)
  have hpd : HasDerivAt
      (((((finiteTiltedRawMoment s w x 5 -
          (fun y => 5 * finiteTiltedRawMoment s w x 4 y) *
            finiteTiltedRawMoment s w x 1 -
          (fun y => 10 * finiteTiltedRawMoment s w x 3 y) *
            finiteTiltedRawMoment s w x 2 +
          (fun y => 20 *
            (finiteTiltedRawMoment s w x 3 * finiteTiltedRawMoment s w x 1 ^ 2) y)) +
        (fun y => 30 *
          (finiteTiltedRawMoment s w x 2 ^ 2 * finiteTiltedRawMoment s w x 1) y)) -
        (fun y => 60 *
          (finiteTiltedRawMoment s w x 2 * finiteTiltedRawMoment s w x 1 ^ 3) y)) +
        (fun y => 24 * (finiteTiltedRawMoment s w x 1 ^ 5) y)))
      (higherFiniteLogDerivative6 s w x t) t := by
    apply hp.congr_deriv
    dsimp [higherFiniteLogDerivative6, cumulant6Polynomial]
    ring
  apply hpd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun u => by
    dsimp [higherFiniteLogDerivative5]
    ring)

private theorem higherFiniteLog_iteratedDeriv1 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 1 (fun t => Real.log (finiteMGF s w x t)) =
      finiteTiltedRawMoment s w x 1 := by
  rw [iteratedDeriv_one]
  funext t
  exact (higherFiniteLog_deriv1 s w x hw hs t).deriv

private theorem higherFiniteLog_iteratedDeriv2 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 2 (fun t => Real.log (finiteMGF s w x t)) =
      higherFiniteLogDerivative2 s w x := by
  rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ,
    higherFiniteLog_iteratedDeriv1 s w x hw hs]
  funext t
  exact (higherFiniteLog_deriv2 s w x hw hs t).deriv

private theorem higherFiniteLog_iteratedDeriv3 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 3 (fun t => Real.log (finiteMGF s w x t)) =
      higherFiniteLogDerivative3 s w x := by
  rw [show 3 = 2 + 1 by rfl, iteratedDeriv_succ,
    higherFiniteLog_iteratedDeriv2 s w x hw hs]
  funext t
  exact (higherFiniteLog_deriv3 s w x hw hs t).deriv

private theorem higherFiniteLog_iteratedDeriv4 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 4 (fun t => Real.log (finiteMGF s w x t)) =
      higherFiniteLogDerivative4 s w x := by
  rw [show 4 = 3 + 1 by rfl, iteratedDeriv_succ,
    higherFiniteLog_iteratedDeriv3 s w x hw hs]
  funext t
  exact (higherFiniteLog_deriv4 s w x hw hs t).deriv

private theorem higherFiniteLog_iteratedDeriv5 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 5 (fun t => Real.log (finiteMGF s w x t)) =
      higherFiniteLogDerivative5 s w x := by
  rw [show 5 = 4 + 1 by rfl, iteratedDeriv_succ,
    higherFiniteLog_iteratedDeriv4 s w x hw hs]
  funext t
  exact (higherFiniteLog_deriv5 s w x hw hs t).deriv

private theorem higherFiniteLog_iteratedDeriv6 {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 6 (fun t => Real.log (finiteMGF s w x t)) =
      higherFiniteLogDerivative6 s w x := by
  rw [show 6 = 5 + 1 by rfl, iteratedDeriv_succ,
    higherFiniteLog_iteratedDeriv5 s w x hw hs]
  funext t
  exact (higherFiniteLog_deriv6 s w x hw hs t).deriv

/-- The actual fifth log-MGF derivative at zero is the fifth cumulant. -/
theorem finiteLogMGF_deriv5_zero_cumulant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 5 (fun t => Real.log (finiteMGF s w x t)) 0 =
      finiteCumulant5 s x w := by
  rw [higherFiniteLog_iteratedDeriv5 s w x hw hs]
  simp only [higherFiniteLogDerivative5,
    finiteTiltedRawMoment_at_zero s w x hs, finiteCumulant5]

/-- The actual sixth log-MGF derivative at zero is the sixth cumulant. -/
theorem finiteLogMGF_deriv6_zero_cumulant {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1) :
    iteratedDeriv 6 (fun t => Real.log (finiteMGF s w x t)) 0 =
      finiteCumulant6 s x w := by
  rw [higherFiniteLog_iteratedDeriv6 s w x hw hs]
  simp only [higherFiniteLogDerivative6,
    finiteTiltedRawMoment_at_zero s w x hs, finiteCumulant6]

/-- The fifth hypergeometric log-MGF derivative is its actual fifth cumulant. -/
theorem hypergeom_logMGF_deriv5_zero (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    iteratedDeriv 5 (fun t => Real.log (hypergeomMGF N k m t)) 0 =
      hypergeomCumulant5 N k m := by
  exact finiteLogMGF_deriv5_zero_cumulant (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i)
    (hypergeomMass_total N k m hk hm)

/-- The sixth hypergeometric log-MGF derivative is its actual sixth cumulant. -/
theorem hypergeom_logMGF_deriv6_zero (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    iteratedDeriv 6 (fun t => Real.log (hypergeomMGF N k m t)) 0 =
      hypergeomCumulant6 N k m := by
  exact finiteLogMGF_deriv6_zero_cumulant (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i)
    (hypergeomMass_total N k m hk hm)

end

end ExactHoeffding
