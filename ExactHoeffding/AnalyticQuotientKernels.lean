import ExactHoeffding.RescaledMGFBridge
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Explicit analytic kernels for removing the quadratic tilt singularity

The divided differences are defined at zero using actual derivatives.
Their analyticity follows from convergent power series, not a smoothness
assumption on the quotient one wants to prove analytic.
-/

namespace ExactHoeffding

noncomputable section

open scoped Topology

def expSlopeKernel : ℝ → ℝ := dslope Real.exp 0

def expQuadraticKernel : ℝ → ℝ := dslope expSlopeKernel 0

def logOnePlus : ℝ → ℝ := fun z => Real.log (1 + z)

def logSlopeKernel : ℝ → ℝ := dslope logOnePlus 0

def logQuadraticKernel : ℝ → ℝ := dslope logSlopeKernel 0

theorem analyticAt_dslope_zero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    AnalyticAt ℝ (dslope f 0) 0 := by
  obtain ⟨p, hp⟩ := hf
  exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩

theorem expSlopeKernel_analytic : AnalyticAt ℝ expSlopeKernel 0 := by
  exact analyticAt_dslope_zero analyticAt_rexp

theorem expQuadraticKernel_analytic : AnalyticAt ℝ expQuadraticKernel 0 := by
  exact analyticAt_dslope_zero expSlopeKernel_analytic

theorem logSlopeKernel_analytic : AnalyticAt ℝ logSlopeKernel 0 := by
  exact analyticAt_dslope_zero hasFPowerSeriesAt_log_one_add.analyticAt

theorem logQuadraticKernel_analytic : AnalyticAt ℝ logQuadraticKernel 0 := by
  exact analyticAt_dslope_zero logSlopeKernel_analytic

@[simp] theorem expSlopeKernel_zero : expSlopeKernel 0 = 1 := by
  simp [expSlopeKernel, Real.deriv_exp]

@[simp] theorem logSlopeKernel_zero : logSlopeKernel 0 = 1 := by
  unfold logSlopeKernel
  rw [dslope_same]
  change deriv (fun z : ℝ => Real.log (1 + z)) 0 = 1
  simpa using hasFPowerSeriesAt_log_one_add.deriv

@[simp] theorem logQuadraticKernel_zero : logQuadraticKernel 0 = -(1 / 2 : ℝ) := by
  have h := hasFPowerSeriesAt_log_one_add.has_fpower_series_dslope_fslope
    |>.has_fpower_series_dslope_fslope
  have hz := h.coeff_zero 1
  unfold logQuadraticKernel logSlopeKernel logOnePlus
  rw [dslope_same]
  norm_num [FormalMultilinearSeries.coeff_fslope] at hz
  exact hz.symm

theorem exp_sub_one_factor (t : ℝ) : Real.exp t - 1 = t * expSlopeKernel t := by
  simpa [expSlopeKernel, smul_eq_mul] using (sub_smul_dslope Real.exp 0 t).symm

theorem expSlopeKernel_factor (t : ℝ) :
    expSlopeKernel t - 1 = t * expQuadraticKernel t := by
  simpa [expQuadraticKernel, smul_eq_mul] using
    (sub_smul_dslope expSlopeKernel 0 t).symm

theorem logOnePlus_quadratic_factor (z : ℝ) :
    Real.log (1 + z) = z + z ^ 2 * logQuadraticKernel z := by
  have h1 := sub_smul_dslope logOnePlus 0 z
  have h2 := sub_smul_dslope logSlopeKernel 0 z
  simp only [sub_zero, smul_eq_mul, logOnePlus, add_zero, Real.log_one,
    sub_zero] at h1
  change z * logSlopeKernel z = Real.log (1 + z) at h1
  simp only [sub_zero, smul_eq_mul, logSlopeKernel_zero] at h2
  change z * logQuadraticKernel z = logSlopeKernel z - 1 at h2
  nlinarith [congrArg (fun r : ℝ => z * r) h2]

end

end ExactHoeffding
