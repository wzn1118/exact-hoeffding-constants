import ExactHoeffding.MGFDerivatives
import ExactHoeffding.Sampling
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Pointwise curvature and its integrated proxy

The finite hypergeometric law at `(N,k,m) = (15,7,3)` has an exact rational
tilted variance above the odd-population constant pointwise threshold.
The integrated curvature identity is proved for every centered `C²` function,
then specialized to normalized finite laws and the actual hypergeometric MGF.
-/

namespace ExactHoeffding

noncomputable section

private lemma obstruction_exp (i : ℕ) :
    Real.exp (Real.log (7 / 6 : ℝ) * (i : ℝ)) = (7 / 6 : ℝ) ^ i := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]

private theorem obstruction_mgf :
    hypergeomMGF 15 7 3 (Real.log (7 / 6)) = 3511 / 2808 := by
  unfold hypergeomMGF finiteMGF
  simp_rw [obstruction_exp]
  norm_num [Finset.sum_range_succ, hypergeomMass, hypergeomCount, Nat.choose]

private theorem obstruction_first :
    finiteTiltFirst (Finset.range (3 + 1)) (hypergeomMass 15 7 3)
      (fun i => (i : ℝ)) (Real.log (7 / 6)) = 8771 / 4680 := by
  unfold finiteTiltFirst
  simp_rw [obstruction_exp]
  norm_num [Finset.sum_range_succ, hypergeomMass, hypergeomCount, Nat.choose]

private theorem obstruction_second :
    finiteTiltSecond (Finset.range (3 + 1)) (hypergeomMass 15 7 3)
      (fun i => (i : ℝ)) (Real.log (7 / 6)) = 1127 / 312 := by
  unfold finiteTiltSecond
  simp_rw [obstruction_exp]
  norm_num [Finset.sum_range_succ, hypergeomMass, hypergeomCount, Nat.choose]

/-- Exact tilted mean in the curvature counterexample. -/
theorem hypergeom_curvature_obstruction_mean :
    finiteTiltFirst (Finset.range (3 + 1)) (hypergeomMass 15 7 3)
      (fun i => (i : ℝ)) (Real.log (7 / 6)) /
        hypergeomMGF 15 7 3 (Real.log (7 / 6)) = 26313 / 17555 := by
  rw [obstruction_first, obstruction_mgf]
  norm_num

/-- Exact tilted variance, computed from the actual finite MGF. -/
theorem hypergeom_curvature_obstruction_variance :
    deriv (deriv (fun t => Real.log (hypergeomMGF 15 7 3 t)))
      (Real.log (7 / 6)) = 197927856 / 308178025 := by
  rw [hypergeomLogMGF_second_deriv 15 7 3 (by norm_num) (by norm_num),
    obstruction_mgf, obstruction_first, obstruction_second]
  norm_num

private theorem halfLogOdds_hasDerivAt (x : ℝ) (hx : -1 < x ∧ x < 1) :
    HasDerivAt (fun y : ℝ => 1 / 2 * Real.log ((1 + y) / (1 - y)))
      (1 / (1 - x ^ 2)) x := by
  have hd : 1 - x ≠ 0 := by linarith
  have hn : 1 + x ≠ 0 := by linarith
  have hsq : 1 - x ^ 2 ≠ 0 := by nlinarith
  have h := (((hasDerivAt_id x).const_add 1).div
    ((hasDerivAt_id x).const_sub 1) hd).log (div_ne_zero hn hd)
  apply (h.const_mul (1 / 2)).congr_deriv
  dsimp
  field_simp
  ring

/-- A strict cubic lower bound for artanh at the rational point in the appendix. -/
theorem artanh_one_fifteenth_cubic_lower :
    (1 / 15 : ℝ) + 1 / (3 * 15 ^ 3) < Real.artanh (1 / 15) := by
  let f : ℝ → ℝ := fun x =>
    1 / 2 * Real.log ((1 + x) / (1 - x)) - x - x ^ 3 / 3
  have hf (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) (1 / 15)) :
      HasDerivAt f (x ^ 4 / (1 - x ^ 2)) x := by
    have hx' : -1 < x ∧ x < 1 := by constructor <;> linarith [hx.1, hx.2]
    have hs : 1 - x ^ 2 ≠ 0 := by nlinarith [hx'.1, hx'.2]
    have h := ((halfLogOdds_hasDerivAt x hx').sub (hasDerivAt_id x)).sub
      (((hasDerivAt_id x).pow 3).div_const 3)
    apply h.congr_deriv
    dsimp
    field_simp
    ring
  have hmono : StrictMonoOn f (Set.Icc (0 : ℝ) (1 / 15)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hf x ⟨le_of_lt hx.1, le_of_lt hx.2⟩).deriv]
      apply div_pos (pow_pos hx.1 4)
      nlinarith [hx.1, hx.2]
  have hlt := hmono (by norm_num : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 15))
    (by norm_num : (1 / 15 : ℝ) ∈ Set.Icc (0 : ℝ) (1 / 15)) (by norm_num)
  rw [Real.artanh_eq_half_log (by norm_num :
    (1 / 15 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)]
  dsimp [f] at hlt
  norm_num at hlt ⊢
  linarith

/-- The rational threshold lies strictly above the exact odd-population factor. -/
theorem curvature_obstruction_rho_lt :
    1 / (15 * Real.artanh (1 / 15)) < (675 / 676 : ℝ) := by
  have h := artanh_one_fifteenth_cubic_lower
  have hp : 0 < 15 * Real.artanh (1 / 15) := by nlinarith
  apply (div_lt_iff₀ hp).2
  nlinarith

/-- The exact normalized curvature exceeds both the rational threshold and rho. -/
theorem hypergeom_curvature_obstruction :
    (14 / 9 : ℝ) * deriv (deriv (fun t => Real.log (hypergeomMGF 15 7 3 t)))
        (Real.log (7 / 6)) = 307887776 / 308178025 ∧
      (675 / 676 : ℝ) < 307887776 / 308178025 ∧
      1 / (15 * Real.artanh (1 / 15)) < (675 / 676 : ℝ) := by
  refine ⟨?_, ?_, curvature_obstruction_rho_lt⟩
  · rw [hypergeom_curvature_obstruction_variance]
    norm_num
  · norm_num

/-- Centering changes the log MGF by a linear function and preserves its
second derivative at every tilt. -/
theorem centeredHypergeomLogMGF_second_deriv (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    deriv (deriv (fun u => Real.log (centeredHypergeomMGF N k m u))) t =
      deriv (deriv (fun u => Real.log (hypergeomMGF N k m u))) t := by
  have hlog : (fun u => Real.log (centeredHypergeomMGF N k m u)) =
      (fun u => Real.log (hypergeomMGF N k m u) - (k : ℝ) * m / N * u) := by
    funext u
    have hp : 0 < hypergeomMGF N k m u :=
      finiteMGF_pos_of_normalized (Finset.range (m + 1))
      (hypergeomMass N k m) (fun i => (i : ℝ))
      (fun i _ => hypergeomMass_nonneg N k m i) (hypergeomMass_total N k m hk hm) u
    rw [centeredHypergeomMGF_factor,
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hp), Real.log_exp]
    ring
  have hfirst : deriv (fun u => Real.log (centeredHypergeomMGF N k m u)) =
      (fun u => deriv (fun v => Real.log (hypergeomMGF N k m v)) u -
        (k : ℝ) * m / N) := by
    rw [hlog]
    funext u
    rw [deriv_fun_sub
      (((hypergeom_logMGF_contDiff N k m 1 hk hm).differentiable (by norm_num)) u)
      (by fun_prop), deriv_const_mul_id]
  rw [hfirst, deriv_sub_const]

/-- The appendix counterexample as an inequality for the actual centered log
MGF, with the paper's finite-population variance scale. -/
theorem hypergeom_centered_curvature_pointwise_bound_fails :
    1 / (15 * Real.artanh (1 / 15)) *
        ((3 : ℝ) * (15 - 3) / (4 * (15 - 1))) <
      deriv (deriv (fun t => Real.log (centeredHypergeomMGF 15 7 3 t)))
        (Real.log (7 / 6)) := by
  rw [centeredHypergeomLogMGF_second_deriv 15 7 3 (by norm_num) (by norm_num),
    hypergeom_curvature_obstruction_variance]
  have h := curvature_obstruction_rho_lt
  norm_num at h ⊢
  linarith

/-- Twice-integrated curvature for any centered `C²` function, for either sign
of the nonzero tilt. -/
theorem centered_integrated_curvature (ψ : ℝ → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (hzero : ψ 0 = 0) (hderivzero : deriv ψ 0 = 0) (t : ℝ) (ht : t ≠ 0) :
    2 * ψ t / t ^ 2 =
      2 * ∫ u : ℝ in (0 : ℝ)..1, (1 - u) * deriv (deriv ψ) (u * t) := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv ψ) := hψ.differentiable_deriv_two
  have hc : Continuous (deriv (deriv ψ)) :=
    (hψ.deriv' : ContDiff ℝ 1 (deriv ψ)).continuous_deriv_one
  let F : ℝ → ℝ := fun u => ψ (u * t) + (1 - u) * t * deriv ψ (u * t)
  have hF (u : ℝ) : HasDerivAt F
      (t ^ 2 * ((1 - u) * deriv (deriv ψ) (u * t))) u := by
    have hu := (hasDerivAt_id u).mul_const t
    have h₁ := (hd (u * t)).hasDerivAt.comp u hu
    have h₂ := (hdd (u * t)).hasDerivAt.comp u hu
    have h₃ := (((hasDerivAt_id u).const_sub 1).mul_const t).mul h₂
    apply (h₁.add h₃).congr_deriv
    dsimp
    ring
  have hint : IntervalIntegrable
      (fun u : ℝ => t ^ 2 * ((1 - u) * deriv (deriv ψ) (u * t)))
        MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((continuous_const.sub continuous_id).mul
      (hc.comp (continuous_id.mul continuous_const)))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u) hint
  rw [intervalIntegral.integral_const_mul] at hi
  dsimp [F] at hi
  simp only [one_mul, zero_mul, sub_self, mul_zero, add_zero,
    sub_zero, hzero, hderivzero] at hi
  rw [← hi]
  field_simp

/-- Curvature integral for the log MGF of any centered normalized finite law. -/
theorem finiteLogMGF_integrated_curvature {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : ∑ i ∈ s, w i = 1)
    (hmean : ∑ i ∈ s, w i * x i = 0) (t : ℝ) (ht : t ≠ 0) :
    2 * Real.log (finiteMGF s w x t) / t ^ 2 =
      2 * ∫ u : ℝ in (0 : ℝ)..1,
        (1 - u) * deriv (deriv (fun v => Real.log (finiteMGF s w x v))) (u * t) := by
  apply centered_integrated_curvature _ (finiteLogMGF_contDiff s w x hw hs 2) _ _ t ht
  · rw [finiteMGF_zero_of_normalized s w x hs, Real.log_one]
  · rw [(finiteLogMGF_hasDerivAt s w x hw hs 0).deriv]
    simp [finiteTiltFirst, hmean]

/-- The integrated identity for the actual centered hypergeometric log MGF,
including every valid degenerate population and sample size. -/
theorem hypergeomLogMGF_integrated_curvature (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) (ht : t ≠ 0) :
    2 * Real.log (centeredHypergeomMGF N k m t) / t ^ 2 =
      2 * ∫ u : ℝ in (0 : ℝ)..1, (1 - u) *
        deriv (deriv (fun v => Real.log (centeredHypergeomMGF N k m v))) (u * t) := by
  apply finiteLogMGF_integrated_curvature (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ) - (k : ℝ) * m / N)
    (fun i _ => hypergeomMass_nonneg N k m i) (hypergeomMass_total N k m hk hm) _ t ht
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hypergeomMass_total N k m hk hm]
  have hmean := hypergeom_mean_complete N k m hk hm
  simp_rw [mul_comm (hypergeomMass N k m _) (_ : ℝ)]
  rw [hmean]
  ring

end

end ExactHoeffding
