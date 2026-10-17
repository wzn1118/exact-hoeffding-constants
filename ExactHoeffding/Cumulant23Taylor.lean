import ExactHoeffding.HighCumulants
import ExactHoeffding.RealMarginMoments

/-!
# The full second- and third-cumulant Taylor expansions

The cumulants are formed from the factorial-moment continuation and are
identified below with the cumulants of the explicit real-margin masses and of
actual hypergeometric laws.  The rational remainder identities give the fourth-
and third-degree expansions, respectively, including fixed sample sizes zero
and one.
-/

open Filter
open scoped Topology

namespace ExactHoeffding

noncomputable section

/-- The second cumulant of the inverse-population moment continuation. -/
def hypergeomRescaledCumulant2 (m : ℕ) (s e : ℝ) : ℝ :=
  hypergeomRescaledMoment m 2 s e - hypergeomRescaledMoment m 1 s e ^ 2

/-- The third cumulant of the inverse-population moment continuation. -/
def hypergeomRescaledCumulant3 (m : ℕ) (s e : ℝ) : ℝ :=
  hypergeomRescaledMoment m 3 s e -
    3 * hypergeomRescaledMoment m 2 s e * hypergeomRescaledMoment m 1 s e +
    2 * hypergeomRescaledMoment m 1 s e ^ 3

/-- The actual variance, expressed in inverse-population coordinates. -/
theorem hypergeom_rescaled_cumulant2_closed (m : ℕ) (s e : ℝ)
    (h1 : 1 - e ≠ 0) :
    hypergeomRescaledCumulant2 m s e =
      (m : ℝ) / 4 * (1 - s ^ 2 * e ^ 2) * (1 - (m : ℝ) * e) / (1 - e) := by
  unfold hypergeomRescaledCumulant2 hypergeomRescaledMoment
  simp only [momentFromFactorials, hypergeomRescaledFactorial,
    descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  field_simp [h1] <;> ring

/-- The exact cubic cumulant in inverse-population coordinates. -/
theorem hypergeom_rescaled_cumulant3_closed (m : ℕ) (s e : ℝ)
    (h1 : 1 - e ≠ 0) (h2 : 1 - 2 * e ≠ 0) :
    hypergeomRescaledCumulant3 m s e =
      hypergeomRescaledCumulant2 m s e * s * e *
        (1 - 2 * (m : ℝ) * e) / (1 - 2 * e) := by
  unfold hypergeomRescaledCumulant3 hypergeomRescaledCumulant2 hypergeomRescaledMoment
  simp only [momentFromFactorials, hypergeomRescaledFactorial,
    descFactorial_cast_product, Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num
  field_simp [h1, h2] <;> ring

/-- The literal fourth-degree variance polynomial in the appendix. -/
def hypergeomCumulant2Taylor (m : ℕ) (s e : ℝ) : ℝ :=
  (m : ℝ) / 4 * (1 - ((m : ℝ) - 1) * e - ((m : ℝ) + s ^ 2 - 1) * e ^ 2 +
    ((m : ℝ) - 1) * (s ^ 2 - 1) * (e ^ 3 + e ^ 4))

/-- The literal third-degree cubic-cumulant polynomial in the appendix. -/
def hypergeomCumulant3Taylor (m : ℕ) (s e : ℝ) : ℝ :=
  (m : ℝ) * s / 4 * (e - 3 * ((m : ℝ) - 1) * e ^ 2 +
    (2 * (m : ℝ) ^ 2 - 9 * (m : ℝ) - s ^ 2 + 7) * e ^ 3)

/-- The analytic coefficient of the exact fifth-order variance remainder. -/
def hypergeomCumulant2RemainderFactor (m : ℕ) (s e : ℝ) : ℝ :=
  (m : ℝ) * ((m : ℝ) - 1) * (s ^ 2 - 1) / (4 * (1 - e))

/-- The analytic coefficient of the exact fourth-order cubic-cumulant remainder. -/
def hypergeomCumulant3RemainderFactor (m : ℕ) (s e : ℝ) : ℝ :=
  (m : ℝ) * s * ((m : ℝ) - 1) *
    (6 * (m : ℝ) + 3 * s ^ 2 - 15 -
      (2 * (m : ℝ) * s ^ 2 + 4 * (m : ℝ) + 2 * s ^ 2 - 14) * e) /
    (4 * (1 - e) * (1 - 2 * e))

/-- Exact fifth-order remainder identity, without asymptotic notation. -/
theorem hypergeom_rescaled_cumulant2_remainder_identity (m : ℕ) (s e : ℝ)
    (h1 : 1 - e ≠ 0) :
    hypergeomRescaledCumulant2 m s e - hypergeomCumulant2Taylor m s e =
      hypergeomCumulant2RemainderFactor m s e * e ^ 5 := by
  rw [hypergeom_rescaled_cumulant2_closed m s e h1]
  unfold hypergeomCumulant2Taylor hypergeomCumulant2RemainderFactor
  field_simp [h1] <;> ring

/-- Exact fourth-order remainder identity, without asymptotic notation. -/
theorem hypergeom_rescaled_cumulant3_remainder_identity (m : ℕ) (s e : ℝ)
    (h1 : 1 - e ≠ 0) (h2 : 1 - 2 * e ≠ 0) :
    hypergeomRescaledCumulant3 m s e - hypergeomCumulant3Taylor m s e =
      hypergeomCumulant3RemainderFactor m s e * e ^ 4 := by
  rw [hypergeom_rescaled_cumulant3_closed m s e h1 h2,
    hypergeom_rescaled_cumulant2_closed m s e h1]
  unfold hypergeomCumulant3Taylor hypergeomCumulant3RemainderFactor
  have h2' : 1 - e * 2 ≠ 0 := by simpa only [mul_comm] using h2
  field_simp [h1, h2, h2'] <;> ring

/-- The variance remainder factor is analytic at the binomial limit. -/
theorem hypergeom_cumulant2_remainderFactor_analytic (m : ℕ) (s : ℝ) :
    AnalyticAt ℝ (hypergeomCumulant2RemainderFactor m s) 0 := by
  unfold hypergeomCumulant2RemainderFactor
  fun_prop (disch := norm_num)

/-- The cubic-cumulant remainder factor is analytic at the binomial limit. -/
theorem hypergeom_cumulant3_remainderFactor_analytic (m : ℕ) (s : ℝ) :
    AnalyticAt ℝ (hypergeomCumulant3RemainderFactor m s) 0 := by
  unfold hypergeomCumulant3RemainderFactor
  fun_prop (disch := norm_num)

/-- The appendix variance expansion with its fifth-order remainder. -/
theorem hypergeom_rescaled_cumulant2_remainder (m : ℕ) (s : ℝ) :
    (fun e => hypergeomRescaledCumulant2 m s e - hypergeomCumulant2Taylor m s e)
      =O[𝓝 0] (fun e : ℝ => e ^ 5) := by
  have hc := (hypergeom_cumulant2_remainderFactor_analytic m s).continuousAt
  have h := hc.isBigO.mul (Asymptotics.isBigO_refl (fun e : ℝ => e ^ 5) (𝓝 0))
  have h1 : ∀ᶠ e : ℝ in 𝓝 0, 1 - e ≠ 0 :=
    (continuousAt_const.sub continuousAt_id).eventually_ne (by norm_num)
  simp only [one_mul] at h
  refine h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [h1] with e he
  exact (hypergeom_rescaled_cumulant2_remainder_identity m s e he).symm

/-- The appendix cubic-cumulant expansion with its fourth-order remainder. -/
theorem hypergeom_rescaled_cumulant3_remainder (m : ℕ) (s : ℝ) :
    (fun e => hypergeomRescaledCumulant3 m s e - hypergeomCumulant3Taylor m s e)
      =O[𝓝 0] (fun e : ℝ => e ^ 4) := by
  have hc := (hypergeom_cumulant3_remainderFactor_analytic m s).continuousAt
  have h := hc.isBigO.mul (Asymptotics.isBigO_refl (fun e : ℝ => e ^ 4) (𝓝 0))
  have h1 : ∀ᶠ e : ℝ in 𝓝 0, 1 - e ≠ 0 :=
    (continuousAt_const.sub continuousAt_id).eventually_ne (by norm_num)
  have h2 : ∀ᶠ e : ℝ in 𝓝 0, 1 - 2 * e ≠ 0 :=
    (continuousAt_const.sub (continuousAt_id.const_mul 2)).eventually_ne (by norm_num)
  simp only [one_mul] at h
  refine h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [h1, h2] with e he1 he2
  exact (hypergeom_rescaled_cumulant3_remainder_identity m s e he1 he2).symm

/-- Moment continuation agrees with every admissible population, including small sizes. -/
theorem hypergeom_rescaled_moment_actual (N k m r : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N) (hr : r ≤ 6)
    (s : ℝ) (hs : (N : ℝ) - 2 * (k : ℝ) = s) :
    hypergeomRescaledMoment m r s (1 / (N : ℝ)) = hypergeomRawMoment N k m r := by
  unfold hypergeomRescaledMoment
  simp_rw [hypergeom_rescaled_factorial_actual N k m _ hN hk hm s hs]
  exact (hypergeom_raw_moment_factorials_through_six N k m r hr).symm

/-- The rescaled second cumulant is the actual hypergeometric variance. -/
theorem hypergeom_rescaled_cumulant2_actual (N k m : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N)
    (s : ℝ) (hs : (N : ℝ) - 2 * (k : ℝ) = s) :
    hypergeomRescaledCumulant2 m s (1 / (N : ℝ)) = hypergeomCumulant2 N k m := by
  unfold hypergeomRescaledCumulant2 hypergeomCumulant2 finiteCumulant2
  rw [hypergeom_rescaled_moment_actual N k m 2 hN hk hm (by omega) s hs,
    hypergeom_rescaled_moment_actual N k m 1 hN hk hm (by omega) s hs]
  rfl

/-- The rescaled cubic cumulant is the actual third hypergeometric cumulant. -/
theorem hypergeom_rescaled_cumulant3_actual (N k m : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N)
    (s : ℝ) (hs : (N : ℝ) - 2 * (k : ℝ) = s) :
    hypergeomRescaledCumulant3 m s (1 / (N : ℝ)) = hypergeomCumulant3 N k m := by
  unfold hypergeomRescaledCumulant3 hypergeomCumulant3 finiteCumulant3
  rw [hypergeom_rescaled_moment_actual N k m 3 hN hk hm (by omega) s hs,
    hypergeom_rescaled_moment_actual N k m 2 hN hk hm (by omega) s hs,
    hypergeom_rescaled_moment_actual N k m 1 hN hk hm (by omega) s hs]
  rfl

/-- Full fourth-degree variance expansion along actual admissible populations. -/
theorem hypergeom_cumulant2_balanced_expansion
    (Ns ks : ℕ → ℕ) (m : ℕ) (s : ℝ)
    (hN : ∀ n, 0 < Ns n) (hk : ∀ n, ks n ≤ Ns n) (hm : ∀ n, m ≤ Ns n)
    (hs : ∀ n, (Ns n : ℝ) - 2 * (ks n : ℝ) = s)
    (hlim : Tendsto (fun n => (Ns n : ℝ)) atTop atTop) :
    (fun n => hypergeomCumulant2 (Ns n) (ks n) m -
      hypergeomCumulant2Taylor m s (1 / (Ns n : ℝ)))
      =O[atTop] (fun n => (1 / (Ns n : ℝ)) ^ 5) := by
  have h := (hypergeom_rescaled_cumulant2_remainder m s).comp_tendsto
    (hlim.const_div_atTop 1)
  simpa only [Function.comp_def,
    hypergeom_rescaled_cumulant2_actual _ _ _ (hN _) (hk _) (hm _) s (hs _)] using h

/-- Full third-degree cubic-cumulant expansion along actual admissible populations. -/
theorem hypergeom_cumulant3_balanced_expansion
    (Ns ks : ℕ → ℕ) (m : ℕ) (s : ℝ)
    (hN : ∀ n, 0 < Ns n) (hk : ∀ n, ks n ≤ Ns n) (hm : ∀ n, m ≤ Ns n)
    (hs : ∀ n, (Ns n : ℝ) - 2 * (ks n : ℝ) = s)
    (hlim : Tendsto (fun n => (Ns n : ℝ)) atTop atTop) :
    (fun n => hypergeomCumulant3 (Ns n) (ks n) m -
      hypergeomCumulant3Taylor m s (1 / (Ns n : ℝ)))
      =O[atTop] (fun n => (1 / (Ns n : ℝ)) ^ 4) := by
  have h := (hypergeom_rescaled_cumulant3_remainder m s).comp_tendsto
    (hlim.const_div_atTop 1)
  simpa only [Function.comp_def,
    hypergeom_rescaled_cumulant3_actual _ _ _ (hN _) (hk _) (hm _) s (hs _)] using h

end
end ExactHoeffding
