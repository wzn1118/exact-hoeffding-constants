import ExactHoeffding.FiniteSupportRecurrenceBridge
import ExactHoeffding.FiniteSupportLegendreCalculus
import ExactHoeffding.HypergeometricBarrier

namespace ExactHoeffding
noncomputable section

/-- The canonical finite hypergeometric law as a positive recurrence law. -/
noncomputable def meanCurveHypergeomLaw
    (k m r : ℕ) (hmk : m ≤ k) : RealRecurrenceLaw where
  degree := m
  marks := (k : ℝ)
  remainder := (r : ℝ)
  mass := hypergeomMass (k + m + r) k m
  marks_ge := by exact_mod_cast hmk
  remainder_nonneg := Nat.cast_nonneg r
  mass_pos := by
    intro i hi
    exact hypergeomMass_pos_canonical k m r i hmk hi
  mass_total := hypergeomMass_total (k + m + r) k m (by omega) (by omega)
  adjacent := by
    intro i hi
    exact hypergeomMass_adjacent_real k m r i hmk hi

noncomputable def meanCurveHypergeomTiltAtMean
    (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m) (u : ℝ) : ℝ :=
  finiteSupportMeanInverse
    ((meanCurveHypergeomLaw k m r hmk).toFiniteSupportTiltCurve
      (by exact_mod_cast hm)) u

noncomputable def meanCurveHypergeomVarianceAtMean
    (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m) (u : ℝ) : ℝ :=
  (meanCurveHypergeomLaw k m r hmk).variance
    (meanCurveHypergeomTiltAtMean k m r hmk hm u)

@[simp] theorem meanCurveHypergeomTiltAtMean_spec
    (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m) {u : ℝ}
    (hu0 : 0 < u) (hum : u < (m : ℝ)) :
    hypergeomTiltMean (k + m + r) k m
      (meanCurveHypergeomTiltAtMean k m r hmk hm u) = u := by
  change (meanCurveHypergeomLaw k m r hmk).mean
    (meanCurveHypergeomTiltAtMean k m r hmk hm u) = u
  exact finiteSupportMeanInverse_spec
    ((meanCurveHypergeomLaw k m r hmk).toFiniteSupportTiltCurve
      (by exact_mod_cast hm)) hu0 hum

/-- The ODE in `odd:lem:ode`, expressed in the actual mean coordinate of the
finite hypergeometric law. The derivative is taken with respect to the mean
u, and the variance is evaluated at the unique tilt realizing that mean. -/
theorem manuscript_odd_lem_ode_mean_contract
    (k m r : ℕ) (hmk : m ≤ k) (hm : 0 < m) {u : ℝ}
    (hu0 : 0 < u) (hum : u < (m : ℝ)) :
    riccatiF ((k + m + r : ℕ) : ℝ) (k : ℝ) (m : ℝ) u
        (meanCurveHypergeomVarianceAtMean k m r hmk hm u) +
      ((k + m + r : ℕ) : ℝ) *
        (u - (m : ℝ) * (k : ℝ) / ((k + m + r : ℕ) : ℝ)) *
        meanCurveHypergeomVarianceAtMean k m r hmk hm u *
        deriv (fun x : ℝ => meanCurveHypergeomVarianceAtMean k m r hmk hm x) u = 0 := by
  let L := meanCurveHypergeomLaw k m r hmk
  let D := L.toFiniteSupportTiltCurve (by exact_mod_cast hm)
  let t := meanCurveHypergeomTiltAtMean k m r hmk hm u
  let V : ℝ → ℝ := fun x => meanCurveHypergeomVarianceAtMean k m r hmk hm x
  let v := hypergeomTiltVariance (k + m + r) k m t
  let w := deriv (hypergeomTiltVariance (k + m + r) k m) t
  have hmean : hypergeomTiltMean (k + m + r) k m t = u := by
    exact meanCurveHypergeomTiltAtMean_spec k m r hmk hm hu0 hum
  have hV : V u = v := by
    rfl
  have hvpos : 0 < v := by
    have h := L.variance_pos hm t
    simpa [v, L, meanCurveHypergeomLaw, RealRecurrenceLaw.variance,
      RealRecurrenceLaw.mean, RealRecurrenceLaw.mgf, hypergeomTiltVariance,
      hypergeomTiltMean, hypergeomMGF, finiteMGF] using h
  have htiltDeriv : HasDerivAt (hypergeomTiltVariance (k + m + r) k m) w t := by
    have h := (hypergeomTiltVariance_differentiableAt (k + m + r) k m
      (by omega) (by omega) t).hasDerivAt
    simpa [w] using h
  have hinvDeriv := finiteSupportMeanInverse_hasDerivAt D hu0 hum
  have hcompose := htiltDeriv.comp u hinvDeriv
  have hDvar : D.variance (finiteSupportMeanInverse D u) = v := by
    rfl
  have hcompose' : HasDerivAt
      (hypergeomTiltVariance (k + m + r) k m ∘ finiteSupportMeanInverse D)
      (w * v⁻¹) u := by
    simpa only [hDvar] using hcompose
  have hmeanCurve : HasDerivAt V (w * v⁻¹) u := by
    change HasDerivAt
      (hypergeomTiltVariance (k + m + r) k m ∘ finiteSupportMeanInverse D)
      (w * v⁻¹) u
    exact hcompose'
  have hchain : v * deriv V u = w := by
    calc
      v * deriv V u = v * (w * v⁻¹) := by rw [hmeanCurve.deriv]
      _ = w := by field_simp [ne_of_gt hvpos]
  have hcurve0 := hypergeomTiltVariance_curve_identity k m r hmk t
  dsimp only at hcurve0
  rw [hmean] at hcurve0
  let A := u * (u + (r : ℝ))
  let C := ((k : ℝ) - u) * ((m : ℝ) - u)
  have hcurveRhs :
      (C - A) * w =
        -(((k + m + r : ℕ) : ℝ) - 1) * v ^ 2 +
          (A + C - (2 * u + (r : ℝ)) * C +
            (2 * u - (k : ℝ) - (m : ℝ)) * A) * v + A * C := by
    simpa [A, C, v, w] using hcurve0
  have hNr :
      ((k + m + r : ℕ) : ℝ) - (k : ℝ) - (m : ℝ) = (r : ℝ) := by
    push_cast
    ring
  have hF :
      -(((k + m + r : ℕ) : ℝ) - 1) * v ^ 2 +
          (A + C - (2 * u + (r : ℝ)) * C +
            (2 * u - (k : ℝ) - (m : ℝ)) * A) * v + A * C =
        riccatiF ((k + m + r : ℕ) : ℝ) (k : ℝ) (m : ℝ) u v := by
    unfold riccatiF riccatiA riccatiC
    dsimp [A, C]
    push_cast
    ring
  have hcurve :
      (((k : ℝ) - u) * ((m : ℝ) - u) - u * (u + (r : ℝ))) * w =
        riccatiF ((k + m + r : ℕ) : ℝ) (k : ℝ) (m : ℝ) u v := by
    change (C - A) * w = _
    exact hcurveRhs.trans hF
  have hN : ((k + m + r : ℕ) : ℝ) ≠ 0 := by positivity
  have hca :
      ((k : ℝ) - u) * ((m : ℝ) - u) - u * (u + (r : ℝ)) =
        -(((k + m + r : ℕ) : ℝ) * u - (m : ℝ) * (k : ℝ)) := by
    push_cast
    ring
  have hmu :
      ((k + m + r : ℕ) : ℝ) *
          (u - (m : ℝ) * (k : ℝ) / ((k + m + r : ℕ) : ℝ)) =
        ((k + m + r : ℕ) : ℝ) * u - (m : ℝ) * (k : ℝ) := by
    field_simp [hN]
  have hcenter :
      riccatiF ((k + m + r : ℕ) : ℝ) (k : ℝ) (m : ℝ) u v +
        ((k + m + r : ℕ) : ℝ) *
          (u - (m : ℝ) * (k : ℝ) / ((k + m + r : ℕ) : ℝ)) * w = 0 := by
    rw [← hcurve, hca, hmu]
    ring
  change riccatiF ((k + m + r : ℕ) : ℝ) (k : ℝ) (m : ℝ) u (V u) +
      ((k + m + r : ℕ) : ℝ) *
        (u - (m : ℝ) * (k : ℝ) / ((k + m + r : ℕ) : ℝ)) *
        V u * deriv V u = 0
  rw [hV]
  calc
    riccatiF ((k + m + r : ℕ) : ℝ) (k : ℝ) (m : ℝ) u v +
        ((k + m + r : ℕ) : ℝ) *
          (u - (m : ℝ) * (k : ℝ) / ((k + m + r : ℕ) : ℝ)) * v * deriv V u =
      riccatiF ((k + m + r : ℕ) : ℝ) (k : ℝ) (m : ℝ) u v +
        ((k + m + r : ℕ) : ℝ) *
          (u - (m : ℝ) * (k : ℝ) / ((k + m + r : ℕ) : ℝ)) *
          (v * deriv V u) := by ring
    _ = 0 := by rw [hchain]; exact hcenter

/-- The mean-coordinate form of `odd:lem:barrier`: the actual tilted
hypergeometric variance is bounded by the paper's quadratic barrier, and
contact occurs exactly at the ordinary mean. -/
theorem manuscript_odd_lem_barrier_mean_contract
    (k m r : ℕ) (hm : 3 ≤ m) (hmk : m ≤ k)
    (hk : k ≤ m + r) (hgap : m < k + r) {u : ℝ}
    (hu0 : 0 < u) (hum : u < (m : ℝ)) :
    let N : ℝ := (k : ℝ) + (m : ℝ) + (r : ℝ)
    let d : ℝ := 1 - 2 * (k : ℝ) / N
    let μ : ℝ := (m : ℝ) * (k : ℝ) / N
    meanCurveHypergeomVarianceAtMean k m r hmk (by omega) u ≤
        varianceBarrier N (m : ℝ) d (u - μ) ∧
      (meanCurveHypergeomVarianceAtMean k m r hmk (by omega) u =
          varianceBarrier N (m : ℝ) d (u - μ) ↔ u = μ) := by
  let hmpos : 0 < m := by omega
  let L := meanCurveHypergeomLaw k m r hmk
  let D := L.toFiniteSupportTiltCurve (by exact_mod_cast hmpos)
  let t := meanCurveHypergeomTiltAtMean k m r hmk hmpos u
  let N : ℝ := (k : ℝ) + (m : ℝ) + (r : ℝ)
  let d : ℝ := 1 - 2 * (k : ℝ) / N
  let μ : ℝ := (m : ℝ) * (k : ℝ) / N
  have hmean : hypergeomTiltMean (k + m + r) k m t = u :=
    meanCurveHypergeomTiltAtMean_spec k m r hmk hmpos hu0 hum
  have hbar := hypergeomTiltVariance_barrier_canonical k m r hm hmk hk hgap
  dsimp only at hbar
  have hzero : hypergeomTiltMean (k + m + r) k m 0 = μ := by
    rw [hypergeomTiltMean_zero (k + m + r) k m (by omega) (by omega)]
    dsimp [μ, N]
    push_cast
    ring
  have htZeroIff : t = 0 ↔ u = μ := by
    constructor
    · intro ht
      rw [ht] at hmean
      rw [hzero] at hmean
      exact hmean.symm
    · intro hu
      have hmean0 : D.mean 0 = u := by
        change hypergeomTiltMean (k + m + r) k m 0 = u
        rw [hzero]
        exact hu.symm
      have hinv : 0 = finiteSupportMeanInverse D u :=
        (finiteSupportMeanInverse_unique D
          (by change 0 < u; exact hu0)
          (by change u < (m : ℝ); exact hum)).mp hmean0
      change finiteSupportMeanInverse D u = 0
      exact hinv.symm
  have hbound :
      meanCurveHypergeomVarianceAtMean k m r hmk hmpos u ≤
        varianceBarrier N (m : ℝ) d (u - μ) := by
    change hypergeomTiltVariance (k + m + r) k m t ≤ _
    have h := hbar.1 t
    rw [hmean] at h
    simpa [N, d, μ] using h
  have heqIff :
      meanCurveHypergeomVarianceAtMean k m r hmk hmpos u =
          varianceBarrier N (m : ℝ) d (u - μ) ↔ t = 0 := by
    change hypergeomTiltVariance (k + m + r) k m t = _ ↔ t = 0
    have h := hbar.2 t
    rw [hmean] at h
    simpa [N, d, μ] using h
  refine ⟨hbound, ?_⟩
  rw [heqIff, htZeroIff]

end
end ExactHoeffding
