import ExactHoeffding.Laplace
import ExactHoeffding.Normalization

/-!
# The exact nonzero-tilt lower-bound certificate

This file formalizes the equality computation for the nearest-balanced
single-coordinate contrast in the odd-population case. It proves the
finite Bernoulli identity at the nonzero log-odds parameter. The global
upper bound and the classification of all extremizers are separate
claims that are not assumed here.
-/

namespace ExactHoeffding

/-- At twice the log-odds tilt, the *centered* Bernoulli log-MGF has
an exact equality, for every nondegenerate success probability. -/
theorem bernoulli_centered_log_odds_equality (p : ℝ)
    (hp : 0 < p) (hq : p < 1) :
    Real.log (bernoulliMGF p (2 * Real.log ((1 - p) / p))) -
        2 * p * Real.log ((1 - p) / p) =
      (1 - 2 * p) * Real.log ((1 - p) / p) := by
  rw [bernoulli_log_odds_balance p hp hq]
  ring

/-- At the nearest-balanced success probability, the centered
Bernoulli log-MGF has exactly the value required for the sharp
one-coordinate lower-bound example, without asymptotics. -/
theorem singleton_odd_log_mgf_certificate (N : ℝ) (hN : 1 < N) :
    let p := (N - 1) / (2 * N)
    let α := Real.log ((N + 1) / (N - 1))
    Real.log (bernoulliMGF p (2 * α)) - 2 * p * α = α / N := by
  dsimp
  have hNpos : (0 : ℝ) < N := by linarith
  have hN0 : N ≠ 0 := ne_of_gt hNpos
  have hN1 : N - 1 ≠ 0 := by linarith
  have hp : 0 < (N - 1) / (2 * N) :=
    div_pos (by linarith) (by linarith)
  have hq : (N - 1) / (2 * N) < 1 := by
    apply (div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * N)).2
    linarith
  have hodds :
      (1 - (N - 1) / (2 * N)) / ((N - 1) / (2 * N)) =
        (N + 1) / (N - 1) := by
    field_simp [hN0, hN1] <;> ring
  have hc := bernoulli_centered_log_odds_equality
    ((N - 1) / (2 * N)) hp hq
  rw [hodds] at hc
  calc
    Real.log (bernoulliMGF ((N - 1) / (2 * N))
          (2 * Real.log ((N + 1) / (N - 1)))) -
        2 * ((N - 1) / (2 * N)) * Real.log ((N + 1) / (N - 1)) =
      (1 - 2 * ((N - 1) / (2 * N))) *
        Real.log ((N + 1) / (N - 1)) := hc
    _ = Real.log ((N + 1) / (N - 1)) / N := by
      field_simp [hN0] <;> ring

/-- The explicit coefficient and zero-sum contrast norm from the
manuscript match the exact one-coordinate log-MGF. This certifies the
nonzero-tilt equality candidate (the lower bound), not global optimality. -/
theorem singleton_odd_quadratic_saturation (N : ℝ) (hN : 1 < N) :
    let p := (N - 1) / (2 * N)
    let α := Real.log ((N + 1) / (N - 1))
    let C := 2 / ((N - 1) * α)
    Real.log (bernoulliMGF p (2 * α)) - 2 * p * α =
      C * ((N - 1) / N) * α ^ 2 / 2 := by
  dsimp
  rw [singleton_odd_log_mgf_certificate N hN]
  have hN0 : N ≠ 0 := by linarith
  have hN1 : N - 1 ≠ 0 := by linarith
  have hfrac : (1 : ℝ) < (N + 1) / (N - 1) := by
    apply (one_lt_div (by linarith : (0 : ℝ) < N - 1)).2
    linarith
  have hlog : Real.log ((N + 1) / (N - 1)) ≠ 0 :=
    ne_of_gt (Real.log_pos hfrac)
  field_simp [hN0, hN1, hlog] <;> ring

end ExactHoeffding
