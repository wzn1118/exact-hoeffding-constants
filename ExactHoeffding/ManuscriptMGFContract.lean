import ExactHoeffding.StrictUniformLaplace
import ExactHoeffding.OptimalProxy

namespace ExactHoeffding

/-- Typed statement contract for the frozen manuscript's Corollary
`cor:mgf` and equations `eq:mgf` and `eq:proxy`. The first two clauses are
exactly the displayed uniform log-Laplace and optimal-proxy bounds. The last
two clauses record the strictness and equality-at-zero conclusions proved in
the frozen corollary's proof. -/
theorem manuscript_cor_mgf_contract :
    ∀ N k m : ℕ, 2 ≤ N → 1 ≤ k → k < N → 1 ≤ m → m < N →
      (∀ t : ℝ,
        hypergeomCenteredLogMGF N k m t ≤
          (t^2 / (8 * ((N : ℝ) - 1))) *
            min ((k : ℝ) * ((N : ℝ) - k))
                ((m : ℝ) * ((N : ℝ) - m))) ∧
      hypergeomOptimalProxy N k m ≤
        min ((k : ℝ) * ((N : ℝ) - k))
            ((m : ℝ) * ((N : ℝ) - m)) /
          (4 * ((N : ℝ) - 1)) ∧
      (∀ t : ℝ, t ≠ 0 →
        hypergeomCenteredLogMGF N k m t <
          (t^2 / (8 * ((N : ℝ) - 1))) *
            min ((k : ℝ) * ((N : ℝ) - k))
                ((m : ℝ) * ((N : ℝ) - m))) ∧
      (∀ t : ℝ,
        hypergeomCenteredLogMGF N k m t =
          (t^2 / (8 * ((N : ℝ) - 1))) *
            min ((k : ℝ) * ((N : ℝ) - k))
                ((m : ℝ) * ((N : ℝ) - m)) ↔ t = 0) := by
  intro N k m hN hk0 hkN hm0 hmN
  have hk : k ≤ N := Nat.le_of_lt hkN
  have hm : m ≤ N := Nat.le_of_lt hmN
  have hNcast : (2 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have hNreal : 0 < (N : ℝ) - 1 := by linarith
  have hcoef : sharpCurvatureConstant N k m =
      min ((k : ℝ) * ((N : ℝ) - k))
          ((m : ℝ) * ((N : ℝ) - m)) /
        (4 * ((N : ℝ) - 1)) := rfl
  have hrhs (t : ℝ) :
      sharpCurvatureConstant N k m * t^2 / 2 =
        (t^2 / (8 * ((N : ℝ) - 1))) *
          min ((k : ℝ) * ((N : ℝ) - k))
              ((m : ℝ) * ((N : ℝ) - m)) := by
    rw [hcoef]
    field_simp [ne_of_gt hNreal]
    <;> ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    calc
      hypergeomCenteredLogMGF N k m t ≤
          sharpCurvatureConstant N k m * t^2 / 2 := by
            exact hypergeom_uniform_log_laplace_domination N k m hk hm t
      _ = _ := hrhs t
  · simpa [sharpCurvatureConstant] using
      hypergeomOptimalProxy_le_curvature N k m hk hm
  · intro t ht
    calc
      hypergeomCenteredLogMGF N k m t <
          sharpCurvatureConstant N k m * t^2 / 2 := by
            exact hypergeom_uniform_log_laplace_domination_strict N k m
              (by omega) hkN (by omega) hmN t ht
      _ = _ := hrhs t
  · intro t
    constructor
    · intro heq
      by_contra ht
      have hlt := hypergeom_uniform_log_laplace_domination_strict N k m
        (by omega) hkN (by omega) hmN t ht
      rw [hrhs t] at hlt
      exact (ne_of_lt hlt) heq
    · rintro rfl
      simp [hypergeomCenteredLogMGF_zero N k m hk hm]

end ExactHoeffding
