import ExactHoeffding.RealMarginMasses
import ExactHoeffding.RealRecurrenceCurvature

/-! # The real-margin probability law satisfies the sharp-curvature recurrence -/

namespace ExactHoeffding

noncomputable section

/-- Explicit real-population normal-form probability law. -/
def realMarginRecurrenceLaw (m : ℕ) (N k : ℝ) (hN : 0 < N)
    (hk : (m:ℝ) ≤ k) (hq : k+(m:ℝ) ≤ N) : RealRecurrenceLaw where
  degree := m
  marks := k
  remainder := N-k-m
  mass := realMarginMass m (1/N) (k/N)
  marks_ge := hk
  remainder_nonneg := by linarith
  mass_pos := by
    have hfac : ∀ j : ℕ, j < m → (j:ℝ) < m := by
      intro j hj; exact_mod_cast hj
    have hp : ∀ j : ℕ, j < m → 0 < k/N-(j:ℝ)*(1/N) := by
      intro j hj
      rw [show k/N-(j:ℝ)*(1/N) = (k-j)/N by ring]
      exact div_pos (by linarith [hfac j hj]) hN
    have hq' : ∀ j : ℕ, j < m → 0 < 1-k/N-(j:ℝ)*(1/N) := by
      intro j hj
      rw [show 1-k/N-(j:ℝ)*(1/N) = (N-k-j)/N by field_simp]
      exact div_pos (by linarith [hfac j hj]) hN
    have hden : 0 < scaledFalling 1 (1/N) m := by
      apply scaledFalling_pos
      intro j hj
      rw [show 1-(j:ℝ)*(1/N) = (N-j)/N by field_simp]
      exact div_pos (by have := hfac j hj; have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith) hN
    intro i hi
    exact realMarginMass_pos m _ _ hp hq' hden i hi
  mass_total := by
    apply realMarginMass_sum
    apply ne_of_gt
    apply scaledFalling_pos
    intro j hj
    have hjr : (j:ℝ) < m := by exact_mod_cast hj
    rw [show 1-(j:ℝ)*(1/N) = (N-j)/N by field_simp]
    exact div_pos (by have := (Nat.cast_nonneg m : (0:ℝ) ≤ m); linarith) hN
  adjacent := by
    intro i hi
    exact realMarginMass_population_adjacent m i N k hN.ne' hi

/-- The general real-recurrence theorem applies to the explicit positive
real-margin masses, rather than an assumed optimizer or assumed law. -/
theorem realMargin_curvature_ge_three (m : ℕ) (N k t : ℝ)
    (hm : 3 ≤ m) (hN : 0 < N) (hk : (m:ℝ) ≤ k) (hq : k+(m:ℝ) ≤ N) :
    deriv (deriv (fun u => Real.log (finiteMGF (Finset.range (m+1))
      (realMarginMass m (1/N) (k/N)) (fun i => (i:ℝ)) u))) t ≤
      (m:ℝ)*(N-m)/(4*(N-1)) := by
  let L := realMarginRecurrenceLaw m N k hN hk hq
  have hw : ∀ i ∈ Finset.range (m+1), 0 ≤ realMarginMass m (1/N) (k/N) i := by
    intro i hi
    exact (L.mass_pos i (show i ≤ m from Nat.le_of_lt_succ (Finset.mem_range.mp hi))).le
  rw [finiteLogMGF_second_deriv _ _ _ hw L.mass_total t]
  have hb := L.variance_sharp hm t
  have hg := L.mgf_pos t
  have hform :
      (finiteTiltSecond (Finset.range (m+1)) (realMarginMass m (1/N) (k/N))
        (fun i => (i:ℝ)) t * finiteMGF (Finset.range (m+1))
        (realMarginMass m (1/N) (k/N)) (fun i => (i:ℝ)) t -
        finiteTiltFirst (Finset.range (m+1)) (realMarginMass m (1/N) (k/N))
        (fun i => (i:ℝ)) t * finiteTiltFirst (Finset.range (m+1))
        (realMarginMass m (1/N) (k/N)) (fun i => (i:ℝ)) t) /
        finiteMGF (Finset.range (m+1)) (realMarginMass m (1/N) (k/N))
        (fun i => (i:ℝ)) t ^ 2 = L.variance t := by
    change (finiteTiltSecond (Finset.range (m+1)) L.mass (fun i => (i:ℝ)) t * L.mgf t -
      finiteTiltFirst (Finset.range (m+1)) L.mass (fun i => (i:ℝ)) t *
      finiteTiltFirst (Finset.range (m+1)) L.mass (fun i => (i:ℝ)) t) / L.mgf t ^ 2 =
      finiteTiltSecond (Finset.range (m+1)) L.mass (fun i => (i:ℝ)) t / L.mgf t -
      (finiteTiltFirst (Finset.range (m+1)) L.mass (fun i => (i:ℝ)) t / L.mgf t)^2
    field_simp
  rw [hform]
  convert hb using 1
  dsimp [L, realMarginRecurrenceLaw]
  ring

end
end ExactHoeffding
