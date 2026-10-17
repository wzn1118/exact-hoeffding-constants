import ExactHoeffding.FixedSampleExtrema
import ExactHoeffding.TwoDrawSingletonComparison
import ExactHoeffding.OptimalProxyAsymptotics

namespace ExactHoeffding
noncomputable section
open Filter Asymptotics
open scoped Topology

theorem hypergeomCenteredLogMGF_zero_marks_all_tilts (N m : ℕ)
    (hm : m ≤ N) (t : ℝ) :
    hypergeomCenteredLogMGF N 0 m t = 0 := by
  have hmgf : hypergeomMGF N 0 m t = 1 := by
    unfold hypergeomMGF finiteMGF
    rw [Finset.sum_eq_single 0]
    · simp [hypergeomMass_zero_marks N m 0 hm (by omega)]
    · intro i hi hne
      have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [hypergeomMass_zero_marks N m i hm him]
      simp [hne]
    · simp
  unfold hypergeomCenteredLogMGF
  rw [hmgf]
  simp

theorem hypergeomOptimalProxy_zero_marks_all_tilts (N m : ℕ)
    (hm : m ≤ N) : hypergeomOptimalProxy N 0 m = 0 := by
  apply optimalProxy_eq_of_optimal _
    (hypergeomCenteredLogMGF_zero_marks_all_tilts N m hm 0) 0
  constructor
  · intro t
    rw [hypergeomCenteredLogMGF_zero_marks_all_tilts N m hm t]
    simp
  · intro D hD
    have h := hD 1
    rw [hypergeomCenteredLogMGF_zero_marks_all_tilts N m hm 1] at h
    norm_num at h
    linarith


/-- The complete `prop:odd2` statement for every odd population `N=2n+1≥5`.
The admissible range includes both Bernoulli endpoint success counts.  The
closed constants are written in `N` notation as `L_N^(2)` and `L_N`. -/
def manuscriptPropOdd2FiniteStatement (n : ℕ) : Prop :=
    let N : ℕ := 2 * n + 1
    let L2 : ℝ :=
      4 / (((N : ℝ) - 2) * Real.log (((N : ℝ) + 1) / ((N : ℝ) - 3)))
    let L1 : ℝ :=
      2 / (((N : ℝ) - 1) * Real.log (((N : ℝ) + 1) / ((N : ℝ) - 1)))
    (∀ k : ℕ, k ≤ N →
      normalizedHypergeomProxy N k 2 ≤ L2) ∧
    (∀ k : ℕ, k ≤ N →
      (normalizedHypergeomProxy N k 2 = L2 ↔ k = n ∨ k = n + 1)) ∧
    normalizedHypergeomProxy N n 2 = L2 ∧
    L2 < L1 ∧
    normalizedHypergeomProxy N 1 2 < L2 ∧
    normalizedHypergeomProxy N (2 * n) 2 < L2

theorem manuscript_prop_odd2_contract (n : ℕ) (hn : 2 ≤ n) :
    manuscriptPropOdd2FiniteStatement n := by
  dsimp [manuscriptPropOdd2FiniteStatement]
  let NR : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  let L2n : ℝ := 4 / ((NR - 2) * Real.log ((NR + 1) / (NR - 3)))
  let L1n : ℝ := 2 / ((NR - 1) * Real.log ((NR + 1) / (NR - 1)))
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNR : NR = 2 * (n : ℝ) + 1 := by
    dsimp [NR]
    push_cast
    ring
  have hN2 : NR - 2 = 2 * (n : ℝ) - 1 := by rw [hNR]; ring
  have hN3 : NR - 3 = 2 * ((n : ℝ) - 1) := by rw [hNR]; ring
  have hN1 : NR - 1 = 2 * (n : ℝ) := by rw [hNR]; ring
  have hnminus : (n : ℝ) - 1 ≠ 0 := by linarith
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hratio2 : (NR + 1) / (NR - 3) = ((n : ℝ) + 1) / ((n : ℝ) - 1) := by
    rw [hN3, hNR]
    field_simp [hnminus]
    ring
  have hratio1 : (NR + 1) / (NR - 1) = ((n : ℝ) + 1) / (n : ℝ) := by
    rw [hN1, hNR]
    field_simp [hn0]
    ring
  have hL2 : oddTwoDrawConstant n = L2n := by
    unfold oddTwoDrawConstant
    change 4 / ((2 * (n : ℝ) - 1) *
      Real.log (((n : ℝ) + 1) / ((n : ℝ) - 1))) =
      4 / ((NR - 2) * Real.log ((NR + 1) / (NR - 3)) )
    rw [hN2, ← hratio2]
  have hL2pos : 0 < L2n := by
    rw [← hL2]
    exact lt_trans (by norm_num) (one_lt_oddTwoDrawConstant n hn)
  have hL1 : oddSingletonConstant n = L1n := by
    unfold oddSingletonConstant
    change 1 / ((n : ℝ) * Real.log (((n : ℝ) + 1) / (n : ℝ))) =
      2 / ((NR - 1) * Real.log ((NR + 1) / (NR - 1)))
    rw [hratio1, hN1]
    have hlog : Real.log (((n : ℝ) + 1) / (n : ℝ)) ≠ 0 := by
      apply ne_of_gt
      apply Real.log_pos
      apply (one_lt_div (show (0 : ℝ) < n by linarith)).2
      linarith
    field_simp [hn0, hlog]
  have hzero : normalizedHypergeomProxy (2*n+1) 0 2 = 0 := by
    unfold normalizedHypergeomProxy
    have hproxy : hypergeomOptimalProxy (2*n+1) 0 2 = 0 := by
      apply optimalProxy_eq_of_optimal _
        (hypergeomCenteredLogMGF_zero_marks_all_tilts (2*n+1) 2 (by omega) 0) 0
      constructor
      · intro t
        rw [hypergeomCenteredLogMGF_zero_marks_all_tilts (2*n+1) 2 (by omega) t]
        simp
      · intro D hD
        have h := hD 1
        rw [hypergeomCenteredLogMGF_zero_marks_all_tilts (2*n+1) 2 (by omega) 1] at h
        norm_num at h
        linarith
    rw [hproxy]
    ring
  have hfull : normalizedHypergeomProxy (2*n+1) (2*n+1) 2 = 0 := by
    unfold normalizedHypergeomProxy
    rw [hypergeomOptimalProxy_success_complement (2*n+1) (2*n+1) 2
      (by omega) (by omega) (by omega)]
    simp only [Nat.sub_self]
    rw [hypergeomOptimalProxy_zero_marks_all_tilts (2*n+1) 2 (by omega)]
    ring
  have hmax (k : ℕ) (hk : k ≤ 2*n+1) :
      normalizedHypergeomProxy (2*n+1) k 2 ≤ oddTwoDrawConstant n := by
    by_cases hk0 : k = 0
    · subst k
      rw [hzero]
      exact le_trans (by norm_num) (le_of_lt (one_lt_oddTwoDrawConstant n hn))
    · by_cases hkN : k = 2*n+1
      · subst k
        rw [hfull]
        exact le_trans (by norm_num) (le_of_lt (one_lt_oddTwoDrawConstant n hn))
      · have hkpos : 1 ≤ k := by omega
        have hkn : k ≤ 2*n := by omega
        exact odd_normalized_proxy_two_draw_le_constant n k hn hkpos hkn
  have heq (k : ℕ) (hk : k ≤ 2*n+1) :
      (normalizedHypergeomProxy (2*n+1) k 2 = oddTwoDrawConstant n ↔
        k = n ∨ k = n + 1) := by
    by_cases hk0 : k = 0
    · subst k
      rw [hzero]
      constructor
      · intro he
        have hp := one_lt_oddTwoDrawConstant n hn
        linarith
      · intro hc
        omega
    · by_cases hkN : k = 2*n+1
      · subst k
        rw [hfull]
        constructor
        · intro he
          have hp := one_lt_oddTwoDrawConstant n hn
          linarith
        · intro hc
          omega
      · exact odd_normalized_proxy_two_draw_eq_constant_iff n k hn (by omega) (by omega)
  have hcenter :
      normalizedHypergeomProxy (2 * n + 1) n 2 = oddTwoDrawConstant n :=
    odd_normalized_proxy_two_draw_value n hn
  have hstrict : oddTwoDrawConstant n < oddSingletonConstant n :=
    oddTwoDrawConstant_lt_singleton n hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hkN
    have h := hmax k hkN
    change normalizedHypergeomProxy (2 * n + 1) k 2 ≤ L2n
    exact h.trans_eq hL2
  · intro k hkN
    change (normalizedHypergeomProxy (2 * n + 1) k 2 = L2n ↔
      k = n ∨ k = n + 1)
    rw [← hL2]
    exact heq k hkN
  · change normalizedHypergeomProxy (2 * n + 1) n 2 = L2n
    exact hcenter.trans hL2
  · change L2n < L1n
    rw [← hL2, ← hL1]
    exact hstrict
  · change normalizedHypergeomProxy (2 * n + 1) 1 2 < L2n
    have h := hmax 1 (by omega)
    have hne : ¬ (1 = n ∨ 1 = n + 1) := by omega
    have hneq : normalizedHypergeomProxy (2 * n + 1) 1 2 ≠ oddTwoDrawConstant n := by
      intro he
      exact hne ((heq 1 (by omega)).mp he)
    have hlt : normalizedHypergeomProxy (2 * n + 1) 1 2 < oddTwoDrawConstant n :=
      lt_of_le_of_ne h hneq
    exact hlt.trans_eq hL2
  · change normalizedHypergeomProxy (2 * n + 1) (2 * n) 2 < L2n
    have h := hmax (2 * n) (by omega)
    have hne : ¬ (2 * n = n ∨ 2 * n = n + 1) := by omega
    have hneq : normalizedHypergeomProxy (2 * n + 1) (2 * n) 2 ≠ oddTwoDrawConstant n := by
      intro he
      exact hne ((heq (2 * n) (by omega)).mp he)
    have hlt : normalizedHypergeomProxy (2 * n + 1) (2 * n) 2 < oddTwoDrawConstant n :=
      lt_of_le_of_ne h hneq
    exact hlt.trans_eq hL2


/-- The odd singleton closed form is the parity constant at population `2*n+1`. -/
theorem oddSingletonConstant_eq_oddHypergeomConstant (n : ℕ) (hn : 2 ≤ n) :
    oddSingletonConstant n = oddHypergeomConstant (2*n+1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < (2*n+1:ℕ) := by positivity
  have hden : 0 < ((2*n+1:ℕ):ℝ) := by positivity
  have harg : (1 / ((2*n+1:ℕ):ℝ)) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · have hpos : 0 < 1 / ((2*n+1:ℕ):ℝ) := div_pos (by norm_num) hden
      linarith
    · apply (div_le_one hden).2
      push_cast
      linarith
  have hratio :
      (1 + 1 / ((2*n+1:ℕ):ℝ)) / (1 - 1 / ((2*n+1:ℕ):ℝ)) =
        ((n:ℝ)+1)/(n:ℝ) := by
    push_cast
    have hn0 : (n:ℝ) ≠ 0 := by linarith
    field_simp [hn0]
    <;> ring
  rw [oddHypergeomConstant_eq_artanh (2*n+1) (by omega),
    Real.artanh_eq_half_log harg, hratio]
  unfold oddSingletonConstant
  push_cast
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  field_simp [hn0]
  <;> ring

/-- The asymptotic statement following `prop:odd2`, with its exact odd-
population sequence and the paper's coefficient and remainder order. -/
def manuscriptPropOdd2GapStatement : Prop :=
    (fun n : ℕ =>
      oddSingletonConstant (n+2) - oddTwoDrawConstant (n+2) -
        (2/3:ℝ) * (1 / (((2*(n+2)+1:ℕ):ℝ)))^3)
      =O[atTop] (fun n : ℕ => (1 / (((2*(n+2)+1:ℕ):ℝ)))^4)

theorem manuscript_prop_odd2_gap_asymptotic_contract :
    manuscriptPropOdd2GapStatement := by
  let N : ℕ → ℕ := fun n => 2*(n+2)+1
  let J : ℕ → ℕ := fun n => n+2
  have hN : Tendsto N atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    dsimp [N]
    omega
  have hodd : ∀ᶠ n in atTop, N n = 2*J n+1 :=
    Filter.Eventually.of_forall fun _ => by simp [N, J]
  have h := odd_nearly_balanced_gap_cubic_expansion_along 2 (by omega) N J hN hodd
  dsimp [N, J] at h
  apply h.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop (0:ℕ)] with n _
  have hn : 2 ≤ n+2 := by omega
  have hsingle := oddSingletonConstant_eq_oddHypergeomConstant (n+2) hn
  have htwo := odd_normalized_proxy_two_draw_value (n+2) hn
  rw [← hsingle, ← htwo]
  ring

/-- Complete `prop:odd2` package: the exact two-draw maximum/equality result
and the stated odd-population asymptotic comparison. -/
theorem manuscript_prop_odd2_full_contract (n : ℕ) (hn : 2 ≤ n) :
    manuscriptPropOdd2FiniteStatement n ∧ manuscriptPropOdd2GapStatement :=
  ⟨manuscript_prop_odd2_contract n hn, manuscript_prop_odd2_gap_asymptotic_contract⟩


end
end ExactHoeffding
