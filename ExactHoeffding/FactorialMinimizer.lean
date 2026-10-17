import ExactHoeffding.FactorialChernoffExact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The minimizing factorial-moment index

For an upper threshold `d` strictly above the hypergeometric mean, the
successive factorial candidates decrease up to the ceiling index displayed
in Proposition `A:factorial`.  This file formalizes the exact candidate ratio,
the admissibility of the ceiling index, and the resulting optimized candidate
bound. -/

namespace ExactHoeffding
noncomputable section

/-- The falling-factorial closed form of a hypergeometric candidate. -/
def hypergeomFactorialValue (N k m d j : ℕ) : ℝ :=
  ((Nat.descFactorial k j : ℝ) * (Nat.descFactorial m j : ℝ)) /
    ((Nat.descFactorial N j : ℝ) * (Nat.descFactorial d j : ℝ))

/-- The ceiling index from the factorial-moment ratio test. -/
def hypergeomFactorialIndex (N k m d : ℕ) : ℕ :=
  ⌈((N : ℝ) * d - (k : ℝ) * m) /
    ((N : ℝ) + d - k - m)⌉₊

private theorem hypergeomFactorialValue_pos (N k m d j : ℕ)
    (hjd : j ≤ d) (hdm : d ≤ m) (hdk : d ≤ k) (hmkN : k + m ≤ N) :
    0 < hypergeomFactorialValue N k m d j := by
  have hjk : j ≤ k := hjd.trans hdk
  have hjm : j ≤ m := hjd.trans hdm
  have hjN : j ≤ N := hjm.trans (by omega)
  have hN : 0 < (Nat.descFactorial N j : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hjN
  have hd : 0 < (Nat.descFactorial d j : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hjd
  have hk : 0 < (Nat.descFactorial k j : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hjk
  have hm : 0 < (Nat.descFactorial m j : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hjm
  unfold hypergeomFactorialValue
  exact div_pos (mul_pos hk hm) (mul_pos hN hd)

private theorem hypergeomFactorialValue_succ_ratio (N k m d j : ℕ)
    (hjd : j + 1 ≤ d) (hdm : d ≤ m) (hdk : d ≤ k)
    (hmkN : k + m ≤ N) :
    hypergeomFactorialValue N k m d (j + 1) /
        hypergeomFactorialValue N k m d j =
      (((k : ℝ) - j) * ((m : ℝ) - j)) /
        (((N : ℝ) - j) * ((d : ℝ) - j)) := by
  have hjk : j ≤ k := (Nat.le_of_succ_le hjd).trans hdk
  have hjm : j ≤ m := (Nat.le_of_succ_le hjd).trans hdm
  have hjN : j ≤ N := hjm.trans (by omega)
  have hkp : (Nat.descFactorial k j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hjk))
  have hmp : (Nat.descFactorial m j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hjm))
  have hNp : (Nat.descFactorial N j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.descFactorial_pos.mpr hjN))
  have hdp : (Nat.descFactorial d j : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (Nat.descFactorial_pos.mpr (Nat.le_of_succ_le hjd)))
  have hkj : (Nat.cast (k - j) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt
      (lt_of_lt_of_le (Nat.lt_of_succ_le hjd) hdk)))
  have hmj : (Nat.cast (m - j) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt
      (lt_of_lt_of_le (Nat.lt_of_succ_le hjd) hdm)))
  have hNj : (Nat.cast (N - j) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt
      (lt_of_lt_of_le (Nat.lt_of_succ_le hjd) (by omega))))
  have hdj : (Nat.cast (d - j) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.sub_pos_of_lt
      (Nat.lt_of_succ_le hjd)))
  unfold hypergeomFactorialValue
  simp only [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hjk,
    Nat.cast_sub hjm, Nat.cast_sub hjN,
    Nat.cast_sub (Nat.le_of_succ_le hjd)]
  field_simp [hkp, hmp, hNp, hdp, hkj, hmj, hNj, hdj]

/-- The denominator in the index formula is positive on the supported
upper-tail domain. -/
theorem hypergeomFactorialIndex_denominator_pos (N k m d : ℕ)
    (hd0 : 0 < d) (hdm : d ≤ m) (hdk : d ≤ k)
    (hmkN : k + m ≤ N) :
    0 < (N : ℝ) + d - k - m := by
  have hkN : k ≤ N := by omega
  have hmNk : m ≤ N - k := by omega
  have hcastk : (N : ℝ) - k = ((N - k : ℕ) : ℝ) := by
    rw [Nat.cast_sub hkN]
  have hcastm : ((N - k : ℕ) : ℝ) - m =
      ((N - k - m : ℕ) : ℝ) := by
    rw [Nat.cast_sub hmNk]
  have heq : (N : ℝ) + d - k - m =
      ((N - k - m : ℕ) : ℝ) + d := by
    rw [← hcastm, ← hcastk]
    ring
  rw [heq]
  have hd0' : (0 : ℝ) < d := by exact_mod_cast hd0
  have hnonneg : (0 : ℝ) ≤ (N - k - m : ℕ) := by positivity
  linarith

/-- Above the mean, the numerator of the continuous minimizing index is
strictly positive. -/
theorem hypergeomFactorialIndex_numerator_pos (N k m d : ℕ)
    (hmean : (k : ℝ) * m < (N : ℝ) * d) :
    0 < (N : ℝ) * d - (k : ℝ) * m := by
  linarith

/-- On the supported upper-tail domain the ceiling index is admissible. -/
theorem hypergeomFactorialIndex_mem (N k m d : ℕ)
    (hmean : (k : ℝ) * m < (N : ℝ) * d)
    (hd0 : 0 < d) (hdm : d ≤ m) (hdk : d ≤ k) (hmkN : k + m ≤ N) :
    1 ≤ hypergeomFactorialIndex N k m d ∧
      hypergeomFactorialIndex N k m d ≤ d := by
  have hB := hypergeomFactorialIndex_denominator_pos N k m d hd0 hdm hdk hmkN
  have hA := hypergeomFactorialIndex_numerator_pos N k m d hmean
  have hratio_pos : 0 <
      ((N : ℝ) * d - (k : ℝ) * m) /
        ((N : ℝ) + d - k - m) := div_pos hA hB
  have hratio_le_d :
      ((N : ℝ) * d - (k : ℝ) * m) /
        ((N : ℝ) + d - k - m) ≤ (d : ℝ) := by
    apply (div_le_iff₀ hB).2
    have hkd : 0 ≤ (k : ℝ) - d := by
      rw [← Nat.cast_sub hdk]
      positivity
    have hmd : 0 ≤ (m : ℝ) - d := by
      rw [← Nat.cast_sub hdm]
      positivity
    have hprod : 0 ≤ ((k : ℝ) - d) * ((m : ℝ) - d) :=
      mul_nonneg hkd hmd
    nlinarith
  dsimp [hypergeomFactorialIndex]
  constructor
  · have hc : 0 < ⌈((N : ℝ) * d - (k : ℝ) * m) /
        ((N : ℝ) + d - k - m)⌉₊ := Nat.ceil_pos.mpr hratio_pos
    omega
  · exact Nat.ceil_le.mpr hratio_le_d

/-- A consecutive candidate decreases exactly through the real cutoff
`(Nd-km)/(N+d-k-m)`. -/
theorem hypergeomFactorialValue_succ_le_iff (N k m d j : ℕ)
    (hjd : j + 1 ≤ d) (hdm : d ≤ m) (hdk : d ≤ k)
    (hmkN : k + m ≤ N) :
    hypergeomFactorialValue N k m d (j + 1) ≤
        hypergeomFactorialValue N k m d j ↔
      (j : ℝ) ≤ ((N : ℝ) * d - (k : ℝ) * m) /
        ((N : ℝ) + d - k - m) := by
  have hB := hypergeomFactorialIndex_denominator_pos N k m d
    (by omega : 0 < d) hdm hdk hmkN
  have hratio := hypergeomFactorialValue_succ_ratio N k m d j hjd hdm hdk hmkN
  have hpos := hypergeomFactorialValue_pos N k m d j
    (Nat.le_of_succ_le hjd) hdm hdk hmkN
  have hden : 0 < ((N : ℝ) - j) * ((d : ℝ) - j) := by
    have hjN : j < N := by omega
    have hjd' : j < d := by omega
    have hNjR : (0 : ℝ) < (N : ℝ) - j := by
      have hjR : (j : ℝ) < N := by exact_mod_cast hjN
      linarith
    have hdjR : (0 : ℝ) < (d : ℝ) - j := by
      have hjR : (j : ℝ) < d := by exact_mod_cast hjd'
      linarith
    exact mul_pos hNjR hdjR
  constructor
  · intro h
    have hquot : hypergeomFactorialValue N k m d (j + 1) /
        hypergeomFactorialValue N k m d j ≤ 1 :=
      (div_le_iff₀ hpos).2 (by simpa using h)
    rw [hratio] at hquot
    have hmul := (div_le_iff₀ hden).1 hquot
    apply (le_div_iff₀ hB).2
    nlinarith
  · intro h
    have hpoly : (j : ℝ) * ((N : ℝ) + d - k - m) ≤
        (N : ℝ) * d - (k : ℝ) * m :=
      (le_div_iff₀ hB).1 h
    have hmul : (((k : ℝ) - j) * ((m : ℝ) - j)) ≤
        ((N : ℝ) - j) * ((d : ℝ) - j) := by
      nlinarith
    have hquot : hypergeomFactorialValue N k m d (j + 1) /
        hypergeomFactorialValue N k m d j ≤ 1 := by
      rw [hratio]
      exact (div_le_iff₀ hden).2 (by simpa using hmul)
    have hlast := (div_le_iff₀ hpos).1 hquot
    simpa using hlast

private theorem hypergeomFactorialValue_le_prefix (N k m d : ℕ)
    (hdm : d ≤ m) (hdk : d ≤ k) (hmkN : k + m ≤ N)
    (hidxmem : hypergeomFactorialIndex N k m d ≤ d) :
    ∀ i j : ℕ, i ≤ j → j ≤ hypergeomFactorialIndex N k m d →
      hypergeomFactorialValue N k m d j ≤ hypergeomFactorialValue N k m d i := by
  intro i j
  induction j generalizing i with
  | zero =>
      intro hij hidx
      have hi : i = 0 := by omega
      subst i
      rfl
  | succ j ih =>
      intro hij hidx
      by_cases hij' : i ≤ j
      · have hstepIdx : j < hypergeomFactorialIndex N k m d := by omega
        have hreal : (j : ℝ) <
            ((N : ℝ) * d - (k : ℝ) * m) /
              ((N : ℝ) + d - k - m) := by
          have hceil : j < ⌈((N : ℝ) * d - (k : ℝ) * m) /
              ((N : ℝ) + d - k - m)⌉₊ := by
            simpa [hypergeomFactorialIndex] using hstepIdx
          exact Nat.lt_ceil.mp hceil
        have hjd' : j + 1 ≤ d := hidx.trans hidxmem
        have hstep := (hypergeomFactorialValue_succ_le_iff N k m d j
          hjd' hdm hdk hmkN).2 hreal.le
        exact hstep.trans (ih i hij' (by omega))
      · have hi : i = j + 1 := by omega
        subst i
        exact le_rfl

private theorem hypergeomFactorialValue_le_suffix (N k m d : ℕ)
    (hd0 : 0 < d) (hdm : d ≤ m) (hdk : d ≤ k) (hmkN : k + m ≤ N)
    (hidxmem : hypergeomFactorialIndex N k m d ≤ d) :
    ∀ j : ℕ, hypergeomFactorialIndex N k m d ≤ j → j ≤ d →
      hypergeomFactorialValue N k m d (hypergeomFactorialIndex N k m d) ≤
        hypergeomFactorialValue N k m d j := by
  intro j
  induction j with
  | zero =>
      intro hidx hjd
      have hidx0 : hypergeomFactorialIndex N k m d = 0 := by omega
      simpa [hidx0]
  | succ j ih =>
      intro hidx hjd
      by_cases hidxj : hypergeomFactorialIndex N k m d ≤ j
      · have hprev := ih hidxj (by omega)
        have hjd' : j + 1 ≤ d := by omega
        have hB := hypergeomFactorialIndex_denominator_pos N k m d
          (by omega) hdm hdk hmkN
        have hratioCut :
            ((N : ℝ) * d - (k : ℝ) * m) /
              ((N : ℝ) + d - k - m) ≤
                (hypergeomFactorialIndex N k m d : ℝ) := by
          dsimp [hypergeomFactorialIndex]
          exact Nat.le_ceil _
        have hidxR : (hypergeomFactorialIndex N k m d : ℝ) ≤ j := by
          exact_mod_cast hidxj
        have hcut :
            ((N : ℝ) * d - (k : ℝ) * m) /
              ((N : ℝ) + d - k - m) ≤ (j : ℝ) :=
          hratioCut.trans hidxR
        have hstep : hypergeomFactorialValue N k m d j ≤
            hypergeomFactorialValue N k m d (j + 1) := by
          by_cases hjeq : (j : ℝ) =
              ((N : ℝ) * d - (k : ℝ) * m) /
                ((N : ℝ) + d - k - m)
          · have hcross : (j : ℝ) * ((N : ℝ) + d - k - m) =
                (N : ℝ) * d - (k : ℝ) * m := by
              calc
                (j : ℝ) * ((N : ℝ) + d - k - m) =
                    (((N : ℝ) * d - (k : ℝ) * m) /
                      ((N : ℝ) + d - k - m) *
                        ((N : ℝ) + d - k - m)) := by rw [hjeq]
                _ = (N : ℝ) * d - (k : ℝ) * m := by
                  exact div_mul_cancel₀ _ hB.ne'
            have hpoly : (((k : ℝ) - j) * ((m : ℝ) - j)) =
                (((N : ℝ) - j) * ((d : ℝ) - j)) := by
              nlinarith
            have hden : 0 < ((N : ℝ) - j) * ((d : ℝ) - j) := by
              have hjN : j < N := by omega
              have hjd'' : j < d := by omega
              have hNj : (0 : ℝ) < (N : ℝ) - j := by
                have : (j : ℝ) < N := by exact_mod_cast hjN
                linarith
              have hdj : (0 : ℝ) < (d : ℝ) - j := by
                have : (j : ℝ) < d := by exact_mod_cast hjd''
                linarith
              exact mul_pos hNj hdj
            have hratio := hypergeomFactorialValue_succ_ratio N k m d j
              hjd' hdm hdk hmkN
            have hquot : hypergeomFactorialValue N k m d (j + 1) /
                hypergeomFactorialValue N k m d j = 1 := by
              rw [hratio, hpoly, div_self hden.ne']
            have hvalpos := hypergeomFactorialValue_pos N k m d j
              (by omega) hdm hdk hmkN
            have hmul :
                (hypergeomFactorialValue N k m d (j + 1) /
                  hypergeomFactorialValue N k m d j) *
                  hypergeomFactorialValue N k m d j =
                hypergeomFactorialValue N k m d (j + 1) := by
              field_simp [hvalpos.ne']
            rw [hquot] at hmul
            have hvaleq : hypergeomFactorialValue N k m d j =
                hypergeomFactorialValue N k m d (j + 1) := by
              simpa using hmul
            exact hvaleq.le
          · have hnot : ¬ hypergeomFactorialValue N k m d (j + 1) ≤
                hypergeomFactorialValue N k m d j := by
              intro hle
              have hlecut := (hypergeomFactorialValue_succ_le_iff N k m d j
                hjd' hdm hdk hmkN).1 hle
              exact hjeq (le_antisymm hlecut hcut)
            exact le_of_not_ge hnot
        exact hprev.trans hstep
      · have hidxEq : hypergeomFactorialIndex N k m d = j + 1 := by omega
        simpa [hidxEq]

/-- The ceiling index is a minimizer among every admissible factorial
candidate; an integral cutoff permits the adjacent tie. -/
theorem hypergeomFactorialValue_index_min (N k m d : ℕ)
    (hmean : (k : ℝ) * m < (N : ℝ) * d)
    (hd0 : 0 < d) (hdm : d ≤ m) (hdk : d ≤ k) (hmkN : k + m ≤ N)
    (j : ℕ) (hjd : j ≤ d) :
    hypergeomFactorialValue N k m d (hypergeomFactorialIndex N k m d) ≤
      hypergeomFactorialValue N k m d j := by
  have hidx := hypergeomFactorialIndex_mem N k m d hmean hd0 hdm hdk hmkN
  by_cases hji : j ≤ hypergeomFactorialIndex N k m d
  · exact hypergeomFactorialValue_le_prefix N k m d hdm hdk hmkN hidx.2
      j (hypergeomFactorialIndex N k m d) hji le_rfl
  · have hij : hypergeomFactorialIndex N k m d ≤ j := by omega
    exact hypergeomFactorialValue_le_suffix N k m d hd0 hdm hdk hmkN hidx.2
      j hij hjd

/-- The closed form above is exactly the finite factorial candidate used by
`finiteFactorialBound`. -/
theorem hypergeomFactorialCandidate_eq_value (N k m d j : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (hdm : d ≤ m) (hjd : j ≤ d) :
    finiteFactorialCandidate (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d j = hypergeomFactorialValue N k m d j := by
  simpa [hypergeomFactorialValue] using
    (hypergeom_factorial_candidate_formula N k m d j hk hm hdm hjd)

/-- The optimized factorial bound is bounded by the admissible ceiling
candidate, so the displayed index gives a certified integer-threshold bound. -/
theorem hypergeomFactorialBound_le_ceiling_candidate (N k m d : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (hmean : (k : ℝ) * m < (N : ℝ) * d)
    (hd0 : 0 < d) (hdm : d ≤ m) (hdk : d ≤ k) (hmkN : k + m ≤ N) :
    finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d ≤
      hypergeomFactorialValue N k m d (hypergeomFactorialIndex N k m d) := by
  have hi := hypergeomFactorialIndex_mem N k m d hmean hd0 hdm hdk hmkN
  rw [← hypergeomFactorialCandidate_eq_value N k m d
    (hypergeomFactorialIndex N k m d) hk hm hdm hi.2]
  exact finiteFactorialBound_le_candidate
    (Finset.range (m + 1)) (fun i => i) (hypergeomMass N k m) d
    (hypergeomFactorialIndex N k m d) hi.2


/-- The minimum defining `finiteFactorialBound` is attained at the explicit
ceiling index on the supported strict upper-tail domain. -/
theorem hypergeomFactorialBound_eq_ceiling_candidate (N k m d : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (hmean : (k : ℝ) * m < (N : ℝ) * d)
    (hd0 : 0 < d) (hdm : d ≤ m) (hdk : d ≤ k) (hmkN : k + m ≤ N) :
    finiteFactorialBound (Finset.range (m + 1)) (fun i => i)
        (hypergeomMass N k m) d =
      hypergeomFactorialValue N k m d (hypergeomFactorialIndex N k m d) := by
  apply le_antisymm
  · exact hypergeomFactorialBound_le_ceiling_candidate N k m d hk hm
      hmean hd0 hdm hdk hmkN
  · unfold finiteFactorialBound
    apply Finset.le_min'
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨j, hj, hvalue⟩
    have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    rw [← hvalue, hypergeomFactorialCandidate_eq_value N k m d j hk hm hdm hjd]
    exact hypergeomFactorialValue_index_min N k m d hmean hd0 hdm hdk hmkN j hjd

end
end ExactHoeffding
