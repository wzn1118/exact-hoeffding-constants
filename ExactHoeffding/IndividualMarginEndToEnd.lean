import ExactHoeffding.IndividualMarginStrictMono

/-! # Positive quantitative deficit for every noncentral margin -/

namespace ExactHoeffding
noncomputable section

/-- The paper's parity-dependent deficit is strictly positive for every
nondegenerate fixed sample, even when no noncentral count exists. -/
theorem individualMarginDelta_pos (N m : ℕ)
    (hN : 2 ≤ N) (hm : 0 < m) (hmN : m < N) :
    0 < individualMarginDelta N m := by
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hM : 0 < individualMarginM N m := by
    unfold individualMarginM
    apply div_pos
    · exact mul_pos (by exact_mod_cast hm) (by exact_mod_cast (by omega : 0 < N-m))
    · linarith
  unfold individualMarginDelta
  split_ifs
  · exact div_pos hM (by positivity)
  · apply div_pos (mul_pos hM (by nlinarith [sq_nonneg ((N:ℝ)-2)]))
    positivity

/-- The actual optimal proxy has the exact individual-margin deficit, which
is at least the strictly positive parity-uniform deficit. -/
theorem hypergeomOptimalProxy_individualMargin_end_to_end
    (N k m : ℕ) (hN : 2 ≤ N) (hk : 0 < k) (hkN : k < N)
    (hm : 0 < m) (hmN : m < N)
    (hkc : k ≠ N/2) (hkc' : k ≠ N-N/2) :
    0 < individualMarginDelta N m ∧
      individualMarginDelta N m ≤ individualMarginGap N k m ∧
      hypergeomOptimalProxy N k m ≤ individualMarginW N m - individualMarginGap N k m ∧
      hypergeomOptimalProxy N k m ≤ individualMarginW N m - individualMarginDelta N m ∧
      hypergeomOptimalProxy N k m < individualMarginW N m := by
  have hpos := individualMarginDelta_pos N m hN hm hmN
  have hgap := individualMarginGap_ge_parityDelta_all N k m hN hk hkN hm hmN hkc hkc'
  have hproxy := hypergeomOptimalProxy_le_individualMarginGap N k m hN hk hkN hm hmN hkc hkc'
  exact ⟨hpos, hgap, hproxy, by linarith, by linarith⟩

end
end ExactHoeffding
