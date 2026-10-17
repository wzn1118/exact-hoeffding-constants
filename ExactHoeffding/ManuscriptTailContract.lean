import ExactHoeffding.SharpWeightedTail
import ExactHoeffding.ExactParityConstants
import Mathlib.Algebra.BigOperators.Fin

open MeasureTheory
open scoped BigOperators

namespace ExactHoeffding
noncomputable section

/-- The paper's zero padding of a length-`n` weight vector to the population. -/
def manuscriptPadWeights {n N : ℕ} (w : Fin n → ℝ) : Fin N → ℝ :=
  fun i => if hi : i.val < n then w ⟨i.val, hi⟩ else 0

theorem manuscript_pad_weighted_sum_eq {n N : ℕ} (hn : n ≤ N)
    (w : Fin n → ℝ) (g : Fin N → ℝ) :
    (∑ i : Fin N, manuscriptPadWeights (N := N) w i * g i) =
      ∑ i : Fin n, w i * g (Fin.castLE hn i) := by
  classical
  let r := N - n
  have hN : n + r = N := by dsimp [r]; omega
  let f : Fin N → ℝ := fun i => manuscriptPadWeights (N := N) w i * g i
  have hcast : (∑ i : Fin (n + r), f (Fin.cast hN i)) = ∑ i : Fin N, f i :=
    Equiv.sum_comp (Fin.castOrderIso hN).toEquiv f
  calc
    ∑ i : Fin N, manuscriptPadWeights (N := N) w i * g i =
        ∑ i : Fin (n + r), f (Fin.cast hN i) := hcast.symm
    _ = (∑ i : Fin n, f (Fin.cast hN (Fin.castAdd r i))) +
        ∑ i : Fin r, f (Fin.cast hN (Fin.natAdd n i)) := by
      rw [Fin.sum_univ_add]
    _ = ∑ i : Fin n, w i * g (Fin.castLE hn i) := by
      have hleft (i : Fin n) :
          f (Fin.cast hN (Fin.castAdd r i)) = w i * g (Fin.castLE hn i) := by
        dsimp [f, manuscriptPadWeights]
        have hi : (Fin.cast hN (Fin.castAdd r i)).val = i.val := by simp [Fin.castAdd]
        have he : Fin.castLE hn i = Fin.cast hN (Fin.castAdd r i) := Fin.ext hi.symm
        simp [he]
      have hright (i : Fin r) : f (Fin.cast hN (Fin.natAdd n i)) = 0 := by
        dsimp [f, manuscriptPadWeights]
        have hi : n ≤ (Fin.cast hN (Fin.natAdd n i)).val := by simp [Fin.natAdd]
        simp
      simp_rw [hleft, hright]
      simp

/-- The centered weighted statistic in Corollary `cor:tail`, written with
its original length-`n` weights. -/
def manuscriptTailStatistic {n N : ℕ} (hn : n ≤ N)
    (w : Fin n → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ i : Fin n, w i * (x (Fin.castLE hn i) - (∑ j : Fin N, x j) / (N : ℝ))

theorem manuscript_tail_statistic_eq_padded {n N : ℕ} (hn : n ≤ N)
    (w : Fin n → ℝ) (x : Fin N → ℝ) :
    manuscriptTailStatistic hn w x =
      ∑ i : Fin N, manuscriptPadWeights (N := N) w i *
        (x i - (∑ j : Fin N, x j) / (N : ℝ)) := by
  unfold manuscriptTailStatistic
  exact (manuscript_pad_weighted_sum_eq hn w
    (fun i => x i - (∑ j : Fin N, x j) / (N : ℝ))).symm

theorem manuscript_parity_constant_closed_form (N : ℕ) (hN : 2 ≤ N) :
    paritySharpConstant N = if Even N then (N : ℝ) / ((N : ℝ) - 1) else
      1 / (((N : ℝ) - 1) * Real.artanh (1 / (N : ℝ))) := by
  obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' N
  · subst N
    have he : Even (2 * q) := ⟨q, by omega⟩
    simp [paritySharpConstant, he]
  · subst N
    have he : ¬ Even (2 * q + 1) := by
      intro h
      obtain ⟨r, hr⟩ := h
      omega
    rw [paritySharpConstant, if_neg he]
    rw [if_neg he]
    exact oddHypergeomConstant_eq_artanh (2 * q + 1) (by omega)

/-- Typed statement contract for the frozen weighted finite-exchangeability
corollary. It includes the zero-padded finite weight vector, the actual
exchangeable probability law on the cube, the one-sided confidence event,
the degenerate projected-variance case, and optimality of the exact constant. -/
theorem manuscript_cor_tail_contract (N n : ℕ) (hN : 2 ≤ N)
    (_hn0 : 1 ≤ n) (hnN : n ≤ N)
    (μ : Measure (Fin N → ℝ)) [IsProbabilityMeasure μ]
    (hex : FiniteExchangeableMeasure μ)
    (hcube : ∀ᵐ x ∂μ, x ∈ realCube N) (w : Fin n → ℝ) :
    (paritySharpConstant N = if Even N then (N : ℝ) / ((N : ℝ) - 1) else
        1 / (((N : ℝ) - 1) * Real.artanh (1 / (N : ℝ)))) ∧
    (∀ t : ℝ,
      (∫ x, Real.exp (t * manuscriptTailStatistic hnN w x) ∂μ) ≤
        Real.exp (t ^ 2 * paritySharpConstant N *
          projectedWeightVariance (manuscriptPadWeights (N := N) w) / 2)) ∧
    (0 < projectedWeightVariance (manuscriptPadWeights (N := N) w) →
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        μ.real {x | Real.sqrt (2 * paritySharpConstant N *
            projectedWeightVariance (manuscriptPadWeights (N := N) w) * Real.log (1 / δ)) ≤
          manuscriptTailStatistic hnN w x} ≤ δ) ∧
    (projectedWeightVariance (manuscriptPadWeights (N := N) w) = 0 →
      ((∀ t : ℝ,
        (∫ x, Real.exp (t * manuscriptTailStatistic hnN w x) ∂μ) = 1) ∧
       (∀ s : ℝ, 0 < s →
        μ.real {x | s ≤ manuscriptTailStatistic hnN w x} = 0))) ∧
    IsExchangeableCoefficient N (paritySharpConstant N) ∧
    (∀ C : ℝ, IsExchangeableCoefficient N C → paritySharpConstant N ≤ C) := by
  have hformula := manuscript_parity_constant_closed_form N hN
  have hvalid := paritySharpConstant_is_valid N hN
  have hleast := paritySharpConstant_is_least N hN
  have hmgf (t : ℝ) :
      (∫ x, Real.exp (t * manuscriptTailStatistic hnN w x) ∂μ) ≤
        Real.exp (t ^ 2 * paritySharpConstant N *
          projectedWeightVariance (manuscriptPadWeights (N := N) w) / 2) := by
    have h := sharp_weighted_exp_bound N hN μ hex hcube (manuscriptPadWeights (N := N) w) t
    simpa only [manuscript_tail_statistic_eq_padded, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hconfidence (hV : 0 < projectedWeightVariance (manuscriptPadWeights (N := N) w))
      (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
      μ.real {x | Real.sqrt (2 * paritySharpConstant N *
          projectedWeightVariance (manuscriptPadWeights (N := N) w) * Real.log (1 / δ)) ≤
        manuscriptTailStatistic hnN w x} ≤ δ := by
    have h := sharp_weighted_confidence_bound N hN μ hex hcube
      (manuscriptPadWeights (N := N) w) hV δ hδ hδ1
    simpa only [manuscript_tail_statistic_eq_padded] using h
  have hzero (hV : projectedWeightVariance (manuscriptPadWeights (N := N) w) = 0) :
      ∀ x : Fin N → ℝ, manuscriptTailStatistic hnN w x = 0 := by
    have hwc := (projectedWeightVariance_eq_zero_iff N (by omega)
      (manuscriptPadWeights (N := N) w)).1 hV
    intro x
    rw [manuscript_tail_statistic_eq_padded]
    rw [← centerContrast_linear_contrast]
    apply Finset.sum_eq_zero
    intro i hi
    simp [centerContrast, hwc i]
  have hmgf_zero (hV : projectedWeightVariance (manuscriptPadWeights (N := N) w) = 0)
      (t : ℝ) :
      (∫ x, Real.exp (t * manuscriptTailStatistic hnN w x) ∂μ) = 1 := by
    simp_rw [hzero hV, mul_zero, Real.exp_zero]
    simp
  have htail_zero (hV : projectedWeightVariance (manuscriptPadWeights (N := N) w) = 0)
      (s : ℝ) (hs : 0 < s) :
      μ.real {x | s ≤ manuscriptTailStatistic hnN w x} = 0 := by
    have h := weighted_tail_zero_of_projectedVariance_zero N (by omega) μ
      (manuscriptPadWeights (N := N) w) hV s hs
    simpa only [manuscript_tail_statistic_eq_padded] using h
  exact ⟨hformula, hmgf, fun hV δ hδ hδ1 => hconfidence hV δ hδ hδ1,
    fun hV => ⟨hmgf_zero hV, fun s hs => htail_zero hV s hs⟩,
    hvalid, fun C hC => hleast C hC⟩

end
end ExactHoeffding
