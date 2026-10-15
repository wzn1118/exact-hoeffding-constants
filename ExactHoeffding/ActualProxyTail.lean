import ExactHoeffding.RescaledActualProxy

/-! # Uniform tilt-tail bound from the actual finite support -/

namespace ExactHoeffding

noncomputable section

theorem finiteMGF_le_exp_abs_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w x : ι → ℝ) (B t : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hs : ∑ i ∈ S, w i = 1)
    (hb : ∀ i ∈ S, |x i| ≤ B) :
    finiteMGF S w x t ≤ Real.exp (|t| * B) := by
  unfold finiteMGF
  calc
    (∑ i ∈ S, w i * Real.exp (t * x i)) ≤
        ∑ i ∈ S, w i * Real.exp (|t| * B) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hw i hi)
      apply Real.exp_le_exp.mpr
      calc
        t * x i ≤ |t * x i| := le_abs_self _
        _ = |t| * |x i| := abs_mul _ _
        _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hb i hi) (abs_nonneg t)
    _ = Real.exp (|t| * B) := by rw [← Finset.sum_mul, hs, one_mul]

theorem finite_logMGF_proxy_tail_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (w x : ι → ℝ) (B t : ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hs : ∑ i ∈ S, w i = 1)
    (hb : ∀ i ∈ S, |x i| ≤ B) (ht : t ≠ 0) :
    2 * Real.log (finiteMGF S w x t) / t ^ 2 ≤ 2 * B / |t| := by
  have hpos := finiteMGF_pos_of_normalized S w x hw hs t
  have hlog : Real.log (finiteMGF S w x t) ≤ |t| * B :=
    (Real.log_le_iff_le_exp hpos).mpr (finiteMGF_le_exp_abs_bound S w x B t hw hs hb)
  calc
    2 * Real.log (finiteMGF S w x t) / t ^ 2 ≤
        2 * (|t| * B) / t ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg t)
      linarith
    _ = 2 * B / |t| := by
      rw [← sq_abs t]
      field_simp

theorem hypergeom_centered_values_abs_le (N k m i : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hi : i ≤ m) :
    |(i : ℝ) - (k : ℝ) * (m : ℝ) / N| ≤ (m : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hiR : (i : ℝ) ≤ m := by exact_mod_cast hi
  have hμ0 : 0 ≤ (k : ℝ) * (m : ℝ) / N := by positivity
  have hμm : (k : ℝ) * (m : ℝ) / N ≤ m := by
    apply (div_le_iff₀ hNR).mpr
    nlinarith [show (0 : ℝ) ≤ m by positivity]
  exact abs_le.mpr ⟨by nlinarith [show (0 : ℝ) ≤ i by positivity], by linarith⟩

/-- This bound is uniform in every admissible population, not an asymptotic proxy. -/
theorem actualHypergeomProxy_tail_bound (N k m : ℕ)
    (hN : 0 < N) (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) (ht : t ≠ 0) :
    actualHypergeomProxy N k m t ≤ 2 * (m : ℝ) / |t| := by
  rw [actualHypergeomProxy, if_neg ht]
  exact finite_logMGF_proxy_tail_bound (Finset.range (m + 1))
    (hypergeomMass N k m) (fun i => (i : ℝ) - (k : ℝ) * (m : ℝ) / N)
    m t (fun i _ => hypergeomMass_nonneg N k m i) (hypergeomMass_total N k m hk hm)
    (fun i hi => hypergeom_centered_values_abs_le N k m i hN hk
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) ht

end

end ExactHoeffding
