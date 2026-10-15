import ExactHoeffding.JacobiMobius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ExactHoeffding

/-- A real linear factor normalized to have constant coefficient one. -/
noncomputable def jacobiRootNormalizedFactor (x : ℝ) : Polynomial ℝ :=
  Polynomial.C 1 - Polynomial.C (x⁻¹) * Polynomial.X

/-- Success probability of the Bernoulli factor contributed by a negative root. -/
noncomputable def jacobiTiltedRootProbability (z x : ℝ) : ℝ := z / (z - x)

/-- The probability generating factor for a Bernoulli variable. -/
noncomputable def jacobiTiltedRootPGFFactor (z x y : ℝ) : ℝ :=
  1 - jacobiTiltedRootProbability z x + jacobiTiltedRootProbability z x * y

theorem jacobiTiltedRootProbability_mem_Ioo {z x : ℝ} (hz : 0 < z) (hx : x < 0) :
    jacobiTiltedRootProbability z x ∈ Set.Ioo 0 1 := by
  have hden : 0 < z - x := sub_pos.mpr (lt_trans hx hz)
  constructor
  · exact div_pos hz hden
  · rw [jacobiTiltedRootProbability, div_lt_one hden]
    linarith

private theorem jacobiRootNormalizedFactor_eval_mul_pgfFactor
    {z x y : ℝ} (hz : 0 < z) (hx : x < 0) :
    (jacobiRootNormalizedFactor x).eval (z * y) =
      (jacobiRootNormalizedFactor x).eval z * jacobiTiltedRootPGFFactor z x y := by
  have hxne : x ≠ 0 := ne_of_lt hx
  have hden : z - x ≠ 0 := ne_of_gt (sub_pos.mpr (lt_trans hx hz))
  simp only [jacobiRootNormalizedFactor, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, jacobiTiltedRootPGFFactor,
    jacobiTiltedRootProbability]
  field_simp [hxne, hden] <;> ring

theorem splits_eq_eval_mul_rootNormalizedFactors {p : Polynomial ℝ}
    (hp : p.Splits) (hnz : ∀ x ∈ p.roots, x ≠ 0) :
    p = Polynomial.C (p.eval 0) *
      (p.roots.map jacobiRootNormalizedFactor).prod := by
  classical
  let m := p.roots
  have heval : p.eval 0 = p.leadingCoeff * (m.map fun x : ℝ => -x).prod := by
    simpa [m] using hp.eval_eq_prod_roots (0 : ℝ)
  have hCprod :
      Polynomial.C ((m.map fun x : ℝ => -x).prod) =
        (m.map fun x : ℝ => Polynomial.C (-x)).prod := by
    simpa [m, Multiset.map_map, Function.comp_def] using
      (map_multiset_prod (Polynomial.C : ℝ →+* Polynomial ℝ)
        (m.map fun x : ℝ => -x))
  have hlinear (x : ℝ) (hx : x ≠ 0) :
      Polynomial.C (-x) * jacobiRootNormalizedFactor x =
        Polynomial.X - Polynomial.C x := by
    unfold jacobiRootNormalizedFactor
    calc
      Polynomial.C (-x) *
          (Polynomial.C 1 - Polynomial.C (x⁻¹) * Polynomial.X) =
        Polynomial.C (-x) - Polynomial.C ((-x) * x⁻¹) * Polynomial.X := by
          simp only [Polynomial.C_1, mul_sub, mul_one, ← mul_assoc,
            ← Polynomial.C_mul]
      _ = Polynomial.X - Polynomial.C x := by
          have hmul : (-x) * x⁻¹ = -1 := by field_simp [hx]
          rw [hmul]
          simp only [map_neg, Polynomial.C_1]
          ring
  have hmap :
      m.map (fun x : ℝ => Polynomial.X - Polynomial.C x) =
        m.map (fun x : ℝ => Polynomial.C (-x) * jacobiRootNormalizedFactor x) := by
    apply Multiset.map_congr rfl
    intro x hx
    exact (hlinear x (hnz x hx)).symm
  calc
    p = Polynomial.C p.leadingCoeff *
        (m.map fun x : ℝ => Polynomial.X - Polynomial.C x).prod := by
      simpa [m] using hp.eq_prod_roots
    _ = Polynomial.C p.leadingCoeff *
        (m.map fun x : ℝ =>
          Polynomial.C (-x) * jacobiRootNormalizedFactor x).prod := by
      rw [hmap]
    _ = Polynomial.C p.leadingCoeff *
        ((m.map fun x : ℝ => Polynomial.C (-x)).prod *
          (m.map jacobiRootNormalizedFactor).prod) := by
      rw [Multiset.prod_map_mul]
    _ = Polynomial.C (p.leadingCoeff * (m.map fun x : ℝ => -x).prod) *
        (m.map jacobiRootNormalizedFactor).prod := by
      rw [← hCprod]
      rw [← mul_assoc, ← Polynomial.C_mul]
    _ = Polynomial.C (p.eval 0) *
        (m.map jacobiRootNormalizedFactor).prod := by rw [← heval]

private theorem reverse_roots_product (s : Multiset ℝ) :
    ((s.map fun x : ℝ =>
      (Polynomial.X - Polynomial.C x : Polynomial ℝ)).prod).reverse =
      (s.map fun x : ℝ =>
        (Polynomial.X - Polynomial.C x : Polynomial ℝ).reverse).prod := by
  induction s using Multiset.induction_on with
  | empty =>
      simpa only [Multiset.map_zero, Multiset.prod_zero, Polynomial.C_1] using
        (Polynomial.reverse_C (1 : ℝ))
  | @cons x s ih =>
      simp [Polynomial.reverse_mul_of_domain, ih]

private theorem reverse_linear_splits (x : ℝ) :
    ((Polynomial.X - Polynomial.C x : Polynomial ℝ).reverse).Splits := by
  apply Polynomial.Splits.of_natDegree_le_one
  exact (Polynomial.reverse_natDegree_le _).trans_eq
    (Polynomial.natDegree_X_sub_C x)

theorem splits_reverse_of_splits {p : Polynomial ℝ} (hp : p.Splits) :
    p.reverse.Splits := by
  rw [hp.eq_prod_roots, Polynomial.reverse_mul_of_domain,
    Polynomial.reverse_C, reverse_roots_product]
  apply (Polynomial.Splits.multisetProd ?_).C_mul p.leadingCoeff
  intro q hq
  rcases Multiset.mem_map.mp hq with ⟨x, hx, rfl⟩
  exact reverse_linear_splits x

theorem jacobiPGF_splits (j h r : ℕ) :
    (jacobiPGF j h r).Splits := by
  rw [jacobiPGF_eq_rodrigues_mobius]
  have hsplit : (jacobiRodrigues j h r).reverse.Splits :=
    splits_reverse_of_splits (jacobiRodrigues_splits j h r)
  have hshift :
      ((jacobiRodrigues j h r).reverse.comp
        (Polynomial.X + Polynomial.C (1 : ℝ))).Splits :=
    hsplit.comp_X_add_C 1
  have hreflect :
      (((jacobiRodrigues j h r).reverse.comp
        (Polynomial.X + Polynomial.C (1 : ℝ))).comp (-Polynomial.X)).Splits :=
    hshift.comp_neg_X
  have harg :
      (Polynomial.X + Polynomial.C (1 : ℝ)).comp (-Polynomial.X) =
        Polynomial.C 1 - Polynomial.X := by
    rw [Polynomial.add_comp]
    simp [sub_eq_add_neg, add_comm]
  have hcomp :
      ((jacobiRodrigues j h r).reverse.comp
        (Polynomial.X + Polynomial.C (1 : ℝ))).comp (-Polynomial.X) =
      (jacobiRodrigues j h r).reverse.comp
        (Polynomial.C 1 - Polynomial.X) := by
    rw [Polynomial.comp_assoc, harg]
  rw [← hcomp]
  exact hreflect

theorem jacobiPGF_natDegree (j h r : ℕ) :
    (jacobiPGF j h r).natDegree = j := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · apply (Polynomial.natDegree_le_iff_coeff_eq_zero).2
    intro n hn
    rw [jacobiPGF_coeff]
    simp [not_le_of_gt hn]
  · rw [jacobiPGF_coeff]
    have hpos : 0 < (jacobiCoeff j h r j : ℝ) := by
      exact_mod_cast jacobiCoeff_pos (j := j) (h := h) (r := r) (i := j)
        (Nat.le_refl j)
    exact ne_of_gt (by simpa using hpos)

theorem jacobiPGF_roots_card (j h r : ℕ) :
    (jacobiPGF j h r).roots.card = j := by
  calc
    (jacobiPGF j h r).roots.card = (jacobiPGF j h r).natDegree :=
      (jacobiPGF_splits j h r).natDegree_eq_card_roots.symm
    _ = j := jacobiPGF_natDegree j h r

theorem jacobiPGF_real_root_factorization (j h r : ℕ) :
    jacobiPGF j h r =
      Polynomial.C (jacobiPGF j h r).leadingCoeff *
        (((jacobiPGF j h r).roots.map
          (fun x => Polynomial.X - Polynomial.C x)).prod) :=
  (jacobiPGF_splits j h r).eq_prod_roots

theorem jacobiPGF_eval_pos_of_nonneg (j h r : ℕ) {x : ℝ}
    (hx : 0 ≤ x) : 0 < (jacobiPGF j h r).eval x := by
  classical
  simp only [jacobiPGF, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)
  · refine ⟨0, by simp, ?_⟩
    have hzero : 0 < jacobiCoeff j h r 0 := jacobiCoeff_pos (by omega)
    simpa using (show 0 < (jacobiCoeff j h r 0 : ℝ) by exact_mod_cast hzero)

theorem jacobiPGF_roots_negative (j h r : ℕ) {x : ℝ}
    (hx : x ∈ (jacobiPGF j h r).roots) : x < 0 := by
  by_contra hnot
  have hx_nonneg : 0 ≤ x := le_of_not_gt hnot
  have hpos := jacobiPGF_eval_pos_of_nonneg j h r hx_nonneg
  have hroot : (jacobiPGF j h r).eval x = 0 :=
    Polynomial.isRoot_of_mem_roots hx
  exact (ne_of_gt hpos) hroot

theorem jacobiPGF_root_normalized_factorization (j h r : ℕ) :
    jacobiPGF j h r =
      Polynomial.C ((jacobiPGF j h r).eval 0) *
        ((jacobiPGF j h r).roots.map jacobiRootNormalizedFactor).prod := by
  apply splits_eq_eval_mul_rootNormalizedFactors (jacobiPGF_splits j h r)
  intro x hx
  exact ne_of_lt (jacobiPGF_roots_negative j h r hx)

theorem jacobiPGF_tilted_bernoulli_pgF (j h r : ℕ) {z : ℝ} (hz : 0 < z)
    (y : ℝ) :
    (jacobiPGF j h r).eval (z * y) / (jacobiPGF j h r).eval z =
      ((jacobiPGF j h r).roots.map
        (fun x => jacobiTiltedRootPGFFactor z x y)).prod := by
  classical
  let p := jacobiPGF j h r
  let m := p.roots
  let rootEval (w x : ℝ) := (jacobiRootNormalizedFactor x).eval w
  let A := (m.map fun x : ℝ => rootEval z x).prod
  let B := (m.map fun x : ℝ => jacobiTiltedRootPGFFactor z x y).prod
  have hfactor (w : ℝ) : p.eval w = p.eval 0 *
      (m.map fun x : ℝ => rootEval w x).prod := by
    have hf := congrArg (fun q : Polynomial ℝ => q.eval w)
      (jacobiPGF_root_normalized_factorization j h r)
    simpa only [Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_apply] using hf
  have hmap : m.map (fun x : ℝ => rootEval (z * y) x) =
      m.map (fun x : ℝ => rootEval z x * jacobiTiltedRootPGFFactor z x y) := by
    apply Multiset.map_congr rfl
    intro x hx
    dsimp [m, p, rootEval]
    exact jacobiRootNormalizedFactor_eval_mul_pgfFactor hz
      (jacobiPGF_roots_negative j h r hx)
  have hprod :
      (m.map fun x : ℝ => rootEval (z * y) x).prod = A * B := by
    calc
      (m.map fun x : ℝ => rootEval (z * y) x).prod =
          (m.map fun x : ℝ =>
            rootEval z x * jacobiTiltedRootPGFFactor z x y).prod :=
              congrArg Multiset.prod hmap
      _ = A * B := by
        simp only [Multiset.prod_map_mul, A, B]
  have hzero : 0 < p.eval 0 := by
    dsimp [p]
    exact jacobiPGF_eval_pos_of_nonneg j h r (le_refl 0)
  have hden : 0 < p.eval z := by
    dsimp [p]
    exact jacobiPGF_eval_pos_of_nonneg j h r hz.le
  have hA : A ≠ 0 := by
    intro hA0
    have heq : p.eval z = p.eval 0 * A := hfactor z
    rw [hA0, mul_zero] at heq
    exact (ne_of_gt hden) heq
  have hnum : p.eval (z * y) = p.eval 0 * (A * B) := by
    calc
      p.eval (z * y) = p.eval 0 *
          (m.map fun x : ℝ => rootEval (z * y) x).prod := hfactor (z * y)
      _ = p.eval 0 * (A * B) := by rw [hprod]
  have hden' : p.eval z = p.eval 0 * A := hfactor z
  calc
    p.eval (z * y) / p.eval z = (p.eval 0 * (A * B)) / (p.eval 0 * A) := by
      rw [hnum, hden']
    _ = B := by
      field_simp [ne_of_gt hzero, hA] <;> ring
    _ = ((jacobiPGF j h r).roots.map
        (fun x => jacobiTiltedRootPGFFactor z x y)).prod := by
      rfl

#print axioms splits_reverse_of_splits
#print axioms jacobiPGF_splits
#print axioms jacobiPGF_natDegree
#print axioms jacobiPGF_roots_card
#print axioms jacobiPGF_real_root_factorization
#print axioms splits_eq_eval_mul_rootNormalizedFactors
#print axioms jacobiPGF_root_normalized_factorization
#print axioms jacobiTiltedRootProbability_mem_Ioo
#print axioms jacobiPGF_tilted_bernoulli_pgF
#print axioms jacobiPGF_roots_negative

end ExactHoeffding
