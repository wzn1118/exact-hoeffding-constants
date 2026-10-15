import ExactHoeffding.JacobiRoots
import Mathlib.Algebra.Polynomial.Reverse
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace ExactHoeffding

/-- The Leibniz expansion of the endpoint-removed Rodrigues polynomial. -/
noncomputable def jacobiRodriguesExpansion (j h r : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (j + 1),
    Polynomial.C
      ((Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
        (Nat.descFactorial (r + j) k : ℝ)) *
      (Polynomial.X : Polynomial ℝ) ^ k *
      (Polynomial.X - Polynomial.C 1) ^ (j - k)

private theorem iterate_derivative_natDegree_eq (p : Polynomial ℝ) (n : ℕ) :
    (Polynomial.derivative^[n] p).natDegree = p.natDegree - n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', Polynomial.natDegree_derivative, ih]
      omega

private theorem jacobiRodriguesBase_natDegree (j h r : ℕ) :
    (jacobiRodriguesBase j h r).natDegree = h + r + 2 * j := by
  have hm₁ := (Polynomial.monic_X : (Polynomial.X : Polynomial ℝ).Monic).pow (h + j)
  have hm₂ := (Polynomial.monic_X_sub_C (1 : ℝ)).pow (r + j)
  have hmul := hm₁.natDegree_mul hm₂
  unfold jacobiRodriguesBase
  rw [hmul]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X,
    Polynomial.natDegree_X_sub_C, Nat.mul_one]
  omega

private theorem jacobiRodriguesEndpointFactor_natDegree (h r : ℕ) :
    (jacobiRodriguesEndpointFactor h r).natDegree = h + r := by
  have hm₁ := (Polynomial.monic_X : (Polynomial.X : Polynomial ℝ).Monic).pow h
  have hm₂ := (Polynomial.monic_X_sub_C (1 : ℝ)).pow r
  have hmul := hm₁.natDegree_mul hm₂
  unfold jacobiRodriguesEndpointFactor
  rw [hmul]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X,
    Polynomial.natDegree_X_sub_C, Nat.mul_one]

private theorem jacobiRodriguesRaw_natDegree (j h r : ℕ) :
    (jacobiRodriguesRaw j h r).natDegree = h + r + j := by
  rw [jacobiRodriguesRaw, iterate_derivative_natDegree_eq,
    jacobiRodriguesBase_natDegree]
  omega

theorem jacobiRodrigues_natDegree (j h r : ℕ) :
    (jacobiRodrigues j h r).natDegree = j := by
  have hraw := jacobiRodriguesRaw_natDegree j h r
  have hraw_ne : jacobiRodriguesRaw j h r ≠ 0 := by
    intro hz
    rw [hz] at hraw
    by_cases hzero : h + r + j = 0
    · have hj : j = 0 := by omega
      have hh : h = 0 := by omega
      have hr : r = 0 := by omega
      subst j
      subst h
      subst r
      simp [jacobiRodriguesRaw, jacobiRodriguesBase] at hz
    · have : 0 < h + r + j := Nat.pos_of_ne_zero hzero
      simp at hraw
      omega
  have hquot_ne : jacobiRodrigues j h r ≠ 0 := by
    intro hz
    have hf := jacobiRodrigues_factorization j h r
    rw [hz, mul_zero] at hf
    exact hraw_ne hf
  have hdeg := congrArg Polynomial.natDegree
    (jacobiRodrigues_factorization j h r)
  rw [(jacobiRodriguesEndpointFactor_monic h r).natDegree_mul' hquot_ne,
    jacobiRodriguesEndpointFactor_natDegree] at hdeg
  rw [hraw] at hdeg
  omega

private theorem jacobiRodriguesRaw_eq_endpoint_mul_expansion (j h r : ℕ) :
    jacobiRodriguesRaw j h r =
      jacobiRodriguesEndpointFactor h r * jacobiRodriguesExpansion j h r := by
  unfold jacobiRodriguesRaw jacobiRodriguesBase jacobiRodriguesEndpointFactor
    jacobiRodriguesExpansion
  rw [Polynomial.iterate_derivative_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk_le : k ≤ j := by
    simp only [Finset.mem_range] at hk
    omega
  have hexp₁ : h + j - (j - k) = h + k := by omega
  have hexp₂ : r + j - k = r + (j - k) := by omega
  rw [Polynomial.iterate_derivative_X_pow_eq_smul,
    Polynomial.iterate_derivative_X_sub_pow]
  simp only [Polynomial.smul_eq_C_mul, nsmul_eq_mul, ← Polynomial.C_eq_natCast,
    hexp₁, hexp₂, pow_add, Polynomial.C_mul]
  ring

theorem jacobiRodrigues_eq_expansion (j h r : ℕ) :
    jacobiRodrigues j h r = jacobiRodriguesExpansion j h r := by
  have hraw := jacobiRodriguesRaw_eq_endpoint_mul_expansion j h r
  have hfac := jacobiRodrigues_factorization j h r
  have hmul : jacobiRodriguesEndpointFactor h r * jacobiRodrigues j h r =
      jacobiRodriguesEndpointFactor h r * jacobiRodriguesExpansion j h r := by
    exact hfac.symm.trans hraw
  exact mul_left_cancel₀
    (jacobiRodriguesEndpointFactor_monic h r).ne_zero hmul

private theorem reflect_X_sub_one_pow (n : ℕ) :
    Polynomial.reflect n
      ((Polynomial.X - Polynomial.C (1 : ℝ) : Polynomial ℝ) ^ n) =
      (1 - Polynomial.X) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hdeg :
          ((Polynomial.X - Polynomial.C (1 : ℝ) : Polynomial ℝ) ^ n).natDegree ≤ n := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
        omega
      rw [pow_succ,
        Polynomial.reflect_mul
          (F := n) (G := 1)
          ((Polynomial.X - Polynomial.C (1 : ℝ) : Polynomial ℝ) ^ n)
          (Polynomial.X - Polynomial.C (1 : ℝ)) hdeg
          (Polynomial.natDegree_X_sub_C (1 : ℝ)).le]
      have hlinear :
          Polynomial.reflect 1
            (Polynomial.X - Polynomial.C (1 : ℝ) : Polynomial ℝ) =
          1 - Polynomial.X := by
        rw [sub_eq_add_neg, Polynomial.reflect_add, Polynomial.reflect_neg]
        simp [sub_eq_add_neg]
      rw [ih, hlinear, pow_succ]

private theorem reflect_sum {α : Type*} (N : ℕ) (s : Finset α)
    (f : α → Polynomial ℝ) :
    Polynomial.reflect N (∑ i ∈ s, f i) = ∑ i ∈ s, Polynomial.reflect N (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Polynomial.reflect_add, ih]

private theorem reflect_rodriguesTerm (j h r k : ℕ) (hk : k ≤ j) :
    Polynomial.reflect j
      (Polynomial.C
        ((Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
          (Nat.descFactorial (r + j) k : ℝ)) *
        (Polynomial.X : Polynomial ℝ) ^ k *
        (Polynomial.X - Polynomial.C 1) ^ (j - k)) =
      Polynomial.C
        ((Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
          (Nat.descFactorial (r + j) k : ℝ)) *
        (1 - Polynomial.X) ^ (j - k) := by
  let c : ℝ :=
    (Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
      (Nat.descFactorial (r + j) k : ℝ)
  have hsum : k + (j - k) = j := Nat.add_sub_of_le hk
  have hdeg₁ : ((Polynomial.X : Polynomial ℝ) ^ k).natDegree ≤ k := by simp
  have hdeg₂ :
      ((Polynomial.X - Polynomial.C (1 : ℝ) : Polynomial ℝ) ^ (j - k)).natDegree ≤
        j - k := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    omega
  have hmul := Polynomial.reflect_mul (F := k) (G := j - k)
    (f := (Polynomial.X : Polynomial ℝ) ^ k)
    (g := (Polynomial.X - Polynomial.C (1 : ℝ)) ^ (j - k)) hdeg₁ hdeg₂
  have hmul' :
      Polynomial.reflect j
        ((Polynomial.X : Polynomial ℝ) ^ k *
          (Polynomial.X - Polynomial.C (1 : ℝ)) ^ (j - k)) =
        Polynomial.reflect k (Polynomial.X ^ k) *
          Polynomial.reflect (j - k)
            ((Polynomial.X - Polynomial.C (1 : ℝ)) ^ (j - k)) := by
    simpa [hsum] using hmul
  calc
    Polynomial.reflect j
        (Polynomial.C c * (Polynomial.X : Polynomial ℝ) ^ k *
          (Polynomial.X - Polynomial.C 1) ^ (j - k)) =
        Polynomial.reflect j
          (Polynomial.C c * ((Polynomial.X : Polynomial ℝ) ^ k *
            (Polynomial.X - Polynomial.C 1) ^ (j - k))) := by
              rw [mul_assoc]
    _ = Polynomial.C c *
          (Polynomial.reflect k (Polynomial.X ^ k) *
            Polynomial.reflect (j - k)
              ((Polynomial.X - Polynomial.C 1) ^ (j - k))) := by
            rw [Polynomial.reflect_C_mul, hmul']
    _ = Polynomial.C c * (1 - Polynomial.X) ^ (j - k) := by
          rw [reflect_X_sub_one_pow]
          simp

private theorem jacobiRodrigues_reflect_expansion (j h r : ℕ) :
    Polynomial.reflect j (jacobiRodrigues j h r) =
      ∑ k ∈ Finset.range (j + 1),
        Polynomial.C
          ((Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
            (Nat.descFactorial (r + j) k : ℝ)) *
          (1 - Polynomial.X) ^ (j - k) := by
  classical
  rw [jacobiRodrigues_eq_expansion]
  unfold jacobiRodriguesExpansion
  rw [reflect_sum]
  apply Finset.sum_congr rfl
  intro k hk
  exact reflect_rodriguesTerm j h r k (by
    simp only [Finset.mem_range] at hk
    omega)

private theorem jacobiRodriguesReflect_comp (j h r : ℕ) :
    (∑ k ∈ Finset.range (j + 1),
      Polynomial.C
        ((Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
          (Nat.descFactorial (r + j) k : ℝ)) *
        (1 - Polynomial.X) ^ (j - k)).comp
        (Polynomial.C 1 - Polynomial.X) =
      ∑ k ∈ Finset.range (j + 1),
        Polynomial.C
          ((Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
            (Nat.descFactorial (r + j) k : ℝ)) *
          (Polynomial.X : Polynomial ℝ) ^ (j - k) := by
  rw [Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro k hk
  have hsub : (1 - Polynomial.X : Polynomial ℝ).comp
      (Polynomial.C 1 - Polynomial.X) = Polynomial.X := by
    calc
      (1 - Polynomial.X : Polynomial ℝ).comp
          (Polynomial.C 1 - Polynomial.X) =
        (1 : Polynomial ℝ).comp (Polynomial.C 1 - Polynomial.X) -
          Polynomial.X.comp (Polynomial.C 1 - Polynomial.X) := Polynomial.sub_comp
      _ = 1 - (Polynomial.C 1 - Polynomial.X) := by simp
      _ = Polynomial.X := by rw [Polynomial.C_1]; ring
  rw [Polynomial.C_mul_comp, Polynomial.pow_comp, hsub]

theorem jacobiPGF_eq_rodrigues_mobius (j h r : ℕ) :
    jacobiPGF j h r =
      (jacobiRodrigues j h r).reverse.comp
        (Polynomial.C 1 - Polynomial.X) := by
  classical
  have hrev :
      (jacobiRodrigues j h r).reverse.comp (Polynomial.C 1 - Polynomial.X) =
        ∑ k ∈ Finset.range (j + 1),
          Polynomial.C
            ((Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
            (Nat.descFactorial (r + j) k : ℝ)) *
            (Polynomial.X : Polynomial ℝ) ^ (j - k) := by
    change (Polynomial.reflect (jacobiRodrigues j h r).natDegree
      (jacobiRodrigues j h r)).comp (Polynomial.C 1 - Polynomial.X) = _
    rw [jacobiRodrigues_natDegree, jacobiRodrigues_reflect_expansion,
      jacobiRodriguesReflect_comp]
  have hbij :
      ∑ k ∈ Finset.range (j + 1),
        Polynomial.C
          ((Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
            (Nat.descFactorial (r + j) k : ℝ)) *
          (Polynomial.X : Polynomial ℝ) ^ (j - k) =
      ∑ i ∈ Finset.range (j + 1),
        Polynomial.C ((jacobiCoeff j h r i : ℝ)) *
          (Polynomial.X : Polynomial ℝ) ^ i := by
    refine Finset.sum_bij'
      (f := fun k : ℕ =>
        Polynomial.C
          ((Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
            (Nat.descFactorial (r + j) k : ℝ)) *
          (Polynomial.X : Polynomial ℝ) ^ (j - k))
      (g := fun i : ℕ =>
        Polynomial.C ((jacobiCoeff j h r i : ℝ)) *
          (Polynomial.X : Polynomial ℝ) ^ i)
      (s := Finset.range (j + 1)) (t := Finset.range (j + 1))
      (fun k _ => j - k) (fun i _ => j - i)
      (by intro k hk; simp only [Finset.mem_range] at hk ⊢; omega)
      (by intro i hi; simp only [Finset.mem_range] at hi ⊢; omega)
      (by intro k hk; simp only [Finset.mem_range] at hk; omega)
      (by intro i hi; simp only [Finset.mem_range] at hi; omega) ?_
    intro k hk
    have hk_le : k ≤ j := by
      simp only [Finset.mem_range] at hk
      omega
    simp [jacobiCoeff, Nat.choose_symm hk_le, Nat.add_comm h j, Nat.sub_sub_self hk_le]
  calc
    jacobiPGF j h r =
        ∑ i ∈ Finset.range (j + 1),
          Polynomial.C ((jacobiCoeff j h r i : ℝ)) *
            (Polynomial.X : Polynomial ℝ) ^ i := by
          simp [jacobiPGF, ← Polynomial.C_mul_X_pow_eq_monomial]
    _ = ∑ k ∈ Finset.range (j + 1),
          Polynomial.C
            ((Nat.choose j k : ℝ) * (Nat.descFactorial (h + j) (j - k) : ℝ) *
              (Nat.descFactorial (r + j) k : ℝ)) *
            (Polynomial.X : Polynomial ℝ) ^ (j - k) := hbij.symm
    _ = (jacobiRodrigues j h r).reverse.comp
          (Polynomial.C 1 - Polynomial.X) := hrev.symm

#print axioms jacobiRodrigues_eq_expansion
#print axioms jacobiRodrigues_natDegree
#print axioms jacobiPGF_eq_rodrigues_mobius

end ExactHoeffding
