import ExactHoeffding.JacobiActualPGF
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ExactHoeffding

noncomputable def jacobiPGFODE (j h r : ℕ) : Polynomial ℝ :=
  Polynomial.X ^ 1 * (jacobiPGF j h r).derivative.derivative -
      Polynomial.X ^ 2 * (jacobiPGF j h r).derivative.derivative +
    Polynomial.C (r + 1 : ℝ) * (jacobiPGF j h r).derivative +
      Polynomial.C ((j : ℝ) + (j + h : ℝ) - 1) *
        (Polynomial.X ^ 1 * (jacobiPGF j h r).derivative) -
    Polynomial.C ((j : ℝ) * (j + h : ℝ)) * jacobiPGF j h r

theorem jacobiPGF_ode (j h r : ℕ) :
    jacobiPGFODE j h r = 0 := by
  classical
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp only [jacobiPGFODE, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.coeff_X_pow_mul', Polynomial.coeff_C_mul,
      Polynomial.coeff_derivative, Polynomial.coeff_zero,
      Nat.not_succ_le_zero, zero_add, add_zero, sub_zero, zero_mul,
      mul_zero, one_mul, mul_one]
    norm_num at ⊢
    by_cases hj : j = 0
    · subst j
      simp [jacobiPGF_coeff, jacobiCoeff]
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
      have hrec := jacobiCoeff_recurrence (j := j) (h := h) (r := r)
        (i := 0) hjpos
      simp only [jacobiPGF_coeff, if_pos (show 1 ≤ j by omega),
        if_pos (show 0 ≤ j by omega)]
      norm_num at hrec
      have hrecR :
          (jacobiCoeff j h r 1 : ℝ) * (r + 1) =
            (jacobiCoeff j h r 0 : ℝ) * j * (j + h) := by
        exact_mod_cast hrec
      linear_combination hrecR
  · by_cases hn1 : n = 1
    · subst n
      simp only [jacobiPGFODE, Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_X_pow_mul', Polynomial.coeff_C_mul,
        Polynomial.coeff_derivative, Polynomial.coeff_zero,
        Nat.not_succ_le_zero, zero_add, add_zero, sub_zero, zero_mul,
        mul_zero, one_mul, mul_one]
      norm_num at ⊢
      by_cases hj : 1 < j
      · have hjpos : 1 < j := hj
        have hrec := jacobiCoeff_recurrence (j := j) (h := h) (r := r)
          (i := 1) (by omega)
        simp only [jacobiPGF_coeff, if_pos (show 2 ≤ j by omega),
          if_pos (show 1 ≤ j by omega)]
        norm_num at hrec
        have hrecR :
            (jacobiCoeff j h r 2 : ℝ) * 2 * (r + 1 + 1) =
              (jacobiCoeff j h r 1 : ℝ) * ((j - 1 : ℕ) : ℝ) *
                ((j + h - 1 : ℕ) : ℝ) := by
          exact_mod_cast hrec
        have hjsub : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        have hjhsub : ((j + h - 1 : ℕ) : ℝ) = (j + h : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [hjsub, hjhsub] at hrecR
        linear_combination hrecR
      · by_cases hj0 : j = 0
        · subst j
          simp [jacobiPGF_coeff, jacobiCoeff]
        · have hj1 : j = 1 := by omega
          subst j
          simp [jacobiPGF_coeff, jacobiCoeff]
    · have hn2 : 2 ≤ n := by omega
      have hn1' : 1 ≤ n := by omega
      simp only [jacobiPGFODE, Polynomial.coeff_sub, Polynomial.coeff_add,
        Polynomial.coeff_X_pow_mul', Polynomial.coeff_C_mul,
        Polynomial.coeff_derivative, Polynomial.coeff_zero, hn0, hn1,
        show n - 1 + 1 = n by omega, show n - 2 + 1 = n - 1 by omega,
        show n - 2 + 1 + 1 = n by omega,
        if_pos hn2, if_pos hn1', zero_add, add_zero, sub_zero, zero_mul,
        mul_zero, one_mul, mul_one]
      have hzero (q : ℕ) (hq : j < q) :
          (jacobiPGF j h r).coeff q = 0 := by
        rw [jacobiPGF_coeff]
        simp [not_le_of_gt hq]
      by_cases hj : n < j
      · have hrec := jacobiCoeff_recurrence (j := j) (h := h) (r := r)
          (i := n) hj
        simp [jacobiPGF_coeff, show n + 1 ≤ j by omega,
          show n ≤ j by omega]
        have hsub1 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        have hsub2 : ((n - 2 : ℕ) : ℝ) + 1 = ((n - 1 : ℕ) : ℝ) := by
          exact_mod_cast (show n - 2 + 1 = n - 1 by omega)
        have hsub1' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        have hsub2' : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
          rw [Nat.cast_sub (by omega)]
          norm_num
        simp only [hsub1, hsub2, hsub1', hsub2']
        norm_num at hrec
        have hrecR :
            (jacobiCoeff j h r (n + 1) : ℝ) * (n + 1) * (r + n + 1) =
              (jacobiCoeff j h r n : ℝ) * ((j - n : ℕ) : ℝ) *
                ((j + h - n : ℕ) : ℝ) := by
          exact_mod_cast hrec
        have hjnsub : ((j - n : ℕ) : ℝ) = (j : ℝ) - n := by
          rw [Nat.cast_sub (Nat.le_of_lt hj)]
        have hjhnsub : ((j + h - n : ℕ) : ℝ) = (j + h : ℝ) - n := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [hjnsub, hjhnsub] at hrecR
        linear_combination hrecR
      · have hjge : j ≤ n := by omega
        by_cases hjeq : j = n
        · subst j
          have hsub1 : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
            rw [Nat.cast_sub (by omega)]
            norm_num
          have hsub2 : ((n - 2 : ℕ) : ℝ) + 1 = ((n - 1 : ℕ) : ℝ) := by
            exact_mod_cast (show n - 2 + 1 = n - 1 by omega)
          have hsub1' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)]
            norm_num
          have hsub2' : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
            rw [Nat.cast_sub (by omega)]
            norm_num
          simp only [hzero (n + 1) (by omega), jacobiPGF_coeff,
            if_pos (show n ≤ n by omega), if_false (show ¬n < n by omega),
            hsub1, hsub2, hsub1', hsub2']
          push_cast
          ring
        · have hjlt : j < n := by omega
          simp only [hzero (n + 1) (by omega), hzero n hjlt]
          simp

theorem jacobiPGF_derivative_ne_zero (j h r : ℕ) (hj : 0 < j) :
    (jacobiPGF j h r).derivative ≠ 0 := by
  apply Polynomial.derivative_ne_zero.mpr
  rw [jacobiPGF_natDegree]
  omega

private theorem jacobiPGF_root_coprime_coefficient (j h r : ℕ) {x : ℝ}
    (hx : x ∈ (jacobiPGF j h r).roots) :
    IsCoprime (Polynomial.X - Polynomial.C x)
      (Polynomial.X * (1 - Polynomial.X)) := by
  have hneg := jacobiPGF_roots_negative j h r hx
  have h0 : IsCoprime (Polynomial.X - Polynomial.C x)
      (Polynomial.X - Polynomial.C (0 : ℝ)) := by
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    exact isUnit_iff_ne_zero.mpr (by simpa using ne_of_lt hneg)
  have h1 : IsCoprime (Polynomial.X - Polynomial.C x)
      (Polynomial.X - Polynomial.C (1 : ℝ)) := by
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    exact isUnit_iff_ne_zero.mpr (by linarith)
  have hneg1 : IsCoprime (Polynomial.X - Polynomial.C x)
      (Polynomial.C 1 - Polynomial.X) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1.neg_right
  simpa [Polynomial.C_1] using h0.mul_right hneg1

theorem jacobiPGF_root_derivative_ne_zero (j h r : ℕ) {x : ℝ}
    (hx : x ∈ (jacobiPGF j h r).roots) :
    (jacobiPGF j h r).derivative.eval x ≠ 0 := by
  let p := jacobiPGF j h r
  let q : Polynomial ℝ := Polynomial.X - Polynomial.C x
  let m := p.rootMultiplicity x
  have hp : p ≠ 0 := jacobiPGF_ne_zero j h r
  have hroot : p.IsRoot x := Polynomial.isRoot_of_mem_roots hx
  have hmpos : 0 < m := (Polynomial.rootMultiplicity_pos hp).2 hroot
  have hjpos : 0 < j := by
    have hdeg : 0 < p.degree := Polynomial.degree_pos_of_root hp hroot
    have hnat : 0 < p.natDegree := Polynomial.natDegree_pos_iff_degree_pos.mpr hdeg
    simpa [p, jacobiPGF_natDegree] using hnat
  by_contra hderiv
  have hmul : 1 < m := by
    rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hp]
    exact ⟨hroot, hderiv⟩
  have hqpow : q ^ m ∣ p := by
    exact Polynomial.pow_rootMultiplicity_dvd p x
  have hqpow' : q ^ (m - 1) ∣ p.derivative := by
    simpa [q] using
      (Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd hqpow)
  have hqpow'' : q ^ (m - 2) ∣ p.derivative.derivative := by
    simpa [q] using
      (Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd
        (p := p) (q := q) 2 hqpow)
  have hqpow_p : q ^ (m - 1) ∣ p := by
    exact dvd_trans (pow_dvd_pow q (Nat.sub_le m 1)) hqpow
  have hode := congrArg (fun f : Polynomial ℝ => f.eval x)
    (jacobiPGF_ode j h r)
  have hqpow_A : q ^ (m - 1) ∣
      (Polynomial.X * (1 - Polynomial.X)) * p.derivative.derivative := by
    have hdiv : q ^ (m - 1) ∣
        (Polynomial.C ((j : ℝ) * (j + h : ℝ)) * p -
          (Polynomial.C (r + 1 : ℝ) +
            Polynomial.C ((j : ℝ) + (j + h : ℝ) - 1) * Polynomial.X) *
            p.derivative) := by
      apply dvd_sub
      · exact dvd_mul_of_dvd_right hqpow_p _
      · exact dvd_mul_of_dvd_right hqpow' _
    have hrewrite :
        (Polynomial.X * (1 - Polynomial.X)) * p.derivative.derivative =
          Polynomial.C ((j : ℝ) * (j + h : ℝ)) * p -
            (Polynomial.C (r + 1 : ℝ) +
              Polynomial.C ((j : ℝ) + (j + h : ℝ) - 1) * Polynomial.X) *
              p.derivative := by
      dsimp [p]
      have := jacobiPGF_ode j h r
      rw [jacobiPGFODE] at this
      linear_combination this
    rw [hrewrite]
    exact hdiv
  have hqpow_p'' : q ^ (m - 1) ∣ p.derivative.derivative := by
    apply (jacobiPGF_root_coprime_coefficient j h r hx).pow_left.dvd_of_dvd_mul_right
    simpa [mul_comm] using hqpow_A
  have hmult1 : p.derivative.rootMultiplicity x = m - 1 := by
    exact Polynomial.derivative_rootMultiplicity_of_root hroot
  have hroot1 : p.derivative.IsRoot x := by
    exact Polynomial.isRoot_of_mem_roots
      ((Polynomial.mem_roots (jacobiPGF_derivative_ne_zero j h r hjpos)).2 hderiv)
  have hmult2 : p.derivative.derivative.rootMultiplicity x = m - 2 := by
    rw [Polynomial.derivative_rootMultiplicity_of_root hroot1, hmult1]
    omega
  have hle : m - 1 ≤ p.derivative.derivative.rootMultiplicity x := by
    rw [Polynomial.le_rootMultiplicity_iff]
    · exact hqpow_p''
    · apply Polynomial.derivative_ne_zero.mpr
      have hmdeg : m ≤ j := by
        have hdeg := Polynomial.natDegree_le_of_dvd hqpow hp
        rw [(Polynomial.monic_X_sub_C x).natDegree_pow,
          Polynomial.natDegree_X_sub_C, jacobiPGF_natDegree] at hdeg
        simpa using hdeg
      rw [Polynomial.natDegree_derivative, jacobiPGF_natDegree]
      omega
  rw [hmult2] at hle
  omega

theorem jacobiPGF_roots_nodup (j h r : ℕ) :
    (jacobiPGF j h r).roots.Nodup := by
  classical
  apply Multiset.nodup_iff_count_le_one.mpr
  intro x
  by_cases hx : x ∈ (jacobiPGF j h r).roots
  · rw [Polynomial.count_roots]
    by_contra hm
    have hm' : 1 < Polynomial.rootMultiplicity x (jacobiPGF j h r) :=
      Nat.lt_of_not_ge hm
    have hroot : (jacobiPGF j h r).IsRoot x :=
      Polynomial.isRoot_of_mem_roots hx
    have hderiv : (jacobiPGF j h r).derivative.IsRoot x :=
      (Polynomial.one_lt_rootMultiplicity_iff_isRoot
        (jacobiPGF_ne_zero j h r)).mp hm' |>.2
    exact jacobiPGF_root_derivative_ne_zero j h r hx
      (by simpa [Polynomial.IsRoot] using hderiv)
  · simp [Multiset.count_eq_zero.mpr hx]

end ExactHoeffding
