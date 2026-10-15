import ExactHoeffding.RealMarginMasses
import ExactHoeffding.SmallSupportCurvature
import ExactHoeffding.SmallSupportEquality
import ExactHoeffding.BernoulliProxy

/-! # Physical and small-support bridges for real success margins -/

namespace ExactHoeffding

noncomputable section

open Finset

/-- At physical parameters the real law agrees with every hypergeometric
mass, including masses which vanish on a restricted physical support. -/
theorem realMarginMass_hypergeom (N k m i : ℕ) (hN : 0 < N)
    (hk : k ≤ N) (hm : m ≤ N) (hi : i ≤ m) :
    realMarginMass m (1/(N:ℝ)) ((k:ℝ)/N) i = hypergeomMass N k m i := by
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hcomp : 1-(k:ℝ)/N = ((N-k:ℕ):ℝ)/N := by
    rw [Nat.cast_sub hk]
    field_simp
  have hden : scaledFalling 1 (1/(N:ℝ)) m =
      (Nat.descFactorial N m:ℝ)/(N:ℝ)^m := by
    simpa only [div_self hNr] using scaledFalling_div_nat_all N N m
  have hpow : (N:ℝ)^m = (N:ℝ)^i*(N:ℝ)^(m-i) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  have hfact : (m.choose i:ℝ)*(i.factorial:ℝ)*((m-i).factorial:ℝ) =
      (m.factorial:ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hf0 : (m.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hc0 : (N.choose m:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hm)
  simp only [realMarginMass, hcomp, scaledFalling_div_nat_all, hden,
    hypergeomMass, hypergeomCount, Nat.cast_mul]
  rw [Nat.descFactorial_eq_factorial_mul_choose k i,
    Nat.descFactorial_eq_factorial_mul_choose (N-k) (m-i),
    Nat.descFactorial_eq_factorial_mul_choose N m]
  push_cast
  rw [hpow]
  field_simp [hNr, hf0, hc0]
  linear_combination (k.choose i:ℝ)*((N-k).choose (m-i):ℝ)*hfact

@[simp] theorem realMarginMass_one_zero (e p : ℝ) :
    realMarginMass 1 e p 0 = 1-p := by
  simp [realMarginMass, scaledFalling_succ]

@[simp] theorem realMarginMass_one_one (e p : ℝ) :
    realMarginMass 1 e p 1 = p := by
  simp [realMarginMass, scaledFalling_succ]

/-- One draw of the real-margin law is precisely Bernoulli. -/
theorem realMarginMGF_one (e p t : ℝ) :
    finiteMGF (range 2) (realMarginMass 1 e p) (fun i => (i:ℝ)) t =
      1-p+p*Real.exp t := by
  simp [finiteMGF, Finset.sum_range_succ]

theorem realMarginCenteredLogMGF_one (e p t : ℝ) :
    Real.log (finiteMGF (range 2) (realMarginMass 1 e p) (fun i => (i:ℝ)) t) - p*t =
      bernoulliCenteredLogMGF p t := by
  rw [realMarginMGF_one]
  rfl

@[simp] theorem realMarginMass_two_zero (e p : ℝ) :
    realMarginMass 2 e p 0 = (1-p)*(1-p-e)/(1-e) := by
  simp [realMarginMass, scaledFalling_succ]

@[simp] theorem realMarginMass_two_one (e p : ℝ) :
    realMarginMass 2 e p 1 = 2*p*(1-p)/(1-e) := by
  simp [realMarginMass, scaledFalling_succ]

@[simp] theorem realMarginMass_two_two (e p : ℝ) :
    realMarginMass 2 e p 2 = p*(p-e)/(1-e) := by
  simp [realMarginMass, scaledFalling_succ]

/-- Actual two-draw curvature equals the three-point rational expression
for real population and real success count. -/
theorem realMargin_two_curvature_formula (N k t : ℝ) (hN : 2 < N)
    (hk : 2 ≤ k) (hq : k+2 ≤ N) :
    deriv (deriv (fun u => Real.log (finiteMGF (range 3)
      (realMarginMass 2 (1/N) (k/N)) (fun i => (i:ℝ)) u))) t =
      threePointVariance ((N-k)*(N-k-1)) (k*(N-k)) (k*(k-1)) (Real.exp t) := by
  have hNr : 0 < N := by linarith
  have hden : 0 < scaledFalling 1 (1/N) 2 := by
    simp only [scaledFalling_succ, scaledFalling_zero, Nat.cast_one, Nat.cast_zero,
      zero_mul, sub_zero, one_mul]
    exact sub_pos.mpr ((div_lt_one hNr).mpr (by linarith))
  have hp : ∀ i : ℕ, i < 2 → 0 < k/N-(i:ℝ)*(1/N) := by
    intro i hi
    have hir : (i:ℝ) < 2 := by exact_mod_cast hi
    have heq : k/N-(i:ℝ)*(1/N) = (k-i)/N := by ring
    rw [heq]
    exact div_pos (by linarith) hNr
  have hq' : ∀ i : ℕ, i < 2 → 0 < (1-k/N)-(i:ℝ)*(1/N) := by
    intro i hi
    have hir : (i:ℝ) < 2 := by exact_mod_cast hi
    have heq : (1-k/N)-(i:ℝ)*(1/N) = (N-k-i)/N := by field_simp
    rw [heq]
    exact div_pos (by linarith) hNr
  rw [finiteLogMGF_second_deriv (range 3) _ _
    (fun i hi => (realMarginMass_pos 2 _ _ hp hq' hden i (by
      have := Finset.mem_range.mp hi; omega)).le)
    (realMarginMass_sum 2 _ _ hden.ne') t]
  simp only [finiteMGF, finiteTiltFirst, finiteTiltSecond, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, mul_one,
    zero_pow, one_pow, Real.exp_zero, zero_mul, zero_add, one_mul, add_zero]
  rw [realMarginMass_two_zero, realMarginMass_two_one, realMarginMass_two_two]
  rw [show t*2=t+t by ring, Real.exp_add]
  unfold threePointVariance
  field_simp [show N-1 ≠ 0 by linarith]

end
end ExactHoeffding
