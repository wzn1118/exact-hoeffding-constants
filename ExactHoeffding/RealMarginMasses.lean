import ExactHoeffding.RescaledFactorialFamily
import ExactHoeffding.TiltedVariance
import Mathlib.RingTheory.Binomial

/-!
# Positive normalized hypergeometric masses with real margins

The falling-factorial coefficients define a probability law whenever both
real margins exceed the last sampled index.  The normalization, ordinary
mean and adjacent recurrence are proved directly, before any optimization.
-/

namespace ExactHoeffding

noncomputable section

open Polynomial Finset

private theorem scaledFalling_smeval (a e : ℝ) (he : e ≠ 0) (q : ℕ) :
    scaledFalling a e q = e ^ q * (descPochhammer ℤ q).smeval (a / e) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [scaledFalling_succ, ih, descPochhammer_succ_right]
      simp only [smeval_mul, smeval_sub, smeval_X, smeval_natCast, pow_zero,
        nsmul_eq_mul, mul_one, pow_succ]
      field_simp

/-- Chu--Vandermonde for falling factorials with an arbitrary real step. -/
theorem scaledFalling_add (a b e : ℝ) (m : ℕ) :
    scaledFalling (a + b) e m =
      ∑ i ∈ range (m + 1), (m.choose i : ℝ) *
        (scaledFalling a e i * scaledFalling b e (m - i)) := by
  by_cases he : e = 0
  · subst e
    simpa [scaledFalling_step_zero, mul_comm, mul_left_comm, mul_assoc] using
      (add_pow a b m)
  · rw [scaledFalling_smeval (a + b) e he m, add_div]
    rw [Ring.descPochhammer_smeval_add m (Commute.all _ _)]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ m := by
      have := Finset.mem_range.mp hi
      omega
    rw [scaledFalling_smeval a e he i, scaledFalling_smeval b e he (m-i)]
    have hp : e ^ m = e ^ i * e ^ (m-i) := by
      rw [← pow_add, Nat.add_sub_of_le hi']
    rw [hp]
    ring

/-- The real-margin law, in probability/step coordinates. -/
def realMarginMass (m : ℕ) (e p : ℝ) (i : ℕ) : ℝ :=
  (m.choose i : ℝ) * scaledFalling p e i * scaledFalling (1-p) e (m-i) /
    scaledFalling 1 e m

/-- Normalization is an algebraic identity for every nonzero denominator. -/
theorem realMarginMass_sum (m : ℕ) (e p : ℝ)
    (hden : scaledFalling 1 e m ≠ 0) :
    ∑ i ∈ range (m+1), realMarginMass m e p i = 1 := by
  unfold realMarginMass
  rw [← Finset.sum_div]
  have h := scaledFalling_add p (1-p) e m
  simp only [add_sub_cancel] at h
  rw [show (∑ i ∈ range (m+1), (m.choose i : ℝ) * scaledFalling p e i *
    scaledFalling (1-p) e (m-i)) = scaledFalling 1 e m by
      simpa only [mul_assoc] using h.symm]
  exact div_self hden

/-- Removing the initial factor shifts the real success margin. -/
theorem scaledFalling_succ_left (a e : ℝ) (q : ℕ) :
    scaledFalling a e (q+1) = a * scaledFalling (a-e) e q := by
  induction q with
  | zero => simp [scaledFalling_succ]
  | succ q ih =>
      rw [scaledFalling_succ, ih, scaledFalling_succ]
      push_cast
      ring

/-- The first unnormalized moment is the success fraction times the
sampling size and the same common denominator. -/
theorem realMarginMass_first_numerator (m : ℕ) (e p : ℝ) :
    (∑ i ∈ range (m+1), (i:ℝ) * ((m.choose i : ℝ) *
      scaledFalling p e i * scaledFalling (1-p) e (m-i))) =
      (m:ℝ)*p*scaledFalling 1 e m := by
  cases m with
  | zero => simp
  | succ m =>
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hv := scaledFalling_add (p-e) (1-p) e m
    have heq : p-e+(1-p) = 1-e := by ring
    rw [heq] at hv
    rw [scaledFalling_succ_left, hv, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hsub : m+1-(i+1) = m-i := by omega
    rw [hsub, scaledFalling_succ_left]
    have hc : ((i:ℝ)+1) * ((m+1).choose (i+1) : ℝ) =
        ((m:ℝ)+1)*(m.choose i : ℝ) := by
      have h := congrArg (fun n:ℕ => (n:ℝ)) (Nat.add_one_mul_choose_eq m i)
      push_cast at h
      nlinarith
    push_cast
    calc
      _ = (((i:ℝ)+1) * ((m+1).choose (i+1) : ℝ)) *
          (p * scaledFalling (p-e) e i * scaledFalling (1-p) e (m-i)) := by ring
      _ = _ := by rw [hc]; ring

/-- The ordinary mean of the real-margin law is exactly `m*p`. -/
theorem realMarginMass_mean (m : ℕ) (e p : ℝ)
    (hden : scaledFalling 1 e m ≠ 0) :
    ∑ i ∈ range (m+1), (i:ℝ) * realMarginMass m e p i = (m:ℝ)*p := by
  simp only [realMarginMass, ← mul_div_assoc, ← Finset.sum_div]
  rw [realMarginMass_first_numerator]
  exact mul_div_cancel_right₀ _ hden

/-- Adjacent balance for the actual real-margin masses. -/
theorem realMarginMass_adjacent (m i : ℕ) (e p : ℝ) (hi : i < m) :
    ((i:ℝ)+1) * ((1-p)-((m:ℝ)-(i:ℝ)-1)*e) *
        realMarginMass m e p (i+1) =
      ((m:ℝ)-(i:ℝ)) * (p-(i:ℝ)*e) * realMarginMass m e p i := by
  have him : i ≤ m := Nat.le_of_lt hi
  have hs : m-(i+1)+1 = m-i := by omega
  have hs' : ((m-(i+1):ℕ):ℝ) = (m:ℝ)-(i:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : i+1 ≤ m)]
    push_cast
    ring
  have hc : ((i:ℝ)+1)*(m.choose (i+1):ℝ) =
      ((m:ℝ)-(i:ℝ))*(m.choose i:ℝ) := by
    have h := congrArg (fun n:ℕ => (n:ℝ)) (Nat.choose_succ_right_eq m i)
    push_cast [Nat.cast_sub him] at h
    nlinarith
  have hu : ((i:ℝ)+1) * ((1-p)-((m:ℝ)-(i:ℝ)-1)*e) *
        ((m.choose (i+1):ℝ)*scaledFalling p e (i+1)*scaledFalling (1-p) e (m-(i+1))) =
      ((m:ℝ)-(i:ℝ)) * (p-(i:ℝ)*e) *
        ((m.choose i:ℝ)*scaledFalling p e i*scaledFalling (1-p) e (m-i)) := by
    rw [← hs, scaledFalling_succ (1-p), scaledFalling_succ p, hs']
    calc
      _ = (((i:ℝ)+1)*(m.choose (i+1):ℝ)) *
          (((1-p)-((m:ℝ)-(i:ℝ)-1)*e)*scaledFalling p e i*
          (p-(i:ℝ)*e)*scaledFalling (1-p) e (m-(i+1))) := by ring
      _ = _ := by rw [hc]; ring
  simpa only [realMarginMass, mul_div_assoc] using
    congrArg (fun x:ℝ => x / scaledFalling 1 e m) hu

/-- The recurrence in real population/mark coordinates, without rounded margins. -/
theorem realMarginMass_population_adjacent (m i : ℕ) (N k : ℝ)
    (hN : N ≠ 0) (hi : i < m) :
    ((i:ℝ)+1) * ((i:ℝ)+1+(N-k-m)) *
        realMarginMass m (1/N) (k/N) (i+1) =
      (k-i) * ((m:ℝ)-i) * realMarginMass m (1/N) (k/N) i := by
  have h := realMarginMass_adjacent m i (1/N) (k/N) hi
  have hleft : (1-k/N)-((m:ℝ)-(i:ℝ)-1)*(1/N) =
      ((i:ℝ)+1+(N-k-m))/N := by field_simp; ring
  have hright : k/N-(i:ℝ)*(1/N) = (k-i)/N := by ring
  rw [hleft, hright] at h
  have hh := congrArg (fun x:ℝ => x*N) h
  field_simp [hN] at hh
  nlinarith [hh]

/-- Complementing the real success fraction reflects the finite support. -/
theorem realMarginMass_reflection (m i : ℕ) (e p : ℝ) (hi : i ≤ m) :
    realMarginMass m e (1-p) i = realMarginMass m e p (m-i) := by
  simp only [realMarginMass, sub_sub_cancel, Nat.sub_sub_self hi,
    Nat.choose_symm hi]
  ring

/-- Every mass is jointly analytic in the inverse population and success
fraction away from the common denominator's zeros. -/
theorem realMarginMass_joint_analytic (m i : ℕ) (z : ℝ × ℝ)
    (hz : scaledFalling 1 z.1 m ≠ 0) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => realMarginMass m u.1 u.2 i) z := by
  apply AnalyticAt.div _ (scaledFalling_joint_analytic m _ _ z
    analyticAt_const analyticAt_fst) hz
  apply AnalyticAt.mul
  · apply AnalyticAt.mul analyticAt_const
    exact scaledFalling_joint_analytic i _ _ z analyticAt_snd analyticAt_fst
  · exact scaledFalling_joint_analytic (m-i) _ _ z
      (analyticAt_const.sub analyticAt_snd) analyticAt_fst

/-- Every factor is positive in the stated real-parameter domain. -/
theorem scaledFalling_pos (a e : ℝ) (q : ℕ)
    (h : ∀ i < q, 0 < a - (i : ℝ)*e) : 0 < scaledFalling a e q := by
  unfold scaledFalling
  exact Finset.prod_pos (fun i hi => h i (Finset.mem_range.mp hi))

/-- Strict positivity of all masses on their full finite support. -/
theorem realMarginMass_pos (m : ℕ) (e p : ℝ)
    (hp : ∀ i < m, 0 < p - (i : ℝ)*e)
    (hq : ∀ i < m, 0 < (1-p) - (i : ℝ)*e)
    (hden : 0 < scaledFalling 1 e m) (i : ℕ) (hi : i ≤ m) :
    0 < realMarginMass m e p i := by
  unfold realMarginMass
  apply div_pos _ hden
  apply mul_pos
  · apply mul_pos
    · exact_mod_cast Nat.choose_pos hi
    · exact scaledFalling_pos p e i (fun j hj => hp j (by omega))
  · exact scaledFalling_pos (1-p) e (m-i) (fun j hj => hq j (by omega))

/-- A convenient strict rectangle around a balanced, real success margin. -/
theorem realMarginMass_pos_near_balanced (N m : ℕ) (hN : 0 < N)
    (hm : 2*m ≤ N) (d : ℝ) (hd : |d| < 1 / (N : ℝ))
    (i : ℕ) (hi : i ≤ m) :
    0 < realMarginMass m (1/(N:ℝ)) ((1-d)/2) i := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hmN : (2:ℝ)*m ≤ N := by exact_mod_cast hm
  have hdl : -(1/(N:ℝ)) < d := (abs_lt.mp hd).1
  have hdu : d < 1/(N:ℝ) := (abs_lt.mp hd).2
  have hfac : ∀ j < m, (j:ℝ)+1 ≤ m := by
    intro j hj
    exact_mod_cast hj
  have hp : ∀ j < m, 0 < (1-d)/2 - (j:ℝ)*(1/(N:ℝ)) := by
    intro j hj
    have hjr := hfac j hj
    have hmul : d*(N:ℝ) < 1 := (lt_div_iff₀ hNr).mp hdu
    have heq : (1-d)/2 - (j:ℝ)*(1/(N:ℝ)) =
        ((1-d)*(N:ℝ)-2*j)/(2*(N:ℝ)) := by field_simp
    rw [heq]
    exact div_pos (by nlinarith) (by positivity)
  have hq : ∀ j < m, 0 < (1-(1-d)/2) - (j:ℝ)*(1/(N:ℝ)) := by
    intro j hj
    have hjr := hfac j hj
    have hmul : -1 < d*(N:ℝ) := (div_lt_iff₀ hNr).mp (by simpa only [neg_div, one_div] using hdl)
    have heq : (1-(1-d)/2) - (j:ℝ)*(1/(N:ℝ)) =
        ((1+d)*(N:ℝ)-2*j)/(2*(N:ℝ)) := by field_simp; ring
    rw [heq]
    exact div_pos (by nlinarith) (by positivity)
  apply realMarginMass_pos m _ _ hp hq _ i hi
  apply scaledFalling_pos
  intro j hj
  have hjr := hfac j hj
  apply (mul_pos_iff_of_pos_right hNr).mp
  field_simp
  nlinarith

/-- The real-margin law has a strictly positive Laplace transform. -/
theorem realMarginMGF_pos (m : ℕ) (e p : ℝ)
    (hp : ∀ i < m, 0 < p - (i : ℝ)*e)
    (hq : ∀ i < m, 0 < (1-p) - (i : ℝ)*e)
    (hden : 0 < scaledFalling 1 e m) (t : ℝ) :
    0 < finiteMGF (range (m+1)) (realMarginMass m e p) (fun i => (i:ℝ)) t := by
  apply finiteMGF_pos_of_normalized
  · intro i hi
    exact (realMarginMass_pos m e p hp hq hden i (by
      have := Finset.mem_range.mp hi
      omega)).le
  · exact realMarginMass_sum m e p (ne_of_gt hden)

end
end ExactHoeffding
