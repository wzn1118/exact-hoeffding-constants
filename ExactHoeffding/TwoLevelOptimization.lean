import ExactHoeffding.ThreePointExclusion
import ExactHoeffding.SliceExponentialAlgebra

/-!
# Excluding an ordered distinct triple at a genuine finite-dimensional maximum
-/

namespace ExactHoeffding

def replaceThree {α : Type*} [DecidableEq α] (y : α → ℝ)
    (a b c : α) (x₁ x₂ x₃ : ℝ) : α → ℝ :=
  fun i => if i = a then x₁ else if i = b then x₂ else if i = c then x₃ else y i

theorem sliceExponential_no_ordered_triple_max {α : Type*} [DecidableEq α]
    (T : Finset α) (y : α → ℝ) (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∉ T) (hb : b ∉ T) (hc : c ∉ T)
    (k : ℕ) (hk0 : 0 < k) (hk : k ≤ T.card + 2)
    (hyab : y a < y b) (hybc : y b < y c)
    (hmax : ∀ v : α → ℝ,
      (∑ i ∈ insert a (insert b (insert c T)), v i) =
        ∑ i ∈ insert a (insert b (insert c T)), y i →
      (∑ i ∈ insert a (insert b (insert c T)), (v i) ^ 2) =
        ∑ i ∈ insert a (insert b (insert c T)), (y i) ^ 2 →
      sliceExponential (insert a (insert b (insert c T))) v k ≤
        sliceExponential (insert a (insert b (insert c T))) y k) : False := by
  let A := sliceExponential T y ((k : ℤ) - 1)
  let B := Real.exp (y a + y b + y c) * sliceExponential T y ((k : ℤ) - 2)
  have hA : 0 ≤ A := sliceExponential_nonneg _ _ _
  have hB : 0 ≤ B := mul_nonneg (Real.exp_pos _).le (sliceExponential_nonneg _ _ _)
  have hAB : 0 < A + B := sliceExponential_two_coefficients_pos T y k hk0 hk _
  apply pairedExponential_no_three_distinct_max A B (y a) (y b) (y c) hA hB hAB hyab hybc
  intro x₁ x₂ x₃ hsum hsq
  let v := replaceThree y a b c x₁ x₂ x₃
  have hva : v a = x₁ := by simp [v, replaceThree]
  have hvb : v b = x₂ := by simp [v, replaceThree, hab.symm]
  have hvc : v c = x₃ := by simp [v, replaceThree, hac.symm, hbc.symm]
  have hvT : ∀ i ∈ T, v i = y i := by
    intro i hi
    have hia : i ≠ a := fun h => ha (h ▸ hi)
    have hib : i ≠ b := fun h => hb (h ▸ hi)
    have hic : i ≠ c := fun h => hc (h ▸ hi)
    simp [v, replaceThree, hia, hib, hic]
  have ha' : a ∉ insert b (insert c T) := by simp [hab, hac, ha]
  have hb' : b ∉ insert c T := by simp [hbc, hb]
  have hsum' : (∑ i ∈ insert a (insert b (insert c T)), v i) =
      ∑ i ∈ insert a (insert b (insert c T)), y i := by
    simp only [Finset.sum_insert ha', Finset.sum_insert hb', Finset.sum_insert hc, hva, hvb, hvc]
    rw [Finset.sum_congr rfl hvT]
    linarith
  have hsq' : (∑ i ∈ insert a (insert b (insert c T)), (v i) ^ 2) =
      ∑ i ∈ insert a (insert b (insert c T)), (y i) ^ 2 := by
    simp only [Finset.sum_insert ha', Finset.sum_insert hb', Finset.sum_insert hc, hva, hvb, hvc]
    rw [Finset.sum_congr rfl (fun i hi => congrArg (fun x : ℝ => x ^ 2) (hvT i hi))]
    linarith
  have hvmax := hmax v hsum' hsq'
  rw [sliceExponential_three_insert T v k a b c hab hac hbc ha hb hc,
    sliceExponential_three_insert T y k a b c hab hac hbc ha hb hc] at hvmax
  simp only [hva, hvb, hvc] at hvmax
  have heq (l : ℤ) : sliceExponential T v l = sliceExponential T y l :=
    sliceExponential_congr T v y l hvT
  simp only [heq] at hvmax
  have hpair (u₁ u₂ u₃ : ℝ) :
      Real.exp u₁ * Real.exp u₂ + Real.exp u₁ * Real.exp u₃ + Real.exp u₂ * Real.exp u₃ =
      Real.exp (u₁ + u₂ + u₃) * (Real.exp (-u₁) + Real.exp (-u₂) + Real.exp (-u₃)) := by
    have h₁ : Real.exp (u₁ + u₂ + u₃) * Real.exp (-u₁) = Real.exp u₂ * Real.exp u₃ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have h₂ : Real.exp (u₁ + u₂ + u₃) * Real.exp (-u₂) = Real.exp u₁ * Real.exp u₃ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have h₃ : Real.exp (u₁ + u₂ + u₃) * Real.exp (-u₃) = Real.exp u₁ * Real.exp u₂ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [mul_add, mul_add, h₁, h₂, h₃]
    ring
  have htriple (u₁ u₂ u₃ : ℝ) : Real.exp u₁ * Real.exp u₂ * Real.exp u₃ =
      Real.exp (u₁ + u₂ + u₃) := by rw [← Real.exp_add, ← Real.exp_add]
  have hprod (D u₁ u₂ u₃ : ℝ) :
      D * Real.exp u₁ * Real.exp u₂ * Real.exp u₃ = D * Real.exp (u₁ + u₂ + u₃) := by
    calc
      _ = D * (Real.exp u₁ * Real.exp u₂ * Real.exp u₃) := by ring
      _ = _ := by rw [htriple]
  rw [hpair x₁ x₂ x₃, hpair (y a) (y b) (y c),
    hprod _ x₁ x₂ x₃, hprod _ (y a) (y b) (y c), hsum] at hvmax
  unfold pairedExponential
  dsimp [A, B]
  nlinarith only [hvmax]

private theorem ordered_triple_of_distinct_values {α : Type*} (y : α → ℝ)
    (a b c : α) (hab : y a ≠ y b) (hac : y a ≠ y c) (hbc : y b ≠ y c) :
    ∃ p q r : α, y p < y q ∧ y q < y r := by
  rcases lt_or_gt_of_ne hab with hab | hab
  · rcases lt_or_gt_of_ne hbc with hbc | hbc
    · exact ⟨a, b, c, hab, hbc⟩
    · rcases lt_or_gt_of_ne hac with hac | hac
      · exact ⟨a, c, b, hac, hbc⟩
      · exact ⟨c, a, b, hac, hab⟩
  · rcases lt_or_gt_of_ne hac with hac | hac
    · exact ⟨b, a, c, hab, hac⟩
    · rcases lt_or_gt_of_ne hbc with hbc | hbc
      · exact ⟨b, c, a, hbc, hac⟩
      · exact ⟨c, b, a, hbc, hab⟩

/-- Every genuine maximizer of the finite subset exponential sum under fixed
sum and squared norm has at most two distinct coordinate values. -/
theorem sliceExponential_maximizer_at_most_two (N k : ℕ) (hk0 : 0 < k) (hkN : k < N)
    (y : Fin N → ℝ)
    (hmax : ∀ v : Fin N → ℝ, (∑ i, v i) = ∑ i, y i →
      (∑ i, (v i) ^ 2) = ∑ i, (y i) ^ 2 →
      sliceExponential Finset.univ v k ≤ sliceExponential Finset.univ y k) :
    (Finset.univ.image y).card ≤ 2 := by
  classical
  by_contra hcard
  obtain ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, h₁₂, h₁₃, h₂₃⟩ :=
    Finset.two_lt_card.mp (lt_of_not_ge hcard)
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx₁
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx₂
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx₃
  obtain ⟨p, q, r, hpq, hqr⟩ := ordered_triple_of_distinct_values y a b c h₁₂ h₁₃ h₂₃
  have hpq' : p ≠ q := fun h => hpq.ne (congrArg y h)
  have hpr' : p ≠ r := fun h => (hpq.trans hqr).ne (congrArg y h)
  have hqr' : q ≠ r := fun h => hqr.ne (congrArg y h)
  let T := (((Finset.univ : Finset (Fin N)).erase p).erase q).erase r
  have hpT : p ∉ T := by simp [T, hpq', hpr']
  have hqT : q ∉ T := by simp [T, hqr']
  have hrT : r ∉ T := by simp [T]
  have huniv : insert p (insert q (insert r T)) = (Finset.univ : Finset (Fin N)) := by
    ext i
    simp only [T, Finset.mem_insert, Finset.mem_erase, Finset.mem_univ, and_true, iff_true]
    by_cases hip : i = p
    · exact Or.inl hip
    · by_cases hiq : i = q
      · exact Or.inr (Or.inl hiq)
      · by_cases hir : i = r
        · exact Or.inr (Or.inr (Or.inl hir))
        · exact Or.inr (Or.inr (Or.inr ⟨hir, hiq, hip⟩))
  have hsize : T.card + 3 = N := by
    have hcount := congrArg Finset.card huniv
    have hp' : p ∉ insert q (insert r T) := by simp [hpq', hpr', hpT]
    have hq' : q ∉ insert r T := by simp [hqr', hqT]
    rw [Finset.card_insert_of_notMem hp', Finset.card_insert_of_notMem hq',
      Finset.card_insert_of_notMem hrT, Finset.card_univ, Fintype.card_fin] at hcount
    omega
  apply sliceExponential_no_ordered_triple_max T y p q r hpq' hpr' hqr' hpT hqT hrT
    k hk0 (by omega) hpq hqr
  intro v hvsum hvsq
  rw [huniv] at hvsum hvsq ⊢
  exact hmax v hvsum hvsq

end ExactHoeffding
