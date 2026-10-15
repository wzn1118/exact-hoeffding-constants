import ExactHoeffding.Normalization

/-!
# Exact support and degenerate hypergeometric laws

The finite sum defining the hypergeometric law ranges over `0 ≤ i ≤ m`.
This qualification is essential for the current natural-number definition
of `hypergeomCount`: outside that range, `m - i` is truncated to zero.
All support statements below therefore use the actual summation domain
`i ≤ m`, and do not interpret the truncated coefficient outside that domain
as a probability mass.
-/

namespace ExactHoeffding

/-- The support predicate for the finite hypergeometric probability law. -/
def hypergeomSupport (N k m i : ℕ) : Prop :=
  i ≤ m ∧ hypergeomCount N k m i ≠ 0

/-- A totalized probability value.  The old `hypergeomMass` is retained for
the finite summation API; this wrapper assigns zero outside its valid draw
index range and therefore has the intended value on all of `ℕ`. -/
noncomputable def hypergeomPMFValue (N k m i : ℕ) : ℝ :=
  if i ≤ m then hypergeomMass N k m i else 0

/-- Inside the finite summation domain, the hypergeometric support is the
usual interval `[max 0 (m+k-N), min k m]`. -/
theorem hypergeomSupport_iff (N k m i : ℕ) (hk : k ≤ N) (_hm : m ≤ N) :
    hypergeomSupport N k m i ↔
      max 0 (m + k - N) ≤ i ∧ i ≤ min k m := by
  unfold hypergeomSupport
  constructor
  · rintro ⟨him, hcount⟩
    rw [hypergeomCount] at hcount
    have hki : Nat.choose k i ≠ 0 := by
      intro hzero
      apply hcount
      simp [hzero]
    have hmn : Nat.choose (N - k) (m - i) ≠ 0 := by
      intro hzero
      apply hcount
      simp [hzero]
    have hik : i ≤ k := (Nat.choose_ne_zero_iff).mp hki
    have hmnk : m - i ≤ N - k := (Nat.choose_ne_zero_iff).mp hmn
    have hlow : m + k - N ≤ i := by omega
    exact ⟨max_le (Nat.zero_le _) hlow, le_min hik him⟩
  · rintro ⟨hlow, hiupper⟩
    have hik : i ≤ k := hiupper.trans (min_le_left _ _)
    have him : i ≤ m := hiupper.trans (min_le_right _ _)
    have hmnk : m - i ≤ N - k := by omega
    exact ⟨him, Nat.mul_ne_zero
      ((Nat.choose_ne_zero_iff).2 hik)
      ((Nat.choose_ne_zero_iff).2 hmnk)⟩

/-- A support point has the expected lower and upper bounds. -/
theorem hypergeomSupport_bounds (N k m i : ℕ) (hk : k ≤ N) (hm : m ≤ N)
    (hi : hypergeomSupport N k m i) :
    max 0 (m + k - N) ≤ i ∧ i ≤ min k m :=
  (hypergeomSupport_iff N k m i hk hm).mp hi

/-- For valid parameters, division by the binomial denominator does not
create or remove a zero mass. -/
theorem hypergeomMass_ne_zero_iff (N k m i : ℕ) (hm : m ≤ N) :
    hypergeomMass N k m i ≠ 0 ↔ hypergeomCount N k m i ≠ 0 := by
  have hden : (Nat.choose N m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero hm
  constructor
  · intro hmass hcount
    apply hmass
    simp [hypergeomMass, hcount]
  · intro hcount
    apply div_ne_zero
    · exact_mod_cast hcount
    · exact hden

/-- The totalized PMF has exactly the finite hypergeometric support. -/
theorem hypergeomPMFValue_ne_zero_iff (N k m i : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomPMFValue N k m i ≠ 0 ↔
      max 0 (m + k - N) ≤ i ∧ i ≤ min k m := by
  by_cases him : i ≤ m
  · simp only [hypergeomPMFValue, if_pos him]
    rw [hypergeomMass_ne_zero_iff N k m i hm]
    constructor
    · intro hcount
      exact (hypergeomSupport_iff N k m i hk hm).mp ⟨him, hcount⟩
    · intro hbounds
      exact ((hypergeomSupport_iff N k m i hk hm).mpr hbounds).2
  · have hright : ¬(max 0 (m + k - N) ≤ i ∧ i ≤ min k m) := by
      omega
    simp [hypergeomPMFValue, him, hright]

/-- On the finite sampling range, totalization agrees term-by-term with the
original mass used by the existing normalization theorem. -/
theorem hypergeomPMFValue_sum_range_eq (N k m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), hypergeomPMFValue N k m i) =
      ∑ i ∈ Finset.range (m + 1), hypergeomMass N k m i := by
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  simp [hypergeomPMFValue, him]

/-- The totalized PMF normalizes on its finite effective range. -/
theorem hypergeomPMFValue_sum_range (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) :
    ∑ i ∈ Finset.range (m + 1), hypergeomPMFValue N k m i = 1 := by
  rw [hypergeomPMFValue_sum_range_eq]
  exact hypergeomMass_total N k m hk hm

/-- With no marked elements, the law is concentrated at zero. -/
theorem hypergeomMass_zero_marks (N m i : ℕ) (hm : m ≤ N) (hi : i ≤ m) :
    hypergeomMass N 0 m i = if i = 0 then 1 else 0 := by
  by_cases hzero : i = 0
  · subst hzero
    rw [if_pos rfl]
    simp [hypergeomMass, hypergeomCount, Nat.choose_ne_zero hm]
  · have hipos : 0 < i := Nat.pos_of_ne_zero hzero
    have hchoose : Nat.choose 0 i = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [if_neg hzero]
    simp [hypergeomMass, hypergeomCount, hchoose]

/-- With no draws, the law is concentrated at zero. -/
theorem hypergeomMass_zero_draws (N k : ℕ) :
    hypergeomMass N k 0 0 = 1 := by
  exact hypergeomMass_no_draws N k

/-- With every population element drawn, the count equals the number of
marked elements. -/
theorem hypergeomMass_full_draws (N k i : ℕ) (hk : k ≤ N) (hi : i ≤ N) :
    hypergeomMass N k N i = if i = k then 1 else 0 := by
  by_cases h : i = k
  · subst h
    simp [hypergeomMass, hypergeomCount]
  · have hsupport : ¬ hypergeomSupport N k N i := by
      intro hs
      have hbounds := hypergeomSupport_bounds N k N i hk le_rfl hs
      omega
    have hcount : hypergeomCount N k N i = 0 := by
      by_contra hcount
      exact hsupport ⟨hi, hcount⟩
    rw [if_neg h]
    simp [hypergeomMass, hcount]

/-- If every population element is marked, the count equals the sample size. -/
theorem hypergeomMass_full_marks (N m i : ℕ) (hm : m ≤ N) (hi : i ≤ m) :
    hypergeomMass N N m i = if i = m then 1 else 0 := by
  by_cases h : i = m
  · subst h
    have hden : Nat.choose N i ≠ 0 := Nat.choose_ne_zero hm
    simp [hypergeomMass, hypergeomCount, hden]
  · have hsupport : ¬ hypergeomSupport N N m i := by
      intro hs
      have hbounds := hypergeomSupport_bounds N N m i le_rfl hm hs
      omega
    have hcount : hypergeomCount N N m i = 0 := by
      by_contra hcount
      exact hsupport ⟨hi, hcount⟩
    rw [if_neg h]
    simp [hypergeomMass, hcount]

end ExactHoeffding
