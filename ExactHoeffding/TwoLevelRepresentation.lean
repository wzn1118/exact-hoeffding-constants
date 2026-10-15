import ExactHoeffding.FiniteExchangeability

namespace ExactHoeffding

/-- A centered vector taking two prescribed values has the exact standard
two-level parameterization with tilt equal to their difference. -/
theorem twoValue_zero_sum_representation {N : ℕ} (v : Fin N → ℝ) (α β : ℝ)
    (hN : 0 < N) (_hαβ : α ≠ β) (hvalues : ∀ i, v i = α ∨ v i = β)
    (hsum : ∑ i, v i = 0) :
    v = twoLevelVector (Finset.univ.filter (fun i => v i = α)) (α - β) := by
  classical
  let M := Finset.univ.filter (fun i => v i = α)
  have hpoint (i : Fin N) : v i = (if i ∈ M then α - β else 0) + β := by
    by_cases hi : v i = α
    · have hiM : i ∈ M := by simp [M, hi]
      rw [if_pos hiM, hi]
      ring
    · have hib : v i = β := (hvalues i).resolve_left hi
      have hiM : i ∉ M := by simp [M, hi]
      rw [if_neg hiM, hib, zero_add]
  have hsum' : (M.card : ℝ) * (α - β) + (N : ℝ) * β = 0 := by
    have h := congrArg (fun f : Fin N → ℝ => ∑ i, f i) (funext hpoint)
    rw [hsum] at h
    simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hβ : β = -(M.card : ℝ) * (α - β) / N := by
    apply (eq_div_iff hN').mpr
    nlinarith only [hsum']
  have hα : α = ((N : ℝ) - M.card) * (α - β) / N := by
    apply (eq_div_iff hN').mpr
    nlinarith only [hsum']
  funext i
  change v i = twoLevelVector M (α - β) i
  unfold twoLevelVector
  by_cases hi : v i = α
  · rw [if_pos (by simp [M, hi]), hi]
    exact hα
  · rw [if_neg (by simp [M, hi]), (hvalues i).resolve_left hi]
    exact hβ

/-- Nonzero zero-sum vectors with at most two values are represented by a
nonempty proper coordinate set and a nonzero tilt. -/
theorem atMostTwo_zero_sum_representation {N : ℕ} (v : Fin N → ℝ)
    (hN : 0 < N) (hsum : ∑ i, v i = 0) (hcard : (Finset.univ.image v).card ≤ 2) :
    v = 0 ∨ ∃ (M : Finset (Fin N)) (t : ℝ),
      0 < M.card ∧ M.card < N ∧ t ≠ 0 ∧ v = twoLevelVector M t := by
  classical
  by_cases hzero : v = 0
  · exact Or.inl hzero
  right
  have htwo : 1 < (Finset.univ.image v).card := by
    by_contra h
    have hle : (Finset.univ.image v).card ≤ 1 := le_of_not_gt h
    let i₀ : Fin N := ⟨0, hN⟩
    have hi₀ : v i₀ ∈ Finset.univ.image v := Finset.mem_image.mpr ⟨i₀, Finset.mem_univ _, rfl⟩
    have hconst : ∀ i, v i = v i₀ := by
      intro i
      exact Finset.card_le_one_iff.mp hle
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) hi₀
    have hsum' : (N : ℝ) * v i₀ = 0 := by
      simpa only [hconst, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] using hsum
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    have hc0 := (mul_eq_zero.mp hsum').resolve_left hN'
    apply hzero
    funext i
    exact (hconst i).trans hc0
  have hcard2 : (Finset.univ.image v).card = 2 := by omega
  obtain ⟨α, β, hαβ, himage⟩ := Finset.card_eq_two.mp hcard2
  have hvalues : ∀ i, v i = α ∨ v i = β := by
    intro i
    have hi : v i ∈ Finset.univ.image v := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [himage] at hi
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hi
  have hαmem : α ∈ Finset.univ.image v := by rw [himage]; simp
  have hβmem : β ∈ Finset.univ.image v := by rw [himage]; simp
  obtain ⟨iα, hiα, hvα⟩ := Finset.mem_image.mp hαmem
  obtain ⟨iβ, hiβ, hvβ⟩ := Finset.mem_image.mp hβmem
  let M := Finset.univ.filter (fun i => v i = α)
  have hMpos : 0 < M.card := Finset.card_pos.mpr ⟨iα, by simp [M, hvα]⟩
  have hiβM : iβ ∉ M := by simp [M, hvβ, hαβ.symm]
  have hMlt : M.card < N := by
    have hss : M ⊂ (Finset.univ : Finset (Fin N)) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, by
        intro heq
        apply hiβM
        rw [heq]
        exact Finset.mem_univ _⟩
    simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_lt_card hss
  exact ⟨M, α - β, hMpos, hMlt, sub_ne_zero.mpr hαβ,
    twoValue_zero_sum_representation v α β hN hαβ hvalues hsum⟩

end ExactHoeffding
