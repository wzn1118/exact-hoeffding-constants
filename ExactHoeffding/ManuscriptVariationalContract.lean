import ExactHoeffding.VariationalIdentity
import Mathlib.Order.ConditionallyCompleteLattice.Finset

namespace ExactHoeffding
noncomputable section

/-- The inner supremum in the displayed Lee--Kim identity, with the paper's
centered hypergeometric log-Laplace transform. -/
def manuscriptTiltQuotientSup (N k m : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ t : ℝ, t ≠ 0 ∧
    v = hypergeomCenteredLogMGF N k m t / t ^ 2}

/-- The displayed term `8N/[m(N-m)] sup_{t ≠ 0} ψ(t)/t²`. -/
def manuscriptVariationalTerm (N k m : ℕ) : ℝ :=
  (8 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) *
    manuscriptTiltQuotientSup N k m

/-- The finite maximum over `1 ≤ k,m < N`, represented by the nonempty
finite index set `Fin (N-1) × Fin (N-1)`. -/
def manuscriptVariationalMaximum (N : ℕ) (hN : 2 ≤ N) : ℝ :=
  (Finset.univ : Finset (Fin (N - 1) × Fin (N - 1))).sup'
    (by
      refine ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), Finset.mem_univ _⟩)
    (fun p : Fin (N - 1) × Fin (N - 1) =>
      manuscriptVariationalTerm N (p.1.val + 1) (p.2.val + 1))

private theorem optimalProxy_eq_twice_tiltQuotientSup
    (ψ : ℝ → ℝ) (hQ : BddAbove {v : ℝ | ∃ t : ℝ, t ≠ 0 ∧
      v = ψ t / t ^ 2}) :
    optimalProxy ψ = 2 * sSup {v : ℝ | ∃ t : ℝ, t ≠ 0 ∧
      v = ψ t / t ^ 2} := by
  let Q : Set ℝ := {v : ℝ | ∃ t : ℝ, t ≠ 0 ∧ v = ψ t / t ^ 2}
  let P : Set ℝ := {v : ℝ | ∃ t : ℝ, t ≠ 0 ∧ v = 2 * ψ t / t ^ 2}
  have hQne : Q.Nonempty := by
    exact ⟨ψ 1 / 1 ^ 2, 1, by norm_num, rfl⟩
  have hPne : P.Nonempty := by
    exact ⟨2 * ψ 1 / 1 ^ 2, 1, by norm_num, rfl⟩
  have hPupper : ∀ a ∈ P, a ≤ 2 * sSup Q := by
    rintro a ⟨t, ht, rfl⟩
    have hq : ψ t / t ^ 2 ∈ Q := ⟨t, ht, rfl⟩
    have h := le_csSup hQ hq
    calc
      2 * ψ t / t ^ 2 = 2 * (ψ t / t ^ 2) := by ring
      _ ≤ 2 * sSup Q := mul_le_mul_of_nonneg_left h (by norm_num)
  have hPapprox : ∀ w, w < 2 * sSup Q → ∃ a ∈ P, w < a := by
    intro w hw
    have hw' : w / 2 < sSup Q := by nlinarith only [hw]
    obtain ⟨q, hq, hqgt⟩ := exists_lt_of_lt_csSup hQne hw'
    rcases hq with ⟨t, ht, hqeq⟩
    refine ⟨2 * (ψ t / t ^ 2), ⟨t, ht, by ring⟩, ?_⟩
    rw [hqeq] at hqgt
    nlinarith only [hqgt]
  have hscaled : sSup P = 2 * sSup Q :=
    csSup_eq_of_forall_le_of_forall_lt_exists_gt hPne hPupper hPapprox
  unfold optimalProxy
  change sSup P = 2 * sSup Q
  exact hscaled

private theorem hypergeomTiltQuotient_bddAbove
    (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) :
    BddAbove {v : ℝ | ∃ t : ℝ, t ≠ 0 ∧
      v = hypergeomCenteredLogMGF N k m t / t ^ 2} := by
  refine ⟨sharpCurvatureConstant N k m / 2, ?_⟩
  rintro v ⟨t, ht, rfl⟩
  have h := hypergeom_uniform_log_laplace_domination N k m hk hm t
  apply (div_le_iff₀ (sq_pos_of_ne_zero ht)).2
  nlinarith only [h]

private theorem hypergeomOptimalProxy_eq_twice_tiltQuotientSup
    (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) :
    hypergeomOptimalProxy N k m = 2 * manuscriptTiltQuotientSup N k m := by
  unfold manuscriptTiltQuotientSup hypergeomOptimalProxy
  exact optimalProxy_eq_twice_tiltQuotientSup _
    (hypergeomTiltQuotient_bddAbove N k m hk hm)

private theorem manuscriptVariationalTerm_eq_normalizedProxy
    (N k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) :
    manuscriptVariationalTerm N k m = normalizedHypergeomProxy N k m := by
  change (8 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m))) *
      manuscriptTiltQuotientSup N k m =
    4 * (N : ℝ) / ((m : ℝ) * ((N : ℝ) - m)) * hypergeomOptimalProxy N k m
  rw [hypergeomOptimalProxy_eq_twice_tiltQuotientSup N k m hk hm]
  ring

private theorem hypergeomVariationalConstant_eq_manuscript_maximum
    (N : ℕ) (hN : 2 ≤ N) :
    hypergeomVariationalConstant N = manuscriptVariationalMaximum N hN := by
  let I := Fin (N - 1) × Fin (N - 1)
  let f : I → ℝ := fun p =>
    manuscriptVariationalTerm N (p.1.val + 1) (p.2.val + 1)
  have hne : (Finset.univ : Finset I).Nonempty :=
    ⟨(⟨0, by omega⟩, ⟨0, by omega⟩), Finset.mem_univ _⟩
  have himage : f '' (Finset.univ : Finset I) =
      {v : ℝ | ∃ k m : ℕ, 0 < k ∧ k < N ∧
        0 < m ∧ m < N ∧ v = normalizedHypergeomProxy N k m} := by
    ext v
    constructor
    · simp only [Set.mem_image]
      rintro ⟨p, hp, hEq⟩
      have : p ∈ (Finset.univ : Finset I) := hp
      simp at this
      rcases p with ⟨k, m⟩
      have hkpos : 0 < k.val + 1 := by omega
      have hkN : k.val + 1 < N := by omega
      have hmpos : 0 < m.val + 1 := by omega
      have hmN : m.val + 1 < N := by omega
      refine ⟨k.val + 1, m.val + 1, hkpos, hkN, hmpos, hmN, ?_⟩
      have hterm := manuscriptVariationalTerm_eq_normalizedProxy N (k.val + 1) (m.val + 1)
        (by omega) (by omega)
      dsimp [f] at hEq
      rw [hterm] at hEq
      exact hEq.symm
    · rintro ⟨k, m, hkpos, hkN, hmpos, hmN, hv⟩
      have hkFin : k - 1 < N - 1 := by omega
      have hmFin : m - 1 < N - 1 := by omega
      let i : I := (⟨k - 1, hkFin⟩, ⟨m - 1, hmFin⟩)
      refine ⟨i, Finset.mem_univ _, ?_⟩
      have hkval : (k - 1 : ℕ) + 1 = k := by omega
      have hmval : (m - 1 : ℕ) + 1 = m := by omega
      have hterm := manuscriptVariationalTerm_eq_normalizedProxy N k m (by omega) (by omega)
      dsimp [f, i]
      rw [hkval, hmval, hterm, hv]
  change sSup {v : ℝ | ∃ k m : ℕ, 0 < k ∧ k < N ∧
      0 < m ∧ m < N ∧ v = normalizedHypergeomProxy N k m} =
    (Finset.univ : Finset I).sup' hne f
  rw [← himage, ← Finset.sup'_eq_csSup_image (Finset.univ : Finset I) hne f]

/-- Typed transcription of Proposition `prop:variational`: the constant defined
using every genuine finite-exchangeable probability measure and every real
zero-sum contrast is exactly the finite maximum and tilt supremum printed in
`eq:LKidentity`. -/
theorem manuscript_variational_contract (N : ℕ) (hN : 2 ≤ N) :
    exactExchangeableConstant N = manuscriptVariationalMaximum N hN := by
  rw [exactExchangeableConstant_eq_variational N hN,
    hypergeomVariationalConstant_eq_manuscript_maximum N hN]

/-- The same typed contract states the universal coefficient threshold for the
actual finite-exchangeable measures and zero-sum contrasts. -/
theorem manuscript_variational_coefficient_contract
    (N : ℕ) (hN : 2 ≤ N) (C : ℝ) :
    IsExchangeableCoefficient N C ↔ manuscriptVariationalMaximum N hN ≤ C := by
  rw [← hypergeomVariationalConstant_eq_manuscript_maximum N hN]
  exact exchangeable_coefficient_iff_variational N hN C

/-- Aggregate typed contract for `prop:variational`: the exact identity and
its universal coefficient characterization for genuine finite-exchangeable
laws and every real zero-sum contrast. -/
theorem manuscript_variational_full_contract (N : ℕ) (hN : 2 ≤ N) (C : ℝ) :
    (exactExchangeableConstant N = manuscriptVariationalMaximum N hN) ∧
    (IsExchangeableCoefficient N C ↔ manuscriptVariationalMaximum N hN ≤ C) := by
  exact ⟨manuscript_variational_contract N hN,
    manuscript_variational_coefficient_contract N hN C⟩

end
end ExactHoeffding
