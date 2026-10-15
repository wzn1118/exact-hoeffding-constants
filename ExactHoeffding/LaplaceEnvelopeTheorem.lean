import ExactHoeffding.HypergeometricLaplace

namespace ExactHoeffding

/-- The complete sub-half-population parameter domain, in the original
`N,k,m` coordinates, with strictness for every nonzero real tilt. -/
theorem hypergeom_laplace_envelope (N k m : ℕ)
    (hm : 3≤m) (hmk : m≤k) (hk : 2*k≤N) (hhalf : 2*m<N) :
    (∀t, hypergeomCenteredLogMGF N k m t≤
      scaledBernoulliLogLaplace (envelopeM (N:ℝ) (m:ℝ))
        ((k:ℝ)/(N:ℝ)) (envelopeScale (N:ℝ) (m:ℝ)) t) ∧
    (∀t, t≠0 → hypergeomCenteredLogMGF N k m t<
      scaledBernoulliLogLaplace (envelopeM (N:ℝ) (m:ℝ))
        ((k:ℝ)/(N:ℝ)) (envelopeScale (N:ℝ) (m:ℝ)) t) := by
  have hkm : k+m≤N := by omega
  have hn : k+m+(N-(k+m))=N := Nat.add_sub_of_le hkm
  have h := hypergeom_laplace_envelope_canonical k m (N-(k+m)) hm hmk
    (by omega) (by omega)
  dsimp only at h
  have hreal : (k:ℝ)+(m:ℝ)+((N-(k+m):ℕ):ℝ)=(N:ℝ) := by
    exact_mod_cast hn
  simpa only [hn,hreal] using h

theorem hypergeom_laplace_envelope_equality_iff (N k m : ℕ)
    (hm : 3≤m) (hmk : m≤k) (hk : 2*k≤N) (hhalf : 2*m<N) (t : ℝ) :
    hypergeomCenteredLogMGF N k m t=
      scaledBernoulliLogLaplace (envelopeM (N:ℝ) (m:ℝ))
        ((k:ℝ)/(N:ℝ)) (envelopeScale (N:ℝ) (m:ℝ)) t ↔ t=0 := by
  constructor
  · intro heq
    by_contra hne
    exact (ne_of_lt ((hypergeom_laplace_envelope N k m hm hmk hk hhalf).2 t hne)) heq
  · rintro rfl
    rw [hypergeomCenteredLogMGF_zero N k m (by omega) (by omega),
      scaledBernoulliLogLaplace_zero]

end ExactHoeffding
