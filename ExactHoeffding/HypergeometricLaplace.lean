import ExactHoeffding.HypergeometricBarrier
import ExactHoeffding.ScaledBernoulliComparison

namespace ExactHoeffding
noncomputable section

def hypergeomCenteredLogMGF (N k m : ℕ) (t : ℝ) :=
  Real.log (hypergeomMGF N k m t)-(m:ℝ)*(k:ℝ)/(N:ℝ)*t

theorem hypergeomCenteredLogMGF_hasDerivAt (N k m : ℕ) (hk : k≤N) (hm : m≤N)
    (t : ℝ) : HasDerivAt (hypergeomCenteredLogMGF N k m)
      (hypergeomTiltMean N k m t-(m:ℝ)*(k:ℝ)/(N:ℝ)) t := by
  exact (finiteLogMGF_hasDerivAt (Finset.range (m+1)) (hypergeomMass N k m)
    (fun i => (i:ℝ)) (fun i _ => hypergeomMass_nonneg N k m i)
    (hypergeomMass_total N k m hk hm) t).sub
    (hasDerivAt_const_mul ((m:ℝ)*(k:ℝ)/(N:ℝ)))

theorem hypergeomCenteredLogMGF_zero (N k m : ℕ) (hk : k≤N) (hm : m≤N) :
    hypergeomCenteredLogMGF N k m 0=0 := by
  simp [hypergeomCenteredLogMGF,hypergeomMGF_zero N k m hk hm]

/-- The manuscript's parity-uniform scaled Bernoulli envelope, proved for
the actual finite hypergeometric log-Laplace transform. -/
theorem hypergeom_laplace_envelope_canonical (k m r : ℕ)
    (hm : 3≤m) (hmk : m≤k) (hk : k≤m+r) (hgap : m<k+r) :
    let N : ℝ := (k:ℝ)+m+r
    let M := envelopeM N (m:ℝ)
    let a := envelopeScale N (m:ℝ)
    (∀t, hypergeomCenteredLogMGF (k+m+r) k m t≤
      scaledBernoulliLogLaplace M ((k:ℝ)/N) a t) ∧
    (∀t, t≠0 → hypergeomCenteredLogMGF (k+m+r) k m t<
      scaledBernoulliLogLaplace M ((k:ℝ)/N) a t) := by
  let N : ℝ := (k:ℝ)+m+r
  let M := envelopeM N (m:ℝ)
  let a := envelopeScale N (m:ℝ)
  let p := (k:ℝ)/N
  let y : ℝ→ℝ := fun t => hypergeomTiltMean (k+m+r) k m t-(m:ℝ)*p
  let v := hypergeomTiltVariance (k+m+r) k m
  have hmR : (3:ℝ)≤m := by exact_mod_cast hm
  have hmkR : (m:ℝ)≤k := by exact_mod_cast hmk
  have hgapR : (m:ℝ)<k+r := by exact_mod_cast hgap
  have hN : 0<N := by dsimp [N]; have := Nat.cast_nonneg (α := ℝ) r; linarith
  have hhalf : 2*(m:ℝ)<N := by dsimp [N]; linarith
  have hN2 : 0<N-2 := by linarith
  have hp0 : 0<p := div_pos (by linarith) hN
  have hp1 : p<1 := by
    apply (div_lt_one hN).2
    dsimp [N]
    have := Nat.cast_nonneg (α := ℝ) r
    linarith
  have hM : M≠0 := ne_of_gt (envelopeM_positive N (m:ℝ) hmR hhalf)
  have ha : a≠0 := ne_of_gt (div_pos (sub_pos.mpr hhalf) hN2)
  have hparam : ((k+m+r:ℕ):ℝ)=N := by simp only [Nat.cast_add,N]
  have hmul : (m:ℝ)*(k:ℝ)/N=(m:ℝ)*p := by dsimp [p]; ring
  have hyd (t : ℝ) : HasDerivAt y (v t) t :=
    (hypergeomTiltMean_hasDerivAt (k+m+r) k m (by omega) (by omega) t).sub_const _
  have hFd (t : ℝ) : HasDerivAt (hypergeomCenteredLogMGF (k+m+r) k m) (y t) t := by
    have hh := hypergeomCenteredLogMGF_hasDerivAt (k+m+r) k m (by omega) (by omega) t
    rw [hparam,hmul] at hh
    exact hh
  have hy0 : y 0=0 := by
    dsimp [y]
    rw [hypergeomTiltMean_zero (k+m+r) k m (by omega) (by omega),hparam,hmul]
    ring
  have hF0 := hypergeomCenteredLogMGF_zero (k+m+r) k m (by omega) (by omega)
  have hbar := hypergeomTiltVariance_barrier_canonical k m r hm hmk hk hgap
  dsimp only at hbar
  have he (t : ℝ) : varianceBarrier N (m:ℝ) (1-2*p) (y t)=
      M*p*(1-p)+a*(1-2*p)*y t-a^2/M*(y t)^2 := by
    unfold varianceBarrier
    dsimp [M,a]
    ring
  have hv (t : ℝ) : v t≤M*p*(1-p)+a*(1-2*p)*y t-a^2/M*(y t)^2 := by
    rw [← he t]
    simpa only [N,p,y,v,hmul,mul_div_assoc] using hbar.1 t
  have hvs (t : ℝ) (ht : t≠0) : v t<M*p*(1-p)+a*(1-2*p)*y t-a^2/M*(y t)^2 := by
    apply lt_of_le_of_ne (hv t)
    intro heq
    have hvEq : v t=varianceBarrier N (m:ℝ) (1-2*p) (y t) :=
      heq.trans (he t).symm
    apply ht
    apply (hbar.2 t).1
    simpa only [N,p,y,v,hmul,mul_div_assoc] using hvEq
  exact ⟨variance_bound_implies_scaled_bernoulli_laplace hM ha hp0 hp1 hyd hFd hv hy0 hF0,
    strict_variance_bound_implies_scaled_bernoulli_laplace hM ha hp0 hp1 hyd hFd hvs hy0 hF0⟩

end
end ExactHoeffding
