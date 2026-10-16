import ExactHoeffding.PiecewiseKL
import ExactHoeffding.BernoulliMGFGeometry
import ExactHoeffding.HypergeometricLaplace
import ExactHoeffding.HypergeometricTail
import ExactHoeffding.Chernoff

namespace ExactHoeffding
noncomputable section

lemma canonical_true_support_min_eq_m (k m r : ℕ)
    (hmk : m ≤ k) (hgap : m < k + r) :
    min (min k (k + m + r - k)) (min m (k + m + r - m)) = m := by
  have hk : k + m + r - k = m + r := by omega
  have hm' : k + m + r - m = k + r := by omega
  rw [hk, hm']
  have hleft : m ≤ min k (m + r) := (Nat.le_min).2 ⟨hmk, by omega⟩
  have hright : min m (k + r) = m := Nat.min_eq_left (by omega)
  rw [hright, Nat.min_eq_right hleft]

lemma canonical_hypergeom_variance_le_binomial_envelope (k m r : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hgap : m < k + r) (t : ℝ) :
    hypergeomTiltVariance (k + m + r) k m t ≤
      hypergeomTiltMean (k + m + r) k m t *
        ((m : ℝ) - hypergeomTiltMean (k + m + r) k m t) / (m : ℝ) := by
  have hN : m ≤ k + m + r := by omega
  have hmin : min (min k ((k + m + r) - k)) (min m ((k + m + r) - m)) = m := by
    simpa [Nat.add_sub_cancel_left, Nat.add_sub_cancel] using
      canonical_true_support_min_eq_m k m r hmk hgap
  have hj : 0 < min (min k ((k + m + r) - k)) (min m ((k + m + r) - m)) := by
    rw [hmin]
    omega
  have h := hypergeom_tilted_true_support_mean_variance_bound
    (k + m + r) k m (by omega) hN t hj
  rw [hmin] at h
  convert h using 1 <;> norm_num [Nat.cast_add, Nat.cast_sub] <;> field_simp <;> ring_nf

lemma canonical_hypergeom_loglaplace_le_ordinary_bernoulli (k m r : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hgap : m < k + r) :
    ∀ t : ℝ,
      hypergeomCenteredLogMGF (k + m + r) k m t ≤
        (m : ℝ) * bernoulliCenteredLogMGF
          ((k : ℝ) / ((k + m + r : ℕ) : ℝ)) t := by
  let N : ℝ := ((k + m + r : ℕ) : ℝ)
  let p : ℝ := (k : ℝ) / N
  let y : ℝ → ℝ := fun t => hypergeomTiltMean (k + m + r) k m t - (m : ℝ) * p
  let v : ℝ → ℝ := hypergeomTiltVariance (k + m + r) k m
  have hN : 0 < N := by
    dsimp [N]
    positivity
  have hp0 : 0 < p := by
    dsimp [p]
    exact div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : p < 1 := by
    apply (div_lt_one hN).2
    dsimp [N]
    exact_mod_cast (show k < k + m + r by omega)
  have hyd (t : ℝ) : HasDerivAt y (v t) t := by
    exact (hypergeomTiltMean_hasDerivAt (k + m + r) k m (by omega) (by omega) t).sub_const _
  have hFd (t : ℝ) : HasDerivAt (hypergeomCenteredLogMGF (k + m + r) k m) (y t) t := by
    have h := hypergeomCenteredLogMGF_hasDerivAt (k + m + r) k m (by omega) (by omega) t
    dsimp [y, p, N]
    convert h using 1 <;> norm_num [Nat.cast_add] <;> ring
  have hy0 : y 0 = 0 := by
    dsimp [y, p, N]
    rw [hypergeomTiltMean_zero (k + m + r) k m (by omega) (by omega)]
    ring
  have hF0 := hypergeomCenteredLogMGF_zero (k + m + r) k m (by omega) (by omega)
  have hv (t : ℝ) : v t ≤
      (m : ℝ) * p * (1-p) + (1-2*p) * y t - (1/(m : ℝ)) * (y t)^2 := by
    have h := canonical_hypergeom_variance_le_binomial_envelope k m r hm hmk hgap t
    dsimp [v, y, p, N]
    convert h using 1 <;> norm_num [Nat.cast_add] <;> field_simp <;> ring_nf
  have hmain := variance_bound_implies_scaled_bernoulli_laplace
    (M := (m : ℝ)) (p := p) (a := (1 : ℝ))
    (by positivity) one_ne_zero hp0 hp1 hyd hFd (by
      intro t
      simpa [one_mul, one_pow] using hv t) hy0 hF0
  intro t
  have ht := hmain t
  dsimp [p, N] at ht ⊢
  simpa [scaledBernoulliLogLaplace, scaledBernoulliDenom,
    bernoulliCenteredLogMGF, bernoulliMGF, one_mul, one_pow] using ht

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

lemma canonical_fenchel_tilt_nonneg {p x : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1) (hpx : p ≤ x) :
    0 ≤ bernoulliFenchelTilt p x := by
  unfold bernoulliFenchelTilt
  apply Real.log_nonneg
  apply (le_div_iff₀ (mul_pos hp (sub_pos.mpr hx1))).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hpx) (sub_nonneg.mpr hp1.le)]

theorem hypergeom_upper_tail_ordinary_kl_canonical (k m r : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hgap : m < k + r)
    (v : ℝ)
    (hv0 : (m : ℝ) * (k : ℝ) / (k + m + r) ≤ v)
    (hvm : v < m) :
    (∑ i ∈ Finset.range (m + 1),
      if v ≤ (i : ℝ) then hypergeomMass (k + m + r) k m i else 0) ≤
      Real.exp (-(m : ℝ) * bernoulliKL
        ((k : ℝ) / (k + m + r)) (v / (m : ℝ))) := by
  let N : ℝ := ((k + m + r : ℕ) : ℝ)
  let p : ℝ := (k : ℝ) / N
  let x : ℝ := v / (m : ℝ)
  let t : ℝ := bernoulliFenchelTilt p x
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  have hp0 : 0 < p := by dsimp [p]; exact div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : p < 1 := by
    apply (div_lt_one hN).2
    dsimp [N]
    exact_mod_cast (show k < k + m + r by omega)
  have hx0 : 0 < x := by
    dsimp [x]
    have hmu : (0 : ℝ) < (m : ℝ) * (k : ℝ) / N := by
      exact div_pos (mul_pos (by positivity) (by exact_mod_cast (show 0 < k by omega))) hN
    have hmv : (m : ℝ) * (k : ℝ) / N ≤ v := by simpa [N] using hv0
    exact div_pos (lt_of_lt_of_le hmu hmv) hm0
  have hx1 : x < 1 := by
    dsimp [x]
    exact (div_lt_one hm0).2 hvm
  have hpx : p ≤ x := by
    dsimp [p, x, N]
    have hden : (0 : ℝ) < (k + m + r : ℕ) := by positivity
    apply (div_le_div_iff₀ hden hm0).2
    have hv0' : (m : ℝ) * (k : ℝ) / (k + m + r : ℕ) ≤ v := by
      simpa [Nat.cast_add] using hv0
    have hcross := (div_le_iff₀ hden).mp hv0'
    simpa [Nat.cast_add, mul_comm, mul_left_comm, mul_assoc] using hcross
  have ht : 0 ≤ t := by
    exact canonical_fenchel_tilt_nonneg hp0 hp1 hx0 hx1 hpx
  have hmark := finite_markov_exp_bound (Finset.range (m + 1))
    (hypergeomMass (k + m + r) k m)
    (fun i => (i : ℝ) - (m : ℝ) * (k : ℝ) / N)
    (fun i => v ≤ (i : ℝ))
    (fun i hi => hypergeomMass_nonneg (k + m + r) k m i)
    t (v - (m : ℝ) * (k : ℝ) / N) ht
    (fun i hi hev => by linarith)
  have hmgf : centeredHypergeomMGF (k + m + r) k m t ≤
      Real.exp ((m : ℝ) * bernoulliCenteredLogMGF p t) := by
    calc
      centeredHypergeomMGF (k + m + r) k m t =
          Real.exp (hypergeomCenteredLogMGF (k + m + r) k m t) :=
        centeredHypergeomMGF_eq_exp_log (k + m + r) k m (by omega) (by omega) t
      _ ≤ Real.exp ((m : ℝ) * bernoulliCenteredLogMGF p t) := by
        apply Real.exp_le_exp.mpr
        have h := canonical_hypergeom_loglaplace_le_ordinary_bernoulli k m r hm hmk hgap t
        simpa [p, N] using h
  have hprod : Real.exp (-(t * (v - (m : ℝ) * (k : ℝ) / N))) *
      centeredHypergeomMGF (k + m + r) k m t ≤
      Real.exp (-(m : ℝ) * bernoulliKL p x) := by
    calc
      Real.exp (-(t * (v - (m : ℝ) * (k : ℝ) / N))) *
          centeredHypergeomMGF (k + m + r) k m t ≤
          Real.exp (-(t * (v - (m : ℝ) * (k : ℝ) / N))) *
            Real.exp ((m : ℝ) * bernoulliCenteredLogMGF p t) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
      _ = Real.exp (-(t * (v - (m : ℝ) * (k : ℝ) / N)) +
            (m : ℝ) * bernoulliCenteredLogMGF p t) := by rw [← Real.exp_add]
      _ ≤ Real.exp (-(m : ℝ) * bernoulliKL p x) := by
        apply Real.exp_le_exp.mpr
        have hid := bernoulli_fenchel_identity p x hp0 hp1 hx0 hx1
        have hscale : v - (m : ℝ) * (k : ℝ) / N = (m : ℝ) * (x-p) := by
          dsimp [x, p, N]
          field_simp
        rw [hscale]
        rw [show -(t * ((m : ℝ) * (x-p))) + (m : ℝ) * bernoulliCenteredLogMGF p t =
          -(m : ℝ) * (t * (x-p) - bernoulliCenteredLogMGF p t) by ring]
        rw [hid]
  calc
    (∑ i ∈ Finset.range (m + 1), if v ≤ (i : ℝ) then hypergeomMass (k + m + r) k m i else 0) ≤
        Real.exp (-(t * (v - (m : ℝ) * (k : ℝ) / N))) *
          centeredHypergeomMGF (k + m + r) k m t := by
            simpa [centeredHypergeomMGF, centeredHypergeomMGF_factor, N, mul_comm] using hmark
    _ ≤ Real.exp (-(m : ℝ) * bernoulliKL p x) := hprod
    _ = Real.exp (-(m : ℝ) * bernoulliKL
        ((k : ℝ) / (k + m + r)) (v / (m : ℝ))) := by
          simp [p, x, N, Nat.cast_add]

end
end ExactHoeffding
