import ExactHoeffding.HypergeomBernoulliMGF
import ExactHoeffding.BernoulliRiccati
import ExactHoeffding.PoissonBinomial
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace ExactHoeffding
noncomputable section

private theorem bernoulliLog_hasDerivAt (p u : ℝ) (hp : p ∈ Set.Ioo 0 1) :
    HasDerivAt (fun v => Real.log (1-p+p*Real.exp v))
      (p*Real.exp u/(1-p+p*Real.exp u)) u := by
  have hd := scaledBernoulliDenom_hasDerivAt p 1 u
  have hpos := scaledBernoulliDenom_pos hp.1 hp.2 1 u
  simpa [scaledBernoulliDenom] using hd.log hpos.ne'

private theorem bernoulliMean_hasDerivAt (p u : ℝ) (hp : p ∈ Set.Ioo 0 1) :
    HasDerivAt (fun v => p*Real.exp v/(1-p+p*Real.exp v))
      (p*(1-p)*Real.exp u/(1-p+p*Real.exp u)^2) u := by
  have hd := scaledBernoulliDenom_hasDerivAt p 1 u
  have hpos := scaledBernoulliDenom_pos hp.1 hp.2 1 u
  have hn := (Real.hasDerivAt_exp u).const_mul p
  have hd' : HasDerivAt (fun v : ℝ => 1-p+p*Real.exp v) (p*Real.exp u) u := by
    exact hn.const_add (1-p)
  have hq := hn.fun_div hd' (by simpa [scaledBernoulliDenom] using hpos.ne')
  apply hq.congr_deriv
  field_simp [show 1-p+p*Real.exp u ≠ 0 by
    simpa only [scaledBernoulliDenom, one_mul] using hpos.ne']
  <;> ring

/-- A shifted Bernoulli factorization gives the logarithmic MGF identity. -/
theorem shifted_bernoulli_log_identity {f : ℝ → ℝ} {t b : ℝ} {j : ℕ}
    (hf : ∀ x, 0 < f x) (p : Fin j → ℝ) (hp : ∀ i, p i ∈ Set.Ioo 0 1)
    (h : ∀ u, f (t+u)/f t = Real.exp (b*u)*∏ i, (1-p i+p i*Real.exp u))
    (u : ℝ) :
    Real.log (f (t+u))-Real.log (f t) =
      b*u + ∑ i, Real.log (1-p i+p i*Real.exp u) := by
  have hl := congrArg Real.log (h u)
  rw [Real.log_div (hf _).ne' (hf _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Finset.prod_ne_zero_iff.mpr (by
      intro i hi
      exact (show 0 < 1-p i+p i*Real.exp u from
        add_pos (sub_pos.mpr (hp i).2) (mul_pos (hp i).1 (Real.exp_pos u))).ne')),
    Real.log_exp, Real.log_prod (fun i _ => (show 0 < 1-p i+p i*Real.exp u from
      add_pos (sub_pos.mpr (hp i).2) (mul_pos (hp i).1 (Real.exp_pos u))).ne')] at hl
  exact hl

/-- First derivative at the tilt is the deterministic shift plus the
Bernoulli means, for an actual everywhere-positive MGF. -/
theorem shifted_bernoulli_log_deriv {f : ℝ → ℝ} {t b : ℝ} {j : ℕ}
    (hf : ∀ x, 0 < f x) (p : Fin j → ℝ) (hp : ∀ i, p i ∈ Set.Ioo 0 1)
    (h : ∀ u, f (t+u)/f t = Real.exp (b*u)*∏ i, (1-p i+p i*Real.exp u)) :
    deriv (fun x => Real.log (f x)) t = b + ∑ i, p i := by
  have hid : (fun u => Real.log (f (t+u))-Real.log (f t)) =
      (fun u => b*u + ∑ i, Real.log (1-p i+p i*Real.exp u)) :=
    funext (shifted_bernoulli_log_identity hf p hp h)
  have hd := (hasDerivAt_const_mul b (x := (0:ℝ))).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => bernoulliLog_hasDerivAt (p i) 0 (hp i)))
  have he := congrArg (fun F : ℝ → ℝ => deriv F 0) hid
  have hd' : HasDerivAt (fun u : ℝ => b*u + ∑ i, Real.log (1-p i+p i*Real.exp u))
      (b+∑ i, p i*Real.exp 0/(1-p i+p i*Real.exp 0)) 0 := by
    convert! hd using 1
  rw [hd'.deriv] at he
  rw [deriv_sub_const,
    deriv_comp_const_add (fun x : ℝ => Real.log (f x)) t 0] at he
  simpa only [add_zero, Real.exp_zero, mul_one, sub_add_cancel, div_one] using he

/-- The second log derivative at the tilt is the sum of Bernoulli variances. -/
theorem shifted_bernoulli_log_second_deriv {f : ℝ → ℝ} {t b : ℝ} {j : ℕ}
    (hf : ∀ x, 0 < f x) (p : Fin j → ℝ) (hp : ∀ i, p i ∈ Set.Ioo 0 1)
    (h : ∀ u, f (t+u)/f t = Real.exp (b*u)*∏ i, (1-p i+p i*Real.exp u)) :
    deriv (deriv (fun x => Real.log (f x))) t = ∑ i, p i*(1-p i) := by
  have hid : (fun u => Real.log (f (t+u))-Real.log (f t)) =
      (fun u => b*u + ∑ i, Real.log (1-p i+p i*Real.exp u)) :=
    funext (shifted_bernoulli_log_identity hf p hp h)
  have hd (u : ℝ) := (hasDerivAt_const_mul b (x := u)).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => bernoulliLog_hasDerivAt (p i) u (hp i)))
  have hfirst : (fun u => deriv (fun x => Real.log (f x)) (t+u)) =
      (fun u => b+∑ i, p i*Real.exp u/(1-p i+p i*Real.exp u)) := by
    funext u
    have he := congrArg (fun F : ℝ → ℝ => deriv F u) hid
    have hd' : HasDerivAt (fun u : ℝ => b*u + ∑ i, Real.log (1-p i+p i*Real.exp u))
        (b+∑ i, p i*Real.exp u/(1-p i+p i*Real.exp u)) u := by
      convert! hd u using 1
    rw [hd'.deriv] at he
    rw [deriv_sub_const,
      deriv_comp_const_add (fun x : ℝ => Real.log (f x)) t u] at he
    exact he
  have hs := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => bernoulliMean_hasDerivAt (p i) 0 (hp i))).const_add b
  have he := congrArg (fun F : ℝ → ℝ => deriv F 0) hfirst
  have hs' : HasDerivAt (fun u : ℝ => b+∑ i, p i*Real.exp u/(1-p i+p i*Real.exp u))
      (∑ i, p i*(1-p i)*Real.exp 0/(1-p i+p i*Real.exp 0)^2) 0 := by
    simpa only using hs
  rw [hs'.deriv] at he
  rw [deriv_comp_const_add] at he
  simpa only [add_zero, Real.exp_zero, mul_one, sub_add_cancel, one_pow, div_one] using he

/-- Every tilted hypergeometric law has the mean and variance of its
lower support endpoint plus a Bernoulli sum of the true support width. -/
theorem hypergeom_tilted_bernoulli_mean_variance (N k m : ℕ)
    (hk : k≤N) (hm : m≤N) (t : ℝ) :
    ∃ p : Fin (min (min k (N-k)) (min m (N-m))) → ℝ,
      (∀ i, p i ∈ Set.Ioo 0 1) ∧
      hypergeomTiltMean N k m t = ((k+m-N:ℕ):ℝ)+∑ i, p i ∧
      hypergeomTiltVariance N k m t = ∑ i, p i*(1-p i) := by
  obtain ⟨p,hp,h⟩ := hypergeom_tilted_shifted_bernoulli_mgf N k m hk hm t
  refine ⟨p,hp,?_,?_⟩
  · have he := shifted_bernoulli_log_deriv (hypergeomMGF_pos N k m hk hm) p hp h
    have hd := finiteLogMGF_hasDerivAt (Finset.range (m+1)) (hypergeomMass N k m)
      (fun i => (i:ℝ)) (fun i _ => hypergeomMass_nonneg N k m i)
      (hypergeomMass_total N k m hk hm) t
    change HasDerivAt (fun u => Real.log (hypergeomMGF N k m u)) (hypergeomTiltMean N k m t) t at hd
    rw [hd.deriv] at he
    exact he
  · rw [← hypergeomLogMGF_second_deriv_eq_variance N k m hk hm t]
    exact shifted_bernoulli_log_second_deriv (hypergeomMGF_pos N k m hk hm) p hp h

/-- The actual hypergeometric tilt lies in the Bernoulli feasible region
after subtracting its true lower support endpoint. -/
theorem hypergeom_tilted_true_support_mean_variance_bound (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ)
    (hj : 0 < min (min k (N-k)) (min m (N-m))) :
    hypergeomTiltVariance N k m t ≤
      (hypergeomTiltMean N k m t - ((k+m-N : ℕ) : ℝ)) *
        ((min (min k (N-k)) (min m (N-m)) : ℕ) -
          (hypergeomTiltMean N k m t - ((k+m-N : ℕ) : ℝ))) /
        (min (min k (N-k)) (min m (N-m)) : ℕ) := by
  obtain ⟨p, hp, hu, hv⟩ := hypergeom_tilted_bernoulli_mean_variance N k m hk hm t
  have hsum : hypergeomTiltMean N k m t - ((k+m-N : ℕ) : ℝ) = ∑ i, p i := by
    rw [hu]
    ring
  rw [hv, hsum]
  exact finite_mean_variance_bound hj p

end
end ExactHoeffding
