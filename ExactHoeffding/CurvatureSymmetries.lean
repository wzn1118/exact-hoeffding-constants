import ExactHoeffding.HypergeometricODE
import ExactHoeffding.Symmetries
import Mathlib.Analysis.Calculus.Deriv.Comp
namespace ExactHoeffding

theorem second_deriv_reflection_affine
    (f g dg ddg : ℝ→ℝ) (c : ℝ)
    (h : ∀t, f t=c*t+g (-t))
    (hg : ∀t, HasDerivAt g (dg t) t)
    (hdg : ∀t, HasDerivAt dg (ddg t) t) (t : ℝ) :
    deriv (deriv f) t=ddg (-t) := by
  have hneg (s : ℝ) : HasDerivAt (fun x : ℝ => -x) (-1) s :=
    (hasDerivAt_id s).neg
  have hd (s : ℝ) : HasDerivAt f (c-dg (-s)) s := by
    have hc := (hasDerivAt_const_mul c (x := s)).add ((hg (-s)).comp s (hneg s))
    have hf : f=(fun x => c*x+g (-x)) := funext h
    rw [hf]
    simpa only [Function.comp_def,Pi.add_apply,mul_neg_one,sub_eq_add_neg] using! hc
  have hdf : deriv f=(fun s => c-dg (-s)) := funext (fun s => (hd s).deriv)
  rw [hdf]
  have h2 := (hasDerivAt_const t c).sub ((hdg (-t)).comp t (hneg t))
  have he : HasDerivAt (fun s => c-dg (-s)) (ddg (-t)) t := by
    simpa only [Function.comp_def,Pi.sub_apply,mul_neg_one,zero_sub,neg_neg] using! h2
  exact he.deriv

theorem hypergeomTiltVariance_transpose (N k m : ℕ) (hk : k≤N) (hm : m≤N) (t : ℝ) :
    hypergeomTiltVariance N k m t=hypergeomTiltVariance N m k t := by
  rw [← hypergeomLogMGF_second_deriv_eq_variance N k m hk hm t,
    ← hypergeomLogMGF_second_deriv_eq_variance N m k hm hk t]
  have hf : (fun s => Real.log (hypergeomMGF N k m s))=
      (fun s => Real.log (hypergeomMGF N m k s)) := by
    funext s
    rw [hypergeomMGF_transpose N k m hk hm s]
  rw [hf]

theorem hypergeomTiltVariance_success_complement (N k m : ℕ)
    (hk : k≤N) (hm : m≤N) (t : ℝ) :
    hypergeomTiltVariance N k m t=hypergeomTiltVariance N (N-k) m (-t) := by
  have hk' : N-k≤N := Nat.sub_le _ _
  rw [← hypergeomLogMGF_second_deriv_eq_variance N k m hk hm t]
  apply second_deriv_reflection_affine
    (fun s => Real.log (hypergeomMGF N k m s))
    (fun s => Real.log (hypergeomMGF N (N-k) m s))
    (hypergeomTiltMean N (N-k) m) (hypergeomTiltVariance N (N-k) m) (m:ℝ)
  · intro s
    rw [hypergeomMGF_success_complement N k m hk hm s,
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (hypergeomMGF_pos N (N-k) m hk' hm (-s))),
      Real.log_exp]
    ring
  · intro s
    exact finiteLogMGF_hasDerivAt (Finset.range (m+1)) (hypergeomMass N (N-k) m)
      (fun i => (i:ℝ)) (fun i _ => hypergeomMass_nonneg N (N-k) m i)
      (hypergeomMass_total N (N-k) m hk' hm) s
  · exact hypergeomTiltMean_hasDerivAt N (N-k) m hk' hm

theorem hypergeomTiltVariance_sample_complement (N k m : ℕ)
    (hk : k≤N) (hm : m≤N) (t : ℝ) :
    hypergeomTiltVariance N k m t=hypergeomTiltVariance N k (N-m) (-t) := by
  rw [hypergeomTiltVariance_transpose N k m hk hm t,
    hypergeomTiltVariance_success_complement N m k hm hk t,
    hypergeomTiltVariance_transpose N (N-m) k (Nat.sub_le _ _) hk (-t)]

end ExactHoeffding
