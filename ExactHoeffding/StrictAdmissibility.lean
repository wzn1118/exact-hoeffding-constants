import ExactHoeffding.TiltedAdmissibilityDirect

namespace ExactHoeffding

theorem cross_sum_strict_order {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x a b : ι→ℝ)
    (h : ∀i∈s,∀j∈s,(x i-x j)*(a i*b j-a j*b i)≤0)
    (i j : ι) (hi : i∈s) (hj : j∈s)
    (hstrict : (x i-x j)*(a i*b j-a j*b i)<0) :
    (∑l∈s,x l*a l)*(∑l∈s,b l)<(∑l∈s,x l*b l)*(∑l∈s,a l) := by
  have hrow : (∑l∈s,(x i-x l)*(a i*b l-a l*b i))<0 := by
    apply Finset.sum_neg'
    · exact fun l hl => h i hi l hl
    · exact ⟨j,hj,hstrict⟩
  have hsum : (∑l∈s,∑q∈s,(x l-x q)*(a l*b q-a q*b l))<0 := by
    apply Finset.sum_neg'
    · exact fun l hl => Finset.sum_nonpos (fun q hq => h l hl q hq)
    · exact ⟨i,hi,hrow⟩
  rw [cross_sum_identity] at hsum
  linarith

theorem hypergeomTiltDown_pos (k m r i : ℕ) (hmk : m≤k) (hi : i<m) (t : ℝ) :
    0<hypergeomTiltDown k m r t i := by
  unfold hypergeomTiltDown
  have hiR : (i:ℝ)<m := by exact_mod_cast hi
  exact mul_pos (mul_pos (sub_pos.mpr hiR)
    (hypergeomMass_pos_canonical k m r i hmk hi.le)) (Real.exp_pos _)

/-- The actual mean-variance inequality is strict as soon as the support
contains at least three points. The strictness follows from two adjacent
tilted mass ratios, independently of a root factorization. -/
theorem hypergeomTiltVariance_admissible_strict (k m r : ℕ)
    (hmk : m≤k) (hm : 2≤m) (t : ℝ) :
    hypergeomTiltVariance (k+m+r) k m t<
      hypergeomTiltMean (k+m+r) k m t*
        ((m:ℝ)-hypergeomTiltMean (k+m+r) k m t)/(m:ℝ) := by
  have hc := hypergeomTiltUpDown_cross k m r 0 1 hmk (by omega) (by omega) t
  have h0 := hypergeomTiltDown_pos k m r 0 hmk (by omega) t
  have h1 := hypergeomTiltDown_pos k m r 1 hmk (by omega) t
  have hprod : 0<Real.exp t*((k:ℝ)+r+1)*
      hypergeomTiltDown k m r t 0*hypergeomTiltDown k m r t 1 := by positivity
  norm_num only [Nat.cast_zero,Nat.cast_one,zero_add,sub_zero] at hc
  have hden : 0<(1+(r:ℝ))*(1+1+(r:ℝ)) := by positivity
  have hdiff : 0<hypergeomTiltUp k m r t 0*hypergeomTiltDown k m r t 1-
      hypergeomTiltUp k m r t 1*hypergeomTiltDown k m r t 0 := by
    nlinarith only [hc,hprod,hden]
  have h := cross_sum_strict_order (Finset.range m) (fun i => (i:ℝ))
    (hypergeomTiltUp k m r t) (hypergeomTiltDown k m r t)
    (by
      intro i hi j hj
      exact hypergeomTiltUpDown_cross_order k m r i j hmk
        (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) t)
    0 1 (Finset.mem_range.mpr (by omega)) (Finset.mem_range.mpr (by omega))
    (by simpa only [Nat.cast_zero,Nat.cast_one,zero_sub,neg_mul,one_mul] using neg_neg_of_pos hdiff)
  rw [hypergeomTiltUp_first,hypergeomTiltDown_sum,hypergeomTiltDown_first,hypergeomTiltUp_sum] at h
  have hg := hypergeomMGF_pos (k+m+r) k m (by omega) (by omega) t
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  apply (lt_div_iff₀ hmR).2
  unfold hypergeomTiltVariance hypergeomTiltMean
  apply (mul_lt_mul_iff_of_pos_right (sq_pos_of_pos hg)).mp
  field_simp [ne_of_gt hg]
  nlinarith only [h]

end ExactHoeffding
