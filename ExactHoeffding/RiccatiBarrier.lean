import ExactHoeffding.RiccatiCertificates
import ExactHoeffding.GlobalCrossing
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ExactHoeffding
noncomputable section

/-- At a contact with the quadratic envelope, the Riccati identity fixes the
sign of the difference of the two variance-curve derivatives. -/
theorem riccati_contact_derivative_sign (N m d z w : ℝ)
    (hm : 3≤m) (hhalf : 2*m<N) (hd : 0≤d)
    (hdelta : d≤barrierDelta N m)
    (hP : 0<varianceBarrier N m d (envelopeM N m*z/2))
    (hPB : varianceBarrier N m d (envelopeM N m*z/2)≤
      (m*(1-d)/2+envelopeM N m*z/2)*
      (m-(m*(1-d)/2+envelopeM N m*z/2))/m)
    (hode : riccatiF N (N*(1-d)/2) m (m*(1-d)/2+envelopeM N m*z/2)
      (varianceBarrier N m d (envelopeM N m*z/2))+
      N*(envelopeM N m*z/2)*varianceBarrier N m d (envelopeM N m*z/2)*w=0) :
    (z<0 → w-varianceBarrierDerivative N m d (envelopeM N m*z/2)<0) ∧
    (0<z → 0<w-varianceBarrierDerivative N m d (envelopeM N m*z/2)) := by
  have hN : 0<N := by linarith
  have hN1 : 0<N-1 := by linarith
  have hN2 : 0<N-2 := by linarith
  have hm0 : 0<m := by linarith
  have hNm : 0<N-m := by linarith
  have hM := envelopeM_positive N m hm hhalf
  have hG := barrierG_positive N m hm hhalf
  have hW := barrier_contact_W_positive N m d z hm hhalf hd hdelta hPB
  have hden := mul_pos hN hP
  have hid (hz : z≠0) := riccati_contact_derivative_identity N m d z w
    (ne_of_gt hN) (ne_of_gt hN1) (ne_of_gt hN2) (ne_of_gt hm0)
    (ne_of_gt hNm) (div_ne_zero (mul_ne_zero (ne_of_gt hM) hz) (by norm_num))
    (ne_of_gt hP) hode
  constructor
  · intro hz
    rw [hid (ne_of_lt hz)]
    have hy : envelopeM N m*z/2<0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hM hz) (by norm_num)
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hG hy) hW) hden
  · intro hz
    rw [hid (ne_of_gt hz)]
    positivity

/-- The same contact calculation in the original tilt variable avoids
introducing an inverse mean map. -/
theorem riccati_time_contact_identity (N m d z w : ℝ)
    (hN : N≠0) (hN1 : N-1≠0) (hN2 : N-2≠0)
    (hm : m≠0) (hNm : N-m≠0) (hy : envelopeM N m*z/2≠0)
    (hode : riccatiF N (N*(1-d)/2) m (m*(1-d)/2+envelopeM N m*z/2)
      (varianceBarrier N m d (envelopeM N m*z/2))+
      N*(envelopeM N m*z/2)*w=0) :
    w-varianceBarrierDerivative N m d (envelopeM N m*z/2)*
      varianceBarrier N m d (envelopeM N m*z/2)=
      barrierG N m*(envelopeM N m*z/2)*barrierW N m d z/N := by
  have hr := barrier_residual_identity N m d z hN1 hN2 hm hNm
  have hprod : (envelopeM N m*z/2)*
      ((w-varianceBarrierDerivative N m d (envelopeM N m*z/2)*
        varianceBarrier N m d (envelopeM N m*z/2))*N)=
      (envelopeM N m*z/2)*(barrierG N m*(envelopeM N m*z/2)*barrierW N m d z) := by
    linear_combination hode-hr
  exact (eq_div_iff hN).2 (mul_left_cancel₀ hy hprod)

theorem varianceBarrier_hasDerivAt (N m d y : ℝ) :
    HasDerivAt (varianceBarrier N m d) (varianceBarrierDerivative N m d y) y := by
  unfold varianceBarrier varianceBarrierDerivative
  have hcalc := (((hasDerivAt_const y (envelopeM N m*(1-d^2)/4)).add
    ((hasDerivAt_id y).const_mul (envelopeScale N m*d))).sub
    (((hasDerivAt_id y).pow 2).const_mul ((envelopeScale N m)^2/envelopeM N m)))
  have hf : (((fun x : ℝ => envelopeM N m*(1-d^2)/4)+
      fun y => envelopeScale N m*d*id y)-
      fun y => (envelopeScale N m)^2/envelopeM N m*(id^2) y)=
      (fun y => envelopeM N m*(1-d^2)/4+envelopeScale N m*d*y-
        (envelopeScale N m)^2/envelopeM N m*y^2) := by
    ext y
    rfl
  rw [hf] at hcalc
  exact hcalc.congr_deriv (by norm_num; ring)

end
end ExactHoeffding
