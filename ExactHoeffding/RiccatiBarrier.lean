import ExactHoeffding.RiccatiCertificates
import ExactHoeffding.GlobalCrossing

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

end
end ExactHoeffding
