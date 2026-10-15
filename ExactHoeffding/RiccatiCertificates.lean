import ExactHoeffding.Basic
import Mathlib.Tactic.LinearCombination

namespace ExactHoeffding
noncomputable section

def riccatiA (N k m u : ℝ) := u*(u+N-k-m)
def riccatiC (k m u : ℝ) := (k-u)*(m-u)
def riccatiF (N k m u v : ℝ) :=
  -(N-1)*v^2+(riccatiA N k m u+riccatiC k m u-
    (2*u+N-k-m)*riccatiC k m u+(2*u-k-m)*riccatiA N k m u)*v+
    riccatiA N k m u*riccatiC k m u

theorem riccati_differential_algebra (N k m u v w : ℝ) :
    v*(((2*u+N-k-m)+w)*(riccatiC k m u+v)-
      ((2*u-k-m)+w)*(riccatiA N k m u+v))-
      (riccatiA N k m u+v)*(riccatiC k m u+v) =
    (k*m-N*u)*v*w-riccatiF N k m u v := by
  unfold riccatiF riccatiA riccatiC
  ring

def envelopeM (N m : ℝ) := m*(N-m)/(N-1)
def envelopeScale (N m : ℝ) := (N-2*m)/(N-2)
def varianceBarrier (N m d y : ℝ) :=
  envelopeM N m*(1-d^2)/4+envelopeScale N m*d*y-
    (envelopeScale N m)^2/envelopeM N m*y^2
def varianceBarrierDerivative (N m d y : ℝ) :=
  envelopeScale N m*d-2*(envelopeScale N m)^2/envelopeM N m*y
def barrierW (N m d z : ℝ) :=
  N-4+3*N*d^2-4*N*envelopeScale N m*d*z+
    ((N+1)*(envelopeScale N m)^2-envelopeM N m)*z^2
def barrierG (N m : ℝ) := N^2*(m-1)*(N-m-1)/(4*(N-2)^2*(N-1))
def admissibilityE (N m d z : ℝ) :=
  1-d^2+4*(N-m)/(N-2)*d*z-
    (N-m)*(3*N^2-4*N-4*m*(N-1))/((N-1)*(N-2)^2)*z^2

theorem barrier_admissibility_identity (N m d z : ℝ)
    (hN1 : N-1≠0) (hN2 : N-2≠0) (hm : m≠0) (hNm : N-m≠0) :
    (m*(1-d)/2+envelopeM N m*z/2)*
      (m-(m*(1-d)/2+envelopeM N m*z/2))/m-
      varianceBarrier N m d (envelopeM N m*z/2) =
      m*(m-1)/(4*(N-1))*admissibilityE N m d z := by
  unfold varianceBarrier envelopeM envelopeScale admissibilityE
  field_simp
  ring

def barrierLambda (N m : ℝ) := (m^2-m*N+3*m+N^2-4*N)/(2*(N-m))
def barrierDelta (N m : ℝ) := (N-2*m)/N
def barrierAlpha (N m : ℝ) := (N-4-barrierLambda N m)/(barrierDelta N m)^2
def certificateA (N m : ℝ) := 3*N+barrierLambda N m+barrierAlpha N m
def certificateB (N m : ℝ) := -2*N*envelopeScale N m-2*barrierLambda N m*(N-m)/(N-2)
def certificateC (N m : ℝ) := (N+1)*(envelopeScale N m)^2-envelopeM N m+
  barrierLambda N m*(N-m)*(3*N^2-4*N-4*m*(N-1))/((N-1)*(N-2)^2)

theorem barrier_sum_of_squares_identity (N m d z : ℝ)
    (hN : N≠0) (hhalf : N-2*m≠0) (hN1 : N-1≠0)
    (hN2 : N-2≠0) (hNm : N-m≠0) :
    barrierW N m d z = barrierLambda N m*admissibilityE N m d z+
      barrierAlpha N m*((barrierDelta N m)^2-d^2)+
      certificateA N m*d^2+2*certificateB N m*d*z+certificateC N m*z^2 := by
  unfold barrierW admissibilityE certificateA certificateB certificateC
  have hd : barrierDelta N m ≠ 0 := div_ne_zero hhalf hN
  have ha : barrierAlpha N m*(barrierDelta N m)^2=N-4-barrierLambda N m := by
    unfold barrierAlpha
    exact div_mul_cancel₀ _ (pow_ne_zero 2 hd)
  linear_combination -ha

def certificateU (N m : ℝ) := N^2-2*N-m^2-m*N+3*m
def certificateV (N m : ℝ) := m^3-6*m^2-2*m*N^2+14*m*N-3*m+N^3-7*N^2+6*N

theorem certificate_U_expansion (j r : ℝ) :
    certificateU (2*(j+3)+r) (j+3)=j^2+3*j*r+5*j+r^2+7*r+6 := by
  unfold certificateU
  ring

theorem certificate_V_expansion (j r : ℝ) :
    certificateV (2*(j+3)+r) (j+3)=
      j^3+4*j^2*r+3*j^2+4*j*r^2+10*j*r+r^3+5*r^2 := by
  unfold certificateV
  ring

theorem certificate_U_positive (j r : ℝ) (hj : 0≤j) (hr : 0≤r) :
    0<certificateU (2*(j+3)+r) (j+3) := by
  rw [certificate_U_expansion]
  positivity

theorem certificate_V_positive (j r : ℝ) (hj : 0≤j) (hr : 0<r) :
    0<certificateV (2*(j+3)+r) (j+3) := by
  rw [certificate_V_expansion]
  positivity

theorem quadratic_form_identity (A B C d z : ℝ) :
    A*(A*d^2+2*B*d*z+C*z^2)=(A*d+B*z)^2+(A*C-B^2)*z^2 := by ring

theorem quadratic_form_positive (A B C d z : ℝ)
    (hA : 0<A) (hdet : 0<A*C-B^2) (hne : d≠0 ∨ z≠0) :
    0<A*d^2+2*B*d*z+C*z^2 := by
  have hid := quadratic_form_identity A B C d z
  by_cases hz : z=0
  · subst hz
    have hd : d≠0 := hne.resolve_right (not_not_intro rfl)
    simpa using mul_pos hA (sq_pos_of_ne_zero hd)
  · have hpos := mul_pos hdet (sq_pos_of_ne_zero hz)
    have hsq := sq_nonneg (A*d+B*z)
    nlinarith

theorem certificate_lambda_expansion (j r : ℝ) (hden : j+3+r≠0) :
    2*(2*(j+3)+r-(j+3))*barrierLambda (2*(j+3)+r) (j+3)=
      3*j^2+3*j*r+13*j+r^2+5*r+12 := by
  unfold barrierLambda
  have heq : 2*(j+3)+r-(j+3)=j+3+r := by ring
  rw [heq]
  field_simp [hden]
  ring

theorem certificate_alpha_numerator_expansion (j r : ℝ) (hden : j+3+r≠0) :
    2*(2*(j+3)+r-(j+3))*(2*(j+3)+r-4-barrierLambda (2*(j+3)+r) (j+3))=
      j^2+3*j*r+3*j+r^2+5*r := by
  unfold barrierLambda
  have heq : 2*(j+3)+r-(j+3)=j+3+r := by ring
  rw [heq]
  field_simp [hden]
  ring

theorem certificate_lambda_positive (j r : ℝ) (hj : 0≤j) (hr : 0<r) :
    0<barrierLambda (2*(j+3)+r) (j+3) := by
  have hd : 0<j+3+r := by positivity
  have hid := certificate_lambda_expansion j r (ne_of_gt hd)
  have hpos : 0<3*j^2+3*j*r+13*j+r^2+5*r+12 := by positivity
  have hden : 0<2*(2*(j+3)+r-(j+3)) := by linarith
  nlinarith only [hid,hpos,hden]

theorem certificate_alpha_numerator_positive (j r : ℝ) (hj : 0≤j) (hr : 0<r) :
    0<2*(j+3)+r-4-barrierLambda (2*(j+3)+r) (j+3) := by
  have hd : 0<j+3+r := by positivity
  have hid := certificate_alpha_numerator_expansion j r (ne_of_gt hd)
  have hpos : 0<j^2+3*j*r+3*j+r^2+5*r := by positivity
  have hden : 0<2*(2*(j+3)+r-(j+3)) := by linarith
  nlinarith only [hid,hpos,hden]

theorem barrier_determinant_identity (N m : ℝ)
    (hN : N≠0) (hN1 : N-1≠0) (hN2 : N-2≠0)
    (hNm : N-m≠0) (hhalf : N-2*m≠0) :
    certificateA N m*certificateC N m-(certificateB N m)^2=
      N^2*certificateU N m*certificateV N m/
        ((N-2*m)^2*(N-2)^2*(N-1)) := by
  unfold certificateA certificateB certificateC certificateU certificateV
  unfold barrierAlpha barrierDelta barrierLambda envelopeScale envelopeM
  have hpoly : -(N*m*4)+N^2+m^2*4≠0 := by
    convert pow_ne_zero 2 hhalf using 1 <;> ring
  field_simp [hN,hN1,hN2,hNm,hhalf,hpoly]
  field_simp [hpoly,hhalf,hN,hN1,hN2,hNm]
  ring

theorem barrier_residual_identity (N m d z : ℝ)
    (hN1 : N-1≠0) (hN2 : N-2≠0) (hm : m≠0) (hNm : N-m≠0) :
    riccatiF N (N*(1-d)/2) m (m*(1-d)/2+envelopeM N m*z/2)
      (varianceBarrier N m d (envelopeM N m*z/2))+
      N*(envelopeM N m*z/2)*varianceBarrier N m d (envelopeM N m*z/2)*
      varianceBarrierDerivative N m d (envelopeM N m*z/2) =
      -barrierG N m*(envelopeM N m*z/2)^2*barrierW N m d z := by
  unfold riccatiF riccatiA riccatiC varianceBarrier varianceBarrierDerivative
  unfold barrierG barrierW envelopeM envelopeScale
  field_simp [hN1,hN2,hm,hNm]
  ring

theorem barrier_certificate_positive (N m d z : ℝ)
    (hm : 3 ≤ m) (hhalf : 2*m < N)
    (hd : 0 ≤ d) (hdelta : d ≤ barrierDelta N m)
    (hE : 0 ≤ admissibilityE N m d z) :
    0 < barrierW N m d z := by
  have hN : 0 < N := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hN2 : 0 < N-2 := by linarith
  have hNm : 0 < N-m := by linarith
  have hgap : 0 < N-2*m := by linarith
  have hrepr : 2*m+(N-2*m)=N := by ring
  have hmrepr : (m-3)+3=m := by ring
  have hj : 0 ≤ m-3 := by linarith
  have hlam : 0 < barrierLambda N m := by
    simpa only [hrepr, hmrepr] using
      certificate_lambda_positive (m-3) (N-2*m) hj hgap
  have han : 0 < N-4-barrierLambda N m := by
    simpa only [hrepr, hmrepr] using
      certificate_alpha_numerator_positive (m-3) (N-2*m) hj hgap
  have hdel : 0 < barrierDelta N m := div_pos hgap hN
  have halpha : 0 < barrierAlpha N m :=
    div_pos han (sq_pos_of_pos hdel)
  have hA : 0 < certificateA N m := by
    unfold certificateA
    positivity
  have hU : 0 < certificateU N m := by
    simpa only [hrepr, hmrepr] using
      certificate_U_positive (m-3) (N-2*m) hj hgap.le
  have hV : 0 < certificateV N m := by
    simpa only [hrepr, hmrepr] using
      certificate_V_positive (m-3) (N-2*m) hj hgap
  have hdet : 0 < certificateA N m*certificateC N m-(certificateB N m)^2 := by
    rw [barrier_determinant_identity N m (ne_of_gt hN) (ne_of_gt hN1)
      (ne_of_gt hN2) (ne_of_gt hNm) (ne_of_gt hgap)]
    positivity
  by_cases heq : d=0 ∧ z=0
  · rcases heq with ⟨rfl,rfl⟩
    simp only [barrierW, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_zero, add_zero, sub_zero]
    linarith
  · have hne : d≠0 ∨ z≠0 := by
      by_cases hd0 : d=0
      · exact Or.inr (fun hz0 => heq ⟨hd0,hz0⟩)
      · exact Or.inl hd0
    have hq := quadratic_form_positive (certificateA N m) (certificateB N m)
      (certificateC N m) d z hA hdet hne
    have hs1 := mul_nonneg hlam.le hE
    have hs2 : 0 ≤ barrierAlpha N m*((barrierDelta N m)^2-d^2) :=
      mul_nonneg halpha.le (by nlinarith only [hd,hdelta,hdel])
    have hid := barrier_sum_of_squares_identity N m d z (ne_of_gt hN)
      (ne_of_gt hgap) (ne_of_gt hN1) (ne_of_gt hN2) (ne_of_gt hNm)
    linarith only [hid,hq,hs1,hs2]

theorem barrier_left_endpoint_identity (N k m : ℝ)
    (hN : N≠0) (hN1 : N-1≠0) (hN2 : N-2≠0)
    (hm : m≠0) (hNm : N-m≠0) :
    varianceBarrier N m (1-2*k/N) (-m*k/N)=
      k*m*(m-1)*((N-m)*(N-2)-k*(m-1))/
      ((N-m)*(N-2)^2*(N-1)) := by
  unfold varianceBarrier envelopeM envelopeScale
  field_simp [hN,hN1,hN2,hm,hNm]
  ring

theorem barrier_right_endpoint_identity (N k m : ℝ)
    (hN : N≠0) (hN1 : N-1≠0) (hN2 : N-2≠0)
    (hm : m≠0) (hNm : N-m≠0) :
    varianceBarrier N m (1-2*k/N) (m-m*k/N)=
      m*(N-k)*(m-1)*(k*(m-1)+(N-2*m)*(N-1))/
      ((N-m)*(N-2)^2*(N-1)) := by
  unfold varianceBarrier envelopeM envelopeScale
  field_simp [hN,hN1,hN2,hm,hNm]
  ring

theorem barrier_endpoints_positive (N k m : ℝ)
    (hm : 3≤m) (hkm : m≤k) (hk : 2*k≤N) (hhalf : 2*m<N) :
    0<varianceBarrier N m (1-2*k/N) (-m*k/N) ∧
    0<varianceBarrier N m (1-2*k/N) (m-m*k/N) := by
  have hN : 0<N := by linarith
  have hN1 : 0<N-1 := by linarith
  have hN2 : 0<N-2 := by linarith
  have hm0 : 0<m := by linarith
  have hm1 : 0<m-1 := by linarith
  have hk0 : 0<k := by linarith
  have hNk : 0<N-k := by linarith
  have hNm : 0<N-m := by linarith
  have hNm1 : 0<N-m-1 := by linarith
  have hgap : 0<N-2*m := by linarith
  have hbound : k≤N-m := by linarith
  have hleft : 0<(N-m)*(N-2)-k*(m-1) := by
    have hmult := mul_le_mul_of_nonneg_right hbound hm1.le
    have hpos := mul_pos hNm hNm1
    nlinarith only [hmult,hpos]
  rw [barrier_left_endpoint_identity N k m (ne_of_gt hN) (ne_of_gt hN1)
    (ne_of_gt hN2) (ne_of_gt hm0) (ne_of_gt hNm),
    barrier_right_endpoint_identity N k m (ne_of_gt hN) (ne_of_gt hN1)
    (ne_of_gt hN2) (ne_of_gt hm0) (ne_of_gt hNm)]
  constructor <;> positivity

theorem riccati_contact_derivative_identity (N m d z w : ℝ)
    (hN : N≠0) (hN1 : N-1≠0) (hN2 : N-2≠0)
    (hm : m≠0) (hNm : N-m≠0)
    (hy : envelopeM N m*z/2≠0)
    (hP : varianceBarrier N m d (envelopeM N m*z/2)≠0)
    (hode : riccatiF N (N*(1-d)/2) m (m*(1-d)/2+envelopeM N m*z/2)
      (varianceBarrier N m d (envelopeM N m*z/2))+
      N*(envelopeM N m*z/2)*varianceBarrier N m d (envelopeM N m*z/2)*w=0) :
    w-varianceBarrierDerivative N m d (envelopeM N m*z/2)=
      barrierG N m*(envelopeM N m*z/2)*barrierW N m d z/
      (N*varianceBarrier N m d (envelopeM N m*z/2)) := by
  have hr := barrier_residual_identity N m d z hN1 hN2 hm hNm
  have hprod :
      (envelopeM N m*z/2)*((w-varianceBarrierDerivative N m d (envelopeM N m*z/2))*
        (N*varianceBarrier N m d (envelopeM N m*z/2)))=
      (envelopeM N m*z/2)*(barrierG N m*(envelopeM N m*z/2)*barrierW N m d z) := by
    linear_combination hode-hr
  exact (eq_div_iff (mul_ne_zero hN hP)).2 (mul_left_cancel₀ hy hprod)

theorem envelopeM_positive (N m : ℝ) (hm : 3≤m) (hhalf : 2*m<N) :
    0<envelopeM N m := by
  unfold envelopeM
  have hm0 : 0<m := by linarith
  have hNm : 0<N-m := by linarith
  have hN1 : 0<N-1 := by linarith
  positivity

theorem barrierG_positive (N m : ℝ) (hm : 3≤m) (hhalf : 2*m<N) :
    0<barrierG N m := by
  unfold barrierG
  have hN : 0<N := by linarith
  have hm1 : 0<m-1 := by linarith
  have hNm1 : 0<N-m-1 := by linarith
  have hN1 : 0<N-1 := by linarith
  have hN2 : 0<N-2 := by linarith
  positivity

theorem barrier_contact_W_positive (N m d z : ℝ)
    (hm : 3≤m) (hhalf : 2*m<N) (hd : 0≤d)
    (hdelta : d≤barrierDelta N m)
    (hPB : varianceBarrier N m d (envelopeM N m*z/2)≤
      (m*(1-d)/2+envelopeM N m*z/2)*
      (m-(m*(1-d)/2+envelopeM N m*z/2))/m) :
    0<barrierW N m d z := by
  have hN1 : 0<N-1 := by linarith
  have hN2 : 0<N-2 := by linarith
  have hm0 : 0<m := by linarith
  have hm1 : 0<m-1 := by linarith
  have hNm : 0<N-m := by linarith
  have hid := barrier_admissibility_identity N m d z (ne_of_gt hN1)
    (ne_of_gt hN2) (ne_of_gt hm0) (ne_of_gt hNm)
  have hcoef : 0<m*(m-1)/(4*(N-1)) := by positivity
  have hE : 0≤admissibilityE N m d z := by
    nlinarith only [hPB,hid,hcoef]
  exact barrier_certificate_positive N m d z hm hhalf hd hdelta hE

end
end ExactHoeffding
