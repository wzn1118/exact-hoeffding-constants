import ExactHoeffding.RiccatiBarrier
import ExactHoeffding.WholeLineCrossing

open Filter Set
open scoped Topology

namespace ExactHoeffding
noncomputable section

/-- The polynomial certificate and crossing theorem apply directly to a
variance flow in the tilt coordinate. No inverse mean map is needed. -/
theorem variance_barrier_of_riccati_flow
    (N m d : ℝ) (u v : ℝ→ℝ)
    (hm : 3≤m) (hhalf : 2*m<N) (hd : 0≤d) (hdelta : d≤barrierDelta N m)
    (hdu : ∀t, HasDerivAt u (v t) t) (hdv : ∀t, DifferentiableAt ℝ v t)
    (hv : ∀t, 0<v t)
    (hPB : ∀t, v t≤u t*(m-u t)/m)
    (hu0 : u 0=m*(1-d)/2)
    (hv0 : v 0=varianceBarrier N m d 0)
    (huBot : Tendsto u atBot (𝓝 0)) (huTop : Tendsto u atTop (𝓝 m))
    (hvBot : Tendsto v atBot (𝓝 0)) (hvTop : Tendsto v atTop (𝓝 0))
    (hleft : 0<varianceBarrier N m d (-m*(1-d)/2))
    (hright : 0<varianceBarrier N m d (m-m*(1-d)/2))
    (hode : ∀t, riccatiF N (N*(1-d)/2) m (u t) (v t)+
      N*(u t-m*(1-d)/2)*deriv v t=0) :
    (∀t, v t≤varianceBarrier N m d (u t-m*(1-d)/2)) ∧
    (∀t, v t=varianceBarrier N m d (u t-m*(1-d)/2) ↔ t=0) := by
  let μ := m*(1-d)/2
  let y : ℝ→ℝ := fun t => u t-μ
  let f : ℝ→ℝ := fun t => v t-varianceBarrier N m d (y t)
  let f' : ℝ→ℝ := fun t => deriv v t-varianceBarrierDerivative N m d (y t)*v t
  have hN : 0<N := by linarith
  have hN1 : 0<N-1 := by linarith
  have hN2 : 0<N-2 := by linarith
  have hm0 : 0<m := by linarith
  have hNm : 0<N-m := by linarith
  have hM := envelopeM_positive N m hm hhalf
  have hG := barrierG_positive N m hm hhalf
  have hmono : StrictMono u := strictMono_of_hasDerivAt_pos hdu hv
  have hy0 : y 0=0 := by dsimp [y,μ]; rw [hu0]; ring
  have hfd (t : ℝ) : HasDerivAt f (f' t) t := by
    exact (hdv t).hasDerivAt.sub
      ((varianceBarrier_hasDerivAt N m d (y t)).comp t ((hdu t).sub_const μ))
  have hfc : Continuous f := continuous_iff_continuousAt.mpr (fun t => (hfd t).continuousAt)
  have hf0 : f 0=0 := by dsimp [f]; rw [hy0,hv0]; ring
  have hb : Tendsto f atBot (𝓝 (-varianceBarrier N m d (-μ))) := by
    have hyb : Tendsto y atBot (𝓝 (-μ)) := by
      simpa only [zero_sub,y] using huBot.sub_const μ
    have hp := (varianceBarrier_hasDerivAt N m d (-μ)).continuousAt.tendsto.comp
      hyb
    simpa only [zero_sub,Function.comp_apply,Pi.sub_apply,f,y] using hvBot.sub hp
  have ht : Tendsto f atTop (𝓝 (-varianceBarrier N m d (m-μ))) := by
    have hp := (varianceBarrier_hasDerivAt N m d (m-μ)).continuousAt.tendsto.comp
      (huTop.sub_const μ)
    simpa only [zero_sub,Function.comp_apply,Pi.sub_apply,f,y] using hvTop.sub hp
  have hcontact (t : ℝ) (ht0 : t≠0) (hf : f t=0) :
      f' t=barrierG N m*y t*barrierW N m d (2*y t/envelopeM N m)/N := by
    let z := 2*y t/envelopeM N m
    have he : envelopeM N m*z/2=y t := by dsimp [z]; field_simp
    have hyne : y t≠0 := by
      intro hy
      have huu : u t=u 0 := by dsimp [y] at hy; rw [hu0]; dsimp [μ] at hy; linarith
      exact ht0 (hmono.injective huu)
    have hp : v t=varianceBarrier N m d (y t) := sub_eq_zero.mp hf
    have hue : μ+y t=u t := by dsimp [y]; ring
    have ho : riccatiF N (N*(1-d)/2) m
        (m*(1-d)/2+envelopeM N m*z/2)
        (varianceBarrier N m d (envelopeM N m*z/2))+
        N*(envelopeM N m*z/2)*deriv v t=0 := by
      rw [he,← hp]
      change riccatiF N (N*(1-d)/2) m (μ+y t) (v t)+N*(y t)*deriv v t=0
      rw [hue]
      exact hode t
    have hh := riccati_time_contact_identity N m d z (deriv v t)
      (ne_of_gt hN) (ne_of_gt hN1) (ne_of_gt hN2) (ne_of_gt hm0)
      (ne_of_gt hNm) (by rw [he]; exact hyne) ho
    rw [he,← hp] at hh
    exact hh
  have hW (t : ℝ) (hf : f t=0) :
      0<barrierW N m d (2*y t/envelopeM N m) := by
    have he : envelopeM N m*(2*y t/envelopeM N m)/2=y t := by field_simp
    have hp : v t=varianceBarrier N m d (y t) := sub_eq_zero.mp hf
    apply barrier_contact_W_positive N m d _ hm hhalf hd hdelta
    rw [he,← hp]
    have hue : m*(1-d)/2+y t=u t := by dsimp [y,μ]; ring
    rw [hue]
    exact hPB t
  have hsignL (t : ℝ) (ht0 : t<0) (hf : f t=0) : f' t<0 := by
    rw [hcontact t (ne_of_lt ht0) hf]
    have hy : y t<0 := by have hh := hmono ht0; rw [hu0] at hh; exact sub_neg.mpr hh
    exact div_neg_of_neg_of_pos
      (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hG hy) (hW t hf)) hN
  have hsignR (t : ℝ) (ht0 : 0<t) (hf : f t=0) : 0<f' t := by
    rw [hcontact t (ne_of_gt ht0) hf]
    have hy : 0<y t := by have hh := hmono ht0; rw [hu0] at hh; exact sub_pos.mpr hh
    exact div_pos (mul_pos (mul_pos hG hy) (hW t hf)) hN
  have hl : -varianceBarrier N m d (-μ)<0 := by
    apply neg_neg_of_pos
    have he : -μ= -m*(1-d)/2 := by dsimp [μ]; ring
    rw [he]
    exact hleft
  have hr : -varianceBarrier N m d (m-μ)<0 := neg_neg_of_pos hright
  have hc := whole_line_crossing_barrier_of_limits hfc hf0 hb ht hl hr
    (fun t _ _ => hfd t) hsignL hsignR
  exact ⟨fun t => sub_nonpos.mp (hc.1 t),fun t => by
    rw [← sub_eq_zero]
    exact hc.2 t⟩

end
end ExactHoeffding
