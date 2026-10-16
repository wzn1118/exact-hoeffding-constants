import ExactHoeffding.PiecewiseKLStrict
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set
open scoped Topology

namespace ExactHoeffding
noncomputable section

/-- Bennett's dimensionless kernel. -/
def bennettKernel (z : ℝ) : ℝ := (1+z)*Real.log (1+z)-z

/-- Bernstein's dimensionless rate kernel. -/
def bernsteinKernel (z : ℝ) : ℝ := 3*z^2/(2*(z+3))

def bennettRate (v₀ x : ℝ) : ℝ := v₀*bennettKernel (x/v₀)
def bernsteinRate (v₀ x : ℝ) : ℝ := x^2/(2*(v₀+x/3))

/-- Bennett rate with the exact finite-population variance proxy. -/
def hypergeomBennettRate (N k m : ℕ) (v : ℝ) : ℝ :=
  bennettRate
    (envelopeM (N : ℝ) (m : ℝ) * ((k : ℝ) / N) * (1 - (k : ℝ) / N))
    |v - (m : ℝ) * k / N|

/-- Bernstein rate with the same exact finite-population variance proxy. -/
def hypergeomBernsteinRate (N k m : ℕ) (v : ℝ) : ℝ :=
  bernsteinRate
    (envelopeM (N : ℝ) (m : ℝ) * ((k : ℝ) / N) * (1 - (k : ℝ) / N))
    |v - (m : ℝ) * k / N|

private lemma bennettRate_hasDerivAt {v₀ x : ℝ} (hv₀ : 0 < v₀) (hx : 0 < x) :
    HasDerivAt (bennettRate v₀) (Real.log (1+x/v₀)) x := by
  have harg : HasDerivAt (fun z : ℝ => 1+z/v₀) (1/v₀) x := by
    simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using
      ((hasDerivAt_id x).div_const v₀).const_add 1
  have hmul := (Real.hasDerivAt_mul_log (by positivity : 1+x/v₀ ≠ 0)).comp x harg
  have hsub := hmul.sub ((hasDerivAt_id x).div_const v₀)
  have h := hsub.const_mul v₀
  change HasDerivAt (fun z : ℝ => v₀*((1+z/v₀)*Real.log (1+z/v₀)-z/v₀)) _ x
  apply h.congr_deriv
  field_simp [hv₀.ne']
  ring

private lemma scaledKLRate_strict_bennett_right
    {M p a μ y : ℝ} (hM : 0 < M) (ha : 0 < a) (hp : 0 < p) (hp1 : p < 1)
    (had : a * (1 - 2*p) < 1) (hy : 0 < y)
    (hθ : p + a*y/M ∈ Ioo 0 1) :
    bennettRate (M*p*(1-p)) y < scaledKLRate M p a μ (μ+y) := by
  let v₀ : ℝ := M*p*(1-p)
  let P : ℝ → ℝ := fun z => M*(p+a*z/M)*(1-(p+a*z/M))
  have hv₀ : 0 < v₀ := by dsimp [v₀]; positivity
  have haM : 0 < a/M := div_pos ha hM
  have hθz : ∀ z ∈ Icc (0:ℝ) y, p+a*z/M ∈ Ioo 0 1 := by
    intro z hz
    have hzy : a*z/M ≤ a*y/M := by
      apply (div_le_iff₀ hM).2
      calc
        a*z ≤ a*y := mul_le_mul_of_nonneg_left hz.2 ha.le
        _ = a*y/M*M := by field_simp [hM.ne']
    constructor
    · have hzterm : 0 ≤ a*z/M := div_nonneg (mul_nonneg ha.le hz.1) hM.le
      nlinarith [hp]
    · linarith [hθ.2]
  have hP : ∀ z ∈ Ioc (0:ℝ) y, 0 < P z ∧ P z < v₀+z := by
    intro z hz
    have hθz' := hθz z ⟨hz.1.le, hz.2⟩
    have hPpos : 0 < P z := by
      dsimp [P]
      exact mul_pos (mul_pos hM hθz'.1) (sub_pos.mpr hθz'.2)
    have hid : P z = v₀ + a*(1-2*p)*z-a^2/M*z^2 := by
      dsimp [P, v₀]
      field_simp [hM.ne']
      ring
    constructor
    · exact hPpos
    · rw [hid]
      have hzsq : 0 ≤ z^2 := sq_nonneg z
      have ha2 : 0 ≤ a^2/M := by positivity
      have hlin : a*(1-2*p)*z < z := by
        simpa using (mul_lt_mul_of_pos_right had hz.1)
      nlinarith
  have hcont_scaled : Continuous (scaledKLRate M p a μ) := by
    exact continuous_const.mul ((bernoulliKL_continuous p hp hp1).comp
      (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).div_const M)))
  have hcont_bennett : ContinuousOn (fun z : ℝ => bennettRate v₀ z) (Icc 0 y) := by
    have harg : ContinuousOn (fun z : ℝ => 1+z/v₀) (Icc 0 y) := by fun_prop
    have hlog : ContinuousOn (fun z : ℝ => Real.log (1+z/v₀)) (Icc 0 y) := by
      apply harg.log
      intro z hz
      have : 0 < 1+z/v₀ := by
        have hz0 : 0 ≤ z := hz.1
        positivity
      exact ne_of_gt this
    change ContinuousOn (fun z : ℝ =>
      v₀*((1+z/v₀)*Real.log (1+z/v₀)-z/v₀)) (Icc 0 y)
    exact continuousOn_const.mul ((harg.mul hlog).sub
      (continuous_id.div_const v₀).continuousOn)
  have hcont_scaled_shift : ContinuousOn
      (fun z : ℝ => scaledKLRate M p a μ (μ+z)) (Icc 0 y) := by
    have h := hcont_scaled.comp_continuousOn
      (s := Icc (0:ℝ) y) (f := fun z : ℝ => μ+z)
      (by fun_prop)
    simpa [Function.comp_def] using h
  have hcont : ContinuousOn
      (fun z : ℝ => scaledKLRate M p a μ (μ+z)-bennettRate v₀ z) (Icc 0 y) := by
    exact hcont_scaled_shift.sub hcont_bennett
  let s : ℝ → ℝ := fun z =>
    scaledKLSlope M p a μ (μ+z)-Real.log (1+z/v₀)
  have hsderiv : ∀ z ∈ Ico (0:ℝ) y, HasDerivAt s
      (1/(P z)-1/(v₀+z)) z := by
    intro z hz
    have hθz' : p+a*((μ+z)-μ)/M ∈ Ioo 0 1 := by
      simpa using hθz z ⟨hz.1, hz.2.le⟩
    have hscaled := scaledKLSlope_hasDerivAt hM ha hp hp1 hθz'
    have harg : HasDerivAt (fun z : ℝ => 1+z/v₀) (1/v₀) z := by
      simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using
        ((hasDerivAt_id z).div_const v₀).const_add 1
    have hlog := harg.log (by
      have : 0 < 1+z/v₀ := by
        have hz0 : 0 ≤ z := hz.1
        positivity
      exact ne_of_gt this)
    have h := hscaled.comp z (by
      simpa [add_comm, add_left_comm, add_assoc] using (hasDerivAt_id z).add_const μ)
    apply (h.sub hlog).congr_deriv
    dsimp [s, P, v₀]
    field_simp [hM.ne', hv₀.ne', hp.ne', sub_ne_zero.mpr hp1.ne']
    ring
  have hs0 : s 0 = 0 := by
    dsimp [s]
    simp [scaledKLSlope, bernoulliFenchelTilt, v₀]
  have hf0 : (fun z : ℝ => scaledKLRate M p a μ (μ+z)-bennettRate v₀ z) 0 = 0 := by
    have hkl : bernoulliKL p p = 0 := by
      unfold bernoulliKL
      rw [div_self hp.ne', div_self (sub_ne_zero.mpr hp1.ne')]
      simp
    simp [scaledKLRate, bennettRate, bennettKernel, v₀, hkl]
  have hds : ∀ z ∈ Ioo (0:ℝ) y, 0 < 1/(P z)-1/(v₀+z) := by
    intro z hz
    have hPz := hP z ⟨hz.1, hz.2.le⟩
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hPz.1 hPz.2)
  have hfd : ∀ z ∈ Ioo (0:ℝ) y, HasDerivAt
      (fun z : ℝ => scaledKLRate M p a μ (μ+z)-bennettRate v₀ z) (s z) z := by
    intro z hz
    have hθz' : p+a*((μ+z)-μ)/M ∈ Ioo 0 1 := by
      simpa using hθz z ⟨hz.1.le, hz.2.le⟩
    have hscaled := scaledKLRate_hasDerivAt hM ha hp hp1 hθz'
    have hcomp := hscaled.comp z (by
      simpa [add_comm, add_left_comm, add_assoc] using (hasDerivAt_id z).add_const μ)
    have hben := bennettRate_hasDerivAt hv₀ hz.1
    apply (hcomp.sub hben).congr_deriv
    dsimp [s]
    ring
  have h := positive_from_contact_right (f := fun z : ℝ =>
      scaledKLRate M p a μ (μ+z)-bennettRate v₀ z) (s := s)
      (ds := fun z => 1/(P z)-1/(v₀+z)) hy hcont hfd hsderiv hds hf0 hs0
  have hstrict := h y ⟨hy, le_rfl⟩
  exact sub_pos.mp hstrict

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

private lemma hypergeom_ad_lt_one (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    envelopeScale (N : ℝ) (m : ℝ) * (1 - 2*((k : ℝ)/N)) < 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have ha0 : 0 ≤ envelopeScale (N : ℝ) (m : ℝ) := by
    unfold envelopeScale
    apply div_nonneg
    · have hcast : (2:ℝ)*(m:ℝ) ≤ N := by exact_mod_cast (show 2*m ≤ N by omega)
      nlinarith
    · have hcast : (2:ℝ) < N := by exact_mod_cast (show 2 < N by omega)
      nlinarith
  have ha1 : envelopeScale (N : ℝ) (m : ℝ) < 1 := by
    unfold envelopeScale
    have hN2 : (0:ℝ) < N-2 := by
      have hcast : (2:ℝ) < N := by exact_mod_cast (show 2 < N by omega)
      linarith
    apply (div_lt_one hN2).2
    have : (2:ℝ) < 2*m := by exact_mod_cast (show 2 < 2*m by omega)
    linarith
  have hd0 : 0 ≤ 1 - 2*((k : ℝ)/N) := by
    apply sub_nonneg.mpr
    have hrewrite : (2:ℝ)*((k:ℝ)/N) = (2*(k:ℝ))/N := by ring
    rw [hrewrite]
    apply (div_le_iff₀ hN).2
    norm_num
    exact_mod_cast hk
  have hd1 : 1 - 2*((k : ℝ)/N) < 1 := by
    have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have : 0 < 2*((k : ℝ)/N) := by positivity
    linarith
  have hprod : 0 < (1-envelopeScale (N : ℝ) (m : ℝ)) *
      (1-(1-2*((k : ℝ)/N))) :=
    mul_pos (sub_pos.mpr ha1) (by positivity)
  nlinarith [hprod]

/-- Actual finite-population Bennett comparison for the upper tail.  The
variance proxy is `M*p*(1-p)` and the proof uses the explicit quadratic
variance barrier `M*p*(1-p)+a*(1-2*p)y-a^2 y^2/M`. -/
theorem hypergeomBennettRate_lt_canonicalPiecewiseRate_upper (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hvμ : (m:ℝ)*k/N < v) (hvm : v ≤ m) :
    hypergeomBennettRate N k m v < canonicalPiecewiseRate N k m v := by
  have hv0 : 0 ≤ v := by
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have : 0 < (m:ℝ)*k/N := by positivity
    linarith
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hM : 0 < envelopeM (N:ℝ) (m:ℝ) := envelopeM_positive _ _ hmR hhR
  have ha : 0 < envelopeScale (N:ℝ) (m:ℝ) := by
    unfold envelopeScale
    apply div_pos
    · have hcast : (2:ℝ)*(m:ℝ) < N := by exact_mod_cast hhalf
      nlinarith
    · have : 2 < N := by omega
      linarith
  have hp : 0 < (k:ℝ)/N := by
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have hp1 : (k:ℝ)/N < 1 := by
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    apply (div_lt_one hN).2
    have : k < N := by omega
    exact_mod_cast this
  let μ : ℝ := (m:ℝ)*(k:ℝ)/(N:ℝ)
  let y : ℝ := v-μ
  have hy : 0 < y := by dsimp [y,μ]; linarith
  have hθ0 := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hv0 hvm
  have hθ : (k:ℝ)/(N:ℝ) + envelopeScale (N:ℝ) (m:ℝ)*y/
      envelopeM (N:ℝ) (m:ℝ) ∈ Ioo 0 1 := by
    simpa [μ, y] using hθ0
  have hb := scaledKLRate_strict_bennett_right (μ := μ) hM ha hp hp1
    (hypergeom_ad_lt_one N k m hm hmk hk hhalf) hy hθ
  have hquad := canonicalPiecewiseRate_quadratic_comparison
    (N := (N:ℝ)) (k := (k:ℝ)) (m := (m:ℝ)) (v := v)
    hmR hmkR hkR hhR hv0 hvm
  have hIP : scaledKLRate (envelopeM (N:ℝ) (m:ℝ)) ((k:ℝ)/N)
      (envelopeScale (N:ℝ) (m:ℝ)) ((m:ℝ)*(k:ℝ)/(N:ℝ)) v ≤
      canonicalPiecewiseRate (N:ℝ) (k:ℝ) (m:ℝ) v := hquad.1
  have hb' : hypergeomBennettRate N k m v <
      scaledKLRate (envelopeM (N:ℝ) (m:ℝ)) ((k:ℝ)/N)
        (envelopeScale (N:ℝ) (m:ℝ)) ((m:ℝ)*k/N) v := by
    simpa [hypergeomBennettRate, y, μ, abs_of_pos (sub_pos.mpr hvμ)] using hb
  exact hb'.trans_le hIP

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

private lemma scaledKLRate_strict_bennett_left
    {M p a μ y : ℝ} (hM : 0 < M) (ha : 0 < a) (hp : 0 < p) (hp1 : p < 1)
    (had0 : 0 ≤ a * (1 - 2*p)) (hy : 0 < y)
    (hθ : p-a*y/M ∈ Ioo 0 1) :
    bennettRate (M*p*(1-p)) y < scaledKLRate M p a μ (μ-y) := by
  let v₀ : ℝ := M*p*(1-p)
  let P : ℝ → ℝ := fun z => M*(p-a*z/M)*(1-(p-a*z/M))
  have hv₀ : 0 < v₀ := by dsimp [v₀]; positivity
  have haM : 0 < a/M := div_pos ha hM
  have hθz : ∀ z ∈ Icc (0:ℝ) y, p-a*z/M ∈ Ioo 0 1 := by
    intro z hz
    have hzy : a*z/M ≤ a*y/M := by
      apply (div_le_iff₀ hM).2
      calc
        a*z ≤ a*y := mul_le_mul_of_nonneg_left hz.2 ha.le
        _ = a*y/M*M := by field_simp [hM.ne']
    constructor
    · linarith [hθ.1]
    · have hzterm : 0 ≤ a*z/M := div_nonneg (mul_nonneg ha.le hz.1) hM.le
      nlinarith [hp1]
  have hP : ∀ z ∈ Ioc (0:ℝ) y, 0 < P z ∧ P z < v₀+z := by
    intro z hz
    have hθz' := hθz z ⟨hz.1.le, hz.2⟩
    have hPpos : 0 < P z := by
      dsimp [P]
      exact mul_pos (mul_pos hM hθz'.1) (sub_pos.mpr hθz'.2)
    have hid : P z = v₀ - a*(1-2*p)*z-a^2/M*z^2 := by
      dsimp [P, v₀]
      field_simp [hM.ne']
      ring
    constructor
    · exact hPpos
    · rw [hid]
      have hzsq : 0 ≤ z^2 := sq_nonneg z
      have ha2 : 0 ≤ a^2/M := by positivity
      have hlin : 0 ≤ a*(1-2*p)*z := mul_nonneg had0 hz.1.le
      have hzpos : 0 < z := hz.1
      nlinarith
  have hcont_scaled : Continuous (scaledKLRate M p a μ) := by
    exact continuous_const.mul ((bernoulliKL_continuous p hp hp1).comp
      (continuous_const.add ((continuous_const.mul (continuous_id.sub continuous_const)).div_const M)))
  have hcont_bennett : ContinuousOn (fun z : ℝ => bennettRate v₀ z) (Icc 0 y) := by
    have harg : ContinuousOn (fun z : ℝ => 1+z/v₀) (Icc 0 y) := by fun_prop
    have hlog : ContinuousOn (fun z : ℝ => Real.log (1+z/v₀)) (Icc 0 y) := by
      apply harg.log
      intro z hz
      have : 0 < 1+z/v₀ := by
        have hz0 : 0 ≤ z := hz.1
        positivity
      exact ne_of_gt this
    change ContinuousOn (fun z : ℝ =>
      v₀*((1+z/v₀)*Real.log (1+z/v₀)-z/v₀)) (Icc 0 y)
    exact continuousOn_const.mul ((harg.mul hlog).sub
      (continuous_id.div_const v₀).continuousOn)
  have hcont_scaled_shift : ContinuousOn
      (fun z : ℝ => scaledKLRate M p a μ (μ-z)) (Icc 0 y) := by
    have h := hcont_scaled.comp_continuousOn
      (s := Icc (0:ℝ) y) (f := fun z : ℝ => μ-z)
      (by fun_prop)
    simpa [Function.comp_def] using h
  have hcont : ContinuousOn
      (fun z : ℝ => scaledKLRate M p a μ (μ-z)-bennettRate v₀ z) (Icc 0 y) := by
    exact hcont_scaled_shift.sub hcont_bennett
  let s : ℝ → ℝ := fun z =>
    -scaledKLSlope M p a μ (μ-z)-Real.log (1+z/v₀)
  have hsderiv : ∀ z ∈ Ico (0:ℝ) y, HasDerivAt s
      (1/(P z)-1/(v₀+z)) z := by
    intro z hz
    have hθz' : p+a*((μ-z)-μ)/M ∈ Ioo 0 1 := by
      convert hθz z ⟨hz.1, hz.2.le⟩ using 1 <;> ring
    have hscaled := scaledKLSlope_hasDerivAt hM ha hp hp1 hθz'
    have harg : HasDerivAt (fun z : ℝ => 1+z/v₀) (1/v₀) z := by
      simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using
        ((hasDerivAt_id z).div_const v₀).const_add 1
    have hlog := harg.log (by
      have hz0 : 0 ≤ z := hz.1
      have : 0 < 1+z/v₀ := by positivity
      exact ne_of_gt this)
    have hargμ : HasDerivAt (fun z : ℝ => μ-z) (-1) z := by
      have htmp := (hasDerivAt_id z).neg.const_add μ
      change HasDerivAt (fun z : ℝ => μ + -z) (-1) z
      apply htmp.congr_deriv
      norm_num
    have h := hscaled.comp z hargμ
    apply (h.neg.sub hlog).congr_deriv
    dsimp [s, P, v₀]
    field_simp [hM.ne', hv₀.ne', hp.ne', sub_ne_zero.mpr hp1.ne']
    ring
  have hs0 : s 0 = 0 := by
    dsimp [s]
    simp [scaledKLSlope, bernoulliFenchelTilt, v₀]
  have hf0 : (fun z : ℝ => scaledKLRate M p a μ (μ-z)-bennettRate v₀ z) 0 = 0 := by
    have hkl : bernoulliKL p p = 0 := by
      unfold bernoulliKL
      rw [div_self hp.ne', div_self (sub_ne_zero.mpr hp1.ne')]
      simp
    simp [scaledKLRate, bennettRate, bennettKernel, v₀, hkl]
  have hds : ∀ z ∈ Ioo (0:ℝ) y, 0 < 1/(P z)-1/(v₀+z) := by
    intro z hz
    have hPz := hP z ⟨hz.1, hz.2.le⟩
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hPz.1 hPz.2)
  have hfd : ∀ z ∈ Ioo (0:ℝ) y, HasDerivAt
      (fun z : ℝ => scaledKLRate M p a μ (μ-z)-bennettRate v₀ z) (s z) z := by
    intro z hz
    have hθz' : p+a*((μ-z)-μ)/M ∈ Ioo 0 1 := by
      convert hθz z ⟨hz.1.le, hz.2.le⟩ using 1 <;> ring
    have hscaled := scaledKLRate_hasDerivAt hM ha hp hp1 hθz'
    have hargμ : HasDerivAt (fun z : ℝ => μ-z) (-1) z := by
      have htmp := (hasDerivAt_id z).neg.const_add μ
      change HasDerivAt (fun z : ℝ => μ + -z) (-1) z
      apply htmp.congr_deriv
      norm_num
    have hcomp := hscaled.comp z hargμ
    have hben := bennettRate_hasDerivAt hv₀ hz.1
    have hsub := hcomp.sub hben
    have hfun : (fun w : ℝ => scaledKLRate M p a μ (μ-w)-bennettRate v₀ w) =
        (scaledKLRate M p a μ ∘ (fun w : ℝ => μ-w)) - bennettRate v₀ := by
      funext w
      simp [Function.comp_def]
    rw [hfun]
    apply hsub.congr_deriv
    dsimp [s]
    ring
  have h := positive_from_contact_right (f := fun z : ℝ =>
      scaledKLRate M p a μ (μ-z)-bennettRate v₀ z) (s := s)
      (ds := fun z => 1/(P z)-1/(v₀+z)) hy hcont hfd hsderiv hds hf0 hs0
  have hstrict := h y ⟨hy, le_rfl⟩
  exact sub_pos.mp hstrict

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- Actual finite-population Bennett comparison for the lower tail. -/
theorem hypergeomBennettRate_lt_canonicalPiecewiseRate_lower (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvμ : v < (m:ℝ)*k/N) :
    hypergeomBennettRate N k m v < canonicalPiecewiseRate N k m v := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hM : 0 < envelopeM (N:ℝ) (m:ℝ) := envelopeM_positive _ _ hmR hhR
  have ha : 0 < envelopeScale (N:ℝ) (m:ℝ) := by
    unfold envelopeScale
    apply div_pos
    · have hcast : (2:ℝ)*(m:ℝ) < N := by exact_mod_cast hhalf
      nlinarith
    · have hcast : (2:ℝ) < N := by exact_mod_cast (show 2 < N by omega)
      nlinarith
  have hp : 0 < (k:ℝ)/N := by
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    positivity
  have hp1 : (k:ℝ)/N < 1 := by
    have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    apply (div_lt_one hN).2
    have : k < N := by omega
    exact_mod_cast this
  let μ : ℝ := (m:ℝ)*(k:ℝ)/(N:ℝ)
  let y : ℝ := μ-v
  have hy : 0 < y := by dsimp [y, μ]; linarith
  have hμm : μ ≤ (m:ℝ) := by
    dsimp [μ]
    have hmpos : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hmul : (m:ℝ)*((k:ℝ)/N) ≤ m := by nlinarith [hp1]
    calc
      (m:ℝ)*(k:ℝ)/(N:ℝ) = (m:ℝ)*((k:ℝ)/N) := by ring
      _ ≤ m := hmul
  have hv_le_m : v ≤ (m:ℝ) := le_trans (le_of_lt hvμ) hμm
  have hθ0 := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hv0 hv_le_m
  have hθ : (k:ℝ)/(N:ℝ) - envelopeScale (N:ℝ) (m:ℝ)*y/
      envelopeM (N:ℝ) (m:ℝ) ∈ Ioo 0 1 := by
    have heq : (k:ℝ)/(N:ℝ) - envelopeScale (N:ℝ) (m:ℝ)*y/
        envelopeM (N:ℝ) (m:ℝ) =
        (k:ℝ)/(N:ℝ) + envelopeScale (N:ℝ) (m:ℝ) *
          (v-(m:ℝ)*(k:ℝ)/(N:ℝ)) / envelopeM (N:ℝ) (m:ℝ) := by
      dsimp [y, μ]
      ring
    rw [heq]
    exact hθ0
  have had0 : 0 ≤ envelopeScale (N:ℝ) (m:ℝ) *
      (1-2*((k:ℝ)/(N:ℝ))) := by
    have hd0 : 0 ≤ 1-2*((k:ℝ)/(N:ℝ)) := by
      apply sub_nonneg.mpr
      have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hrewrite : (2:ℝ)*((k:ℝ)/N) = (2*(k:ℝ))/N := by ring
      rw [hrewrite]
      apply (div_le_iff₀ hN).2
      norm_num
      exact_mod_cast hk
    exact mul_nonneg ha.le hd0
  have hb := scaledKLRate_strict_bennett_left (μ := μ) hM ha hp hp1 had0 hy hθ
  have hquad := canonicalPiecewiseRate_quadratic_comparison
    (N := (N:ℝ)) (k := (k:ℝ)) (m := (m:ℝ)) (v := v)
    hmR hmkR hkR hhR hv0 hv_le_m
  have hIP : scaledKLRate (envelopeM (N:ℝ) (m:ℝ)) ((k:ℝ)/N)
      (envelopeScale (N:ℝ) (m:ℝ)) ((m:ℝ)*(k:ℝ)/(N:ℝ)) v ≤
      canonicalPiecewiseRate (N:ℝ) (k:ℝ) (m:ℝ) v := hquad.1
  have hb' : hypergeomBennettRate N k m v <
      scaledKLRate (envelopeM (N:ℝ) (m:ℝ)) ((k:ℝ)/N)
        (envelopeScale (N:ℝ) (m:ℝ)) ((m:ℝ)*(k:ℝ)/(N:ℝ)) v := by
    simpa [hypergeomBennettRate, y, μ, abs_of_neg (sub_neg.mpr hvμ)] using hb
  exact hb'.trans_le hIP

end
end ExactHoeffding
