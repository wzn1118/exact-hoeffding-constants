import ExactHoeffding.PiecewiseKLFourRates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Set

namespace ExactHoeffding
noncomputable section

/-- The first and second derivatives of the four displayed KL rates on the
open support. The second derivative is recorded as the derivative of the
first-derivative slope, which avoids any convention about iterated `deriv` at
points where a derivative may not exist. -/
theorem manuscript_A3_four_symmetric_binomial_KL_derivatives
    {N k m v : ℝ}
    (hm : 0 < m) (hmk : m ≤ k) (hk : 2*k ≤ N)
    (hhalf : 2*m < N) (hv : v ∈ Ioo 0 m) :
    let p := k/N
    let q := m/N
    let B1 := fourBinomialEnvelope1 m v
    let B2 := fourBinomialEnvelope2 k v
    let B3 := fourBinomialEnvelope3 N k m v
    let B4 := fourBinomialEnvelope4 N k m v
    (HasDerivAt (binomialKLRate m p) (binomialKLSlope m p v) v ∧
      HasDerivAt (binomialKLSlope m p) (1/B1) v) ∧
    (HasDerivAt (fourBinomialKLRate2 N k m)
        (fourBinomialKLRate2Slope N k m v) v ∧
      HasDerivAt (fourBinomialKLRate2Slope N k m) (1/B2) v) ∧
    (HasDerivAt (fourBinomialKLRate3 N k m)
        (fourBinomialKLRate3Slope N k m v) v ∧
      HasDerivAt (fourBinomialKLRate3Slope N k m) (1/B3) v) ∧
    (HasDerivAt (fourBinomialKLRate4 N k m)
        (fourBinomialKLRate4Slope N k m v) v ∧
      HasDerivAt (fourBinomialKLRate4Slope N k m) (1/B4) v) := by
  dsimp
  have hN : 0 < N := by linarith
  have hk0 : 0 < k := lt_of_lt_of_le hm hmk
  have hp : 0 < k/N := div_pos hk0 hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 (by linarith [hk])
  have hq : 0 < m/N := div_pos hm hN
  have hq1 : m/N < 1 := (div_lt_one hN).2 (by linarith [hhalf])
  have hNm : 0 < N-m := by linarith
  have hNk : 0 < N-k := by linarith [hk]
  have hkNm : k < N-m := by linarith [hk, hhalf]
  have hmNk : m < N-k := by linarith [hk, hhalf]
  have hv0 : 0 < v := hv.1
  have hvm : v < m := hv.2
  have hvk : v < k := lt_of_lt_of_le hvm hmk
  have hR1 : HasDerivAt (binomialKLRate m (k/N))
      (binomialKLSlope m (k/N) v) v :=
    binomialKLRate_hasDerivAt hm hp hp1 hv0 hvm
  have hS1 := binomialKLSlope_hasDerivAt hm hp hp1 hv0 hvm
  have hS1' : HasDerivAt (binomialKLSlope m (k/N))
      (1/fourBinomialEnvelope1 m v) v := by
    convert hS1 using 1 <;> simp [fourBinomialEnvelope1, klBinomialEnvelope]
  have hR2 : HasDerivAt (fourBinomialKLRate2 N k m)
      (fourBinomialKLRate2Slope N k m v) v := by
    have hx : 0 < v/k := div_pos hv0 hk0
    have hx1 : v/k < 1 := (div_lt_one hk0).2 hvk
    have hmap := (hasDerivAt_id v).div_const k
    have h := (bernoulliKL_hasDerivAt hq hq1 hx hx1).comp v hmap |>.const_mul k
    change HasDerivAt (fun y : ℝ => k*bernoulliKL (m/N) (y/k)) _ v
    apply h.congr_deriv
    unfold fourBinomialKLRate2Slope
    change k*(bernoulliFenchelTilt (m/N) (v/k)*(1/k)) =
      bernoulliFenchelTilt (m/N) (v/k)
    field_simp [hk0.ne']
  have hS2 : HasDerivAt (fourBinomialKLRate2Slope N k m)
      (1/fourBinomialEnvelope2 k v) v := by
    have hx : 0 < v/k := div_pos hv0 hk0
    have hx1 : v/k < 1 := (div_lt_one hk0).2 hvk
    have hmap := (hasDerivAt_id v).div_const k
    have h := (bernoulliFenchelTilt_hasDerivAt hq hq1 hx hx1).comp v hmap
    change HasDerivAt (fun y : ℝ => bernoulliFenchelTilt (m/N) (y/k)) _ v
    apply h.congr_deriv
    change 1/(v/k*(1-v/k))*(1/k) = 1/(v*(k-v)/k)
    field_simp [hk0.ne']
  have hR3 : HasDerivAt (fourBinomialKLRate3 N k m)
      (fourBinomialKLRate3Slope N k m v) v := by
    have hx : 0 < (k-v)/(N-m) := div_pos (sub_pos.mpr hvk) hNm
    have hx1 : (k-v)/(N-m) < 1 := (div_lt_one hNm).2 (by linarith)
    have hmap := ((hasDerivAt_const v k).sub (hasDerivAt_id v)).div_const (N-m)
    have h := (bernoulliKL_hasDerivAt hp hp1 hx hx1).comp v hmap |>.const_mul (N-m)
    change HasDerivAt (fun y : ℝ => (N-m)*bernoulliKL (k/N) ((k-y)/(N-m))) _ v
    apply h.congr_deriv
    change (N-m)*(bernoulliFenchelTilt (k/N) ((k-v)/(N-m))*((0-1)/(N-m))) =
      -bernoulliFenchelTilt (k/N) ((k-v)/(N-m))
    field_simp [hNm.ne']
    ring
  have hS3 : HasDerivAt (fourBinomialKLRate3Slope N k m)
      (1/fourBinomialEnvelope3 N k m v) v := by
    have hx : 0 < (k-v)/(N-m) := div_pos (sub_pos.mpr hvk) hNm
    have hx1 : (k-v)/(N-m) < 1 := (div_lt_one hNm).2 (by linarith)
    have hmap := ((hasDerivAt_const v k).sub (hasDerivAt_id v)).div_const (N-m)
    have h := ((bernoulliFenchelTilt_hasDerivAt hp hp1 hx hx1).comp v hmap).neg
    change HasDerivAt (fun y : ℝ => -bernoulliFenchelTilt (k/N) ((k-y)/(N-m))) _ v
    apply h.congr_deriv
    unfold fourBinomialEnvelope3
    change -(1/((k-v)/(N-m)*(1-(k-v)/(N-m)))*((0-1)/(N-m))) =
      1/((k-v)*(N-m-k+v)/(N-m))
    field_simp [hNm.ne']
    ring
  have hR4 : HasDerivAt (fourBinomialKLRate4 N k m)
      (fourBinomialKLRate4Slope N k m v) v := by
    have hx : 0 < (m-v)/(N-k) := div_pos (sub_pos.mpr hvm) hNk
    have hx1 : (m-v)/(N-k) < 1 := (div_lt_one hNk).2 (by linarith)
    have hmap := ((hasDerivAt_const v m).sub (hasDerivAt_id v)).div_const (N-k)
    have h := (bernoulliKL_hasDerivAt hq hq1 hx hx1).comp v hmap |>.const_mul (N-k)
    change HasDerivAt (fun y : ℝ => (N-k)*bernoulliKL (m/N) ((m-y)/(N-k))) _ v
    apply h.congr_deriv
    change (N-k)*(bernoulliFenchelTilt (m/N) ((m-v)/(N-k))*((0-1)/(N-k))) =
      -bernoulliFenchelTilt (m/N) ((m-v)/(N-k))
    field_simp [hNk.ne']
    ring
  have hS4 : HasDerivAt (fourBinomialKLRate4Slope N k m)
      (1/fourBinomialEnvelope4 N k m v) v := by
    have hx : 0 < (m-v)/(N-k) := div_pos (sub_pos.mpr hvm) hNk
    have hx1 : (m-v)/(N-k) < 1 := (div_lt_one hNk).2 (by linarith)
    have hmap := ((hasDerivAt_const v m).sub (hasDerivAt_id v)).div_const (N-k)
    have h := ((bernoulliFenchelTilt_hasDerivAt hq hq1 hx hx1).comp v hmap).neg
    change HasDerivAt (fun y : ℝ => -bernoulliFenchelTilt (m/N) ((m-y)/(N-k))) _ v
    apply h.congr_deriv
    unfold fourBinomialEnvelope4
    change -(1/((m-v)/(N-k)*(1-(m-v)/(N-k)))*((0-1)/(N-k))) =
      1/((m-v)*(N-k-m+v)/(N-k))
    field_simp [hNk.ne']
    ring
  exact ⟨⟨hR1, hS1'⟩, ⟨hR2, hS2⟩, ⟨hR3, hS3⟩, ⟨hR4, hS4⟩⟩

/-- The four symmetric binomial KL rates and their first derivatives vanish
at the common mean. -/
theorem manuscript_A3_four_symmetric_binomial_KL_mean_contact
    {N k m : ℕ}
    (hN7 : 7 ≤ N) (hm3 : 3 ≤ m) (hmk : m ≤ k)
    (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    let n : ℝ := N
    let kk : ℝ := k
    let mm : ℝ := m
    let μ : ℝ := mm*kk/n
    (binomialKLRate mm (kk/n) μ = 0 ∧
      fourBinomialKLRate2 n kk mm μ = 0 ∧
      fourBinomialKLRate3 n kk mm μ = 0 ∧
      fourBinomialKLRate4 n kk mm μ = 0) ∧
    (binomialKLSlope mm (kk/n) μ = 0 ∧
      fourBinomialKLRate2Slope n kk mm μ = 0 ∧
      fourBinomialKLRate3Slope n kk mm μ = 0 ∧
      fourBinomialKLRate4Slope n kk mm μ = 0) := by
  dsimp
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hkN : k < N := by omega
  have hmN : m < N := by omega
  have hNm : 0 < (N : ℝ) - (m : ℝ) := sub_pos.mpr (by exact_mod_cast hmN)
  have hNk : 0 < (N : ℝ) - (k : ℝ) := sub_pos.mpr (by exact_mod_cast hkN)
  have hp : 0 < (k : ℝ) / N := div_pos hkpos hNpos
  have hp1 : (k : ℝ) / N < 1 := (div_lt_one hNpos).2 (by exact_mod_cast hkN)
  have hq : 0 < (m : ℝ) / N := div_pos hmpos hNpos
  have hq1 : (m : ℝ) / N < 1 := (div_lt_one hNpos).2 (by exact_mod_cast hmN)
  have hmean1 : ((m:ℝ)*(k:ℝ)/(N:ℝ))/(m:ℝ) = (k:ℝ)/(N:ℝ) := by
    field_simp [hmpos.ne', hNpos.ne']
  have hmean2 : ((m:ℝ)*(k:ℝ)/(N:ℝ))/(k:ℝ) = (m:ℝ)/(N:ℝ) := by
    field_simp [hkpos.ne', hNpos.ne']
  have hmean3 : ((k:ℝ)-(m:ℝ)*(k:ℝ)/(N:ℝ))/((N:ℝ)-(m:ℝ)) =
      (k:ℝ)/(N:ℝ) := by
    field_simp [hNpos.ne', hNm.ne']
  have hmean4 : ((m:ℝ)-(m:ℝ)*(k:ℝ)/(N:ℝ))/((N:ℝ)-(k:ℝ)) =
      (m:ℝ)/(N:ℝ) := by
    field_simp [hNpos.ne', hNk.ne']
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold binomialKLRate
      rw [hmean1, bernoulliKL_self hp hp1]
      ring
    · unfold fourBinomialKLRate2
      rw [hmean2, bernoulliKL_self hq hq1]
      ring
    · unfold fourBinomialKLRate3
      rw [hmean3, bernoulliKL_self hp hp1]
      ring
    · unfold fourBinomialKLRate4
      rw [hmean4, bernoulliKL_self hq hq1]
      ring
  · refine ⟨?_, ?_, ?_, ?_⟩
    · unfold binomialKLSlope
      rw [hmean1]
      simp [bernoulliFenchelTilt, hp.ne', (sub_pos.mpr hp1).ne']
    · unfold fourBinomialKLRate2Slope
      rw [hmean2]
      simp [bernoulliFenchelTilt, hq.ne', (sub_pos.mpr hq1).ne']
    · unfold fourBinomialKLRate3Slope
      rw [hmean3]
      simp [bernoulliFenchelTilt, hp.ne', (sub_pos.mpr hp1).ne']
    · unfold fourBinomialKLRate4Slope
      rw [hmean4]
      simp [bernoulliFenchelTilt, hq.ne', (sub_pos.mpr hq1).ne']

/-- Typed contract for the four symmetry-related binomial KL rates in the
manuscript. The finite-population parameters are natural numbers satisfying
(A:domain), while the threshold is any real point in the full closed support.
It records the exact reciprocal-variance-envelope gaps, all comparison and
equality cases (including endpoints and the degenerate `k=m` case), and the
strict improvement of the piecewise rate away from the mean. -/
theorem manuscript_A3_four_symmetric_binomial_KL_contract
    {N k m : ℕ} {v : ℝ}
    (hN7 : 7 ≤ N) (hm3 : 3 ≤ m) (hmk : m ≤ k)
    (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (hv0 : 0 ≤ v) (hvm : v ≤ (m : ℝ)) :
    let n : ℝ := N
    let kk : ℝ := k
    let mm : ℝ := m
    let μ : ℝ := mm*kk/n
    let R1 : ℝ := binomialKLRate mm (kk/n) v
    let R2 : ℝ := fourBinomialKLRate2 n kk mm v
    let R3 : ℝ := fourBinomialKLRate3 n kk mm v
    let R4 : ℝ := fourBinomialKLRate4 n kk mm v
    let B1 : ℝ := fourBinomialEnvelope1 mm v
    let B2 : ℝ := fourBinomialEnvelope2 kk v
    let B3 : ℝ := fourBinomialEnvelope3 n kk mm v
    let B4 : ℝ := fourBinomialEnvelope4 n kk mm v
    let Rmax : ℝ := fourBinomialKLRateMax n kk mm v
    let J : ℝ := canonicalPiecewiseRate n kk mm v
    (0 ≤ B2-B1 ∧ B2-B1=(kk-mm)*v^2/(mm*kk) ∧
      0 ≤ B3-B1 ∧
        B3-B1=((kk-mm)*v^2+(n-mm-kk)*(mm-v)^2+
          mm*(kk-mm)*(n-mm-kk))/(mm*(n-mm)) ∧
      0 ≤ B4-B1 ∧ B4-B1=(n-mm-kk)*(mm-v)^2/(mm*(n-kk))) ∧
    (v ∈ Ioo 0 mm →
      (HasDerivAt (binomialKLRate mm (kk/n)) (binomialKLSlope mm (kk/n) v) v ∧
        HasDerivAt (binomialKLSlope mm (kk/n)) (1/B1) v) ∧
      (HasDerivAt (fourBinomialKLRate2 n kk mm) (fourBinomialKLRate2Slope n kk mm v) v ∧
        HasDerivAt (fourBinomialKLRate2Slope n kk mm) (1/B2) v) ∧
      (HasDerivAt (fourBinomialKLRate3 n kk mm) (fourBinomialKLRate3Slope n kk mm v) v ∧
        HasDerivAt (fourBinomialKLRate3Slope n kk mm) (1/B3) v) ∧
      (HasDerivAt (fourBinomialKLRate4 n kk mm) (fourBinomialKLRate4Slope n kk mm v) v ∧
        HasDerivAt (fourBinomialKLRate4Slope n kk mm) (1/B4) v)) ∧
    ((binomialKLRate mm (kk/n) μ=0 ∧
      fourBinomialKLRate2 n kk mm μ=0 ∧
      fourBinomialKLRate3 n kk mm μ=0 ∧
      fourBinomialKLRate4 n kk mm μ=0) ∧
      (binomialKLSlope mm (kk/n) μ=0 ∧
        fourBinomialKLRate2Slope n kk mm μ=0 ∧
        fourBinomialKLRate3Slope n kk mm μ=0 ∧
        fourBinomialKLRate4Slope n kk mm μ=0)) ∧
    (R2 ≤ R1 ∧ (R2=R1 ↔ v=μ ∨ kk=mm) ∧
      R3 ≤ R1 ∧ (R3=R1 ↔ v=μ) ∧
      R4 ≤ R1 ∧ (R4=R1 ↔ v=μ)) ∧
    (Rmax=R1 ∧ (v≠μ → Rmax<J)) := by
  dsimp
  have hN7R : (7 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN7
  have hm3R : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm3
  have hmkR : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
  have hkR : 2*(k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  have hhalfR : 2*(m : ℝ) < (N : ℝ) := by exact_mod_cast hhalf
  have hNpos : 0 < (N : ℝ) := by linarith
  have hmpos : 0 < (m : ℝ) := by linarith
  have hkpos : 0 < (k : ℝ) := by linarith
  have hNm : 0 < (N : ℝ)-(m : ℝ) := by linarith
  have hNk : 0 < (N : ℝ)-(k : ℝ) := by linarith
  have hR : 0 ≤ (N : ℝ)-(m : ℝ)-(k : ℝ) := by linarith
  have hL : 0 ≤ (k : ℝ)-(m : ℝ) := by linarith
  have hgap2 :
      fourBinomialEnvelope2 (k : ℝ) v-fourBinomialEnvelope1 (m : ℝ) v =
        ((k : ℝ)-(m : ℝ))*v^2/((m : ℝ)*(k : ℝ)) := by
    unfold fourBinomialEnvelope1 fourBinomialEnvelope2
    field_simp [hmpos.ne', hkpos.ne']
    ring
  have hgap3 :
      fourBinomialEnvelope3 (N : ℝ) (k : ℝ) (m : ℝ) v-
        fourBinomialEnvelope1 (m : ℝ) v =
        (((k : ℝ)-(m : ℝ))*v^2+
          ((N : ℝ)-(m : ℝ)-(k : ℝ))*((m : ℝ)-v)^2+
          (m : ℝ)*((k : ℝ)-(m : ℝ))*((N : ℝ)-(m : ℝ)-(k : ℝ))) /
          ((m : ℝ)*((N : ℝ)-(m : ℝ))) := by
    unfold fourBinomialEnvelope1 fourBinomialEnvelope3
    field_simp [hmpos.ne', hNm.ne']
    ring
  have hgap4 :
      fourBinomialEnvelope4 (N : ℝ) (k : ℝ) (m : ℝ) v-
        fourBinomialEnvelope1 (m : ℝ) v =
        ((N : ℝ)-(m : ℝ)-(k : ℝ))*((m : ℝ)-v)^2/
          ((m : ℝ)*((N : ℝ)-(k : ℝ))) := by
    unfold fourBinomialEnvelope1 fourBinomialEnvelope4
    field_simp [hmpos.ne', hNk.ne']
    ring
  have h2nonneg : 0 ≤ fourBinomialEnvelope2 (k : ℝ) v-
      fourBinomialEnvelope1 (m : ℝ) v := by
    rw [hgap2]
    exact div_nonneg (mul_nonneg hL (sq_nonneg v)) (mul_nonneg hmpos.le hkpos.le)
  have h3nonneg : 0 ≤ fourBinomialEnvelope3 (N : ℝ) (k : ℝ) (m : ℝ) v-
      fourBinomialEnvelope1 (m : ℝ) v := by
    rw [hgap3]
    apply div_nonneg
    · have hv2 : 0 ≤ v^2 := sq_nonneg v
      have hmv2 : 0 ≤ ((m : ℝ)-v)^2 := sq_nonneg ((m : ℝ)-v)
      have hterms : 0 ≤ ((k : ℝ)-(m : ℝ))*v^2 := mul_nonneg hL hv2
      have hterms2 : 0 ≤ ((N : ℝ)-(m : ℝ)-(k : ℝ))*((m : ℝ)-v)^2 :=
        mul_nonneg hR hmv2
      have hterms3 : 0 ≤ (m : ℝ)*((k : ℝ)-(m : ℝ))*
          ((N : ℝ)-(m : ℝ)-(k : ℝ)) := by
        exact mul_nonneg (mul_nonneg hmpos.le hL) hR
      linarith
    · exact mul_nonneg hmpos.le hNm.le
  have h4nonneg : 0 ≤ fourBinomialEnvelope4 (N : ℝ) (k : ℝ) (m : ℝ) v-
      fourBinomialEnvelope1 (m : ℝ) v := by
    rw [hgap4]
    exact div_nonneg (mul_nonneg hR (sq_nonneg ((m : ℝ)-v)))
      (mul_nonneg hmpos.le hNk.le)
  have hvSupport : v ∈ Icc (0 : ℝ) (m : ℝ) := ⟨hv0, hvm⟩
  have hRate := fourBinomialKLRate_comparisons hNpos hmpos hmkR
      (show (k : ℝ) ≤ (N : ℝ)/2 by linarith [hkR]) hhalfR hvSupport
  have hMax := fourBinomialKLRateMax_eq_R1 hNpos hmpos hmkR
      (show (k : ℝ) ≤ (N : ℝ)/2 by linarith [hkR]) hhalfR hvSupport
  have hStrict := canonicalPiecewiseRate_strict_improves_fourBinomialKLRateMax
      hm3R hmkR hkR hhalfR hv0 hvm
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact h2nonneg
    · exact hgap2
    · exact h3nonneg
    · exact hgap3
    · exact h4nonneg
    · exact hgap4
  · intro hvInterior
    have hderiv := manuscript_A3_four_symmetric_binomial_KL_derivatives
      hmpos hmkR hkR hhalfR hvInterior
    exact hderiv
  · exact manuscript_A3_four_symmetric_binomial_KL_mean_contact
      hN7 hm3 hmk hk hhalf
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact hRate.1.1
      · exact hRate.1.2
      · exact hRate.2.1.1
      · exact hRate.2.1.2
      · exact hRate.2.2.1
      · exact hRate.2.2.2
    · refine ⟨hMax, ?_⟩
      intro hvμ
      exact hStrict hvμ

end
end ExactHoeffding
