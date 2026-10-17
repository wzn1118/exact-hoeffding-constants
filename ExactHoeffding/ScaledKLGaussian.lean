import ExactHoeffding.PiecewiseKLComparison
import ExactHoeffding.JointBinomialOptimizer
import ExactHoeffding.LimitProxyStrict
import ExactHoeffding.ExactParityConstants

/-! # The Gaussian rate below the scaled Bernoulli KL envelope

Conjugation is proved at an explicit quadratic optimizer. The variance
coefficient and the target-mean rate retain their original definitions.
-/

namespace ExactHoeffding
noncomputable section

/-- The sharp Bernoulli coefficient is positive for every interior law. -/
theorem bernoulliSharpBeta_pos_interior (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < bernoulliSharpBeta p := by
  by_cases hh : p = 1/2
  · rw [hh, bernoulliSharpBeta_half]; norm_num
  · exact lt_trans (mul_pos hp (sub_pos.mpr hp1))
      (bernoulliSharpBeta_gt_variance p hp hp1 hh)

/-- Conjugating the actual sharp Bernoulli log-MGF bound gives this KL
lower bound, including target endpoints. No rate comparison is assumed. -/
theorem bernoulliKL_ge_sharp_gaussian (p θ : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (θ-p)^2 / (2*bernoulliSharpBeta p) ≤ bernoulliKL p θ := by
  let β := bernoulliSharpBeta p
  have hβ : 0 < β := bernoulliSharpBeta_pos_interior p hp hp1
  let t := (θ-p)/β
  have hf := bernoulli_fenchel_upper p θ t hp hp1 hθ0 hθ1
  have hq := bernoulli_sharp_quadratic_bound p hp.le hp1.le t
  change bernoulliCenteredLogMGF p t ≤ β*t^2/2 at hq
  have hf' : t*(θ-p)-bernoulliCenteredLogMGF p t ≤ bernoulliKL p θ := by
    convert hf using 1 <;> unfold bernoulliCenteredLogMGF <;> ring
  have hid : t*(θ-p)-β*t^2/2 = (θ-p)^2/(2*β) := by
    dsimp [t]
    field_simp [hβ.ne']
    <;> ring
  calc
    _ = t*(θ-p)-β*t^2/2 := hid.symm
    _ ≤ t*(θ-p)-bernoulliCenteredLogMGF p t := by linarith
    _ ≤ bernoulliKL p θ := hf'

/-- For an unbalanced sub-half Bernoulli law the only Gaussian contacts in
mean coordinates are its original and reflected means. -/
theorem bernoulliKL_sharp_gaussian_eq_iff_subhalf (p θ : ℝ)
    (hp : 0 < p) (hph : p < 1/2) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    bernoulliKL p θ = (θ-p)^2/(2*bernoulliSharpBeta p) ↔
      θ=p ∨ θ=1-p := by
  have hp1 : p < 1 := by linarith
  have hβ : 0 < bernoulliSharpBeta p := bernoulliSharpBeta_pos_interior p hp hp1
  have hpne : p ≠ 1/2 := by linarith
  have hL : 0 < Real.log ((1-p)/p) :=
    Real.log_pos ((one_lt_div hp).2 (by linarith))
  have hcontact : bernoulliSharpBeta p * (2*Real.log ((1-p)/p)) = 1-2*p := by
    rw [bernoulliSharpBeta_eq_formula p hpne]
    field_simp [hL.ne']
  constructor
  · intro heq
    by_cases hθp : θ=p
    · exact Or.inl hθp
    let t := (θ-p)/bernoulliSharpBeta p
    have ht : t ≠ 0 := div_ne_zero (sub_ne_zero.mpr hθp) hβ.ne'
    by_cases htc : t = 2*Real.log ((1-p)/p)
    · right
      have hh : θ-p = bernoulliSharpBeta p * (2*Real.log ((1-p)/p)) := by
        have h := (div_eq_iff hβ.ne').mp htc
        linarith
      rw [hcontact] at hh
      linarith
    · have hs := bernoulli_subhalf_quadratic_strict_away_contacts p t hp hph ht htc
      have hf := bernoulli_fenchel_upper p θ t hp hp1 hθ0 hθ1
      have hf' : t*(θ-p)-bernoulliCenteredLogMGF p t ≤ bernoulliKL p θ := by
        convert hf using 1 <;> unfold bernoulliCenteredLogMGF <;> ring
      have hid : t*(θ-p)-bernoulliSharpBeta p*t^2/2 =
          (θ-p)^2/(2*bernoulliSharpBeta p) := by
        dsimp [t]; field_simp [hβ.ne'] <;> ring
      rw [heq] at hf'
      linarith
  · rintro (rfl | rfl)
    · simp [bernoulliKL, hp.ne', (sub_pos.mpr hp1).ne']
    · have hlog : Real.log (p/(1-p)) = -Real.log ((1-p)/p) := by
        rw [Real.log_div hp.ne' (sub_pos.mpr hp1).ne',
          Real.log_div (sub_pos.mpr hp1).ne' hp.ne']
        ring
      rw [bernoulliSharpBeta_eq_formula p hpne]
      unfold bernoulliKL
      rw [show 1-(1-p)=p by ring, hlog]
      field_simp [hL.ne', (show 1-2*p ≠ 0 by linarith)]
      <;> field_simp [show 1-p*2 ≠ 0 by linarith]
      <;> ring

/-- Balanced Bernoulli KL strictly improves its quadratic tangent away
from the mean, including the two supported endpoints. -/
theorem bernoulliKL_sharp_gaussian_strict_half (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hne : θ ≠ 1/2) :
    (θ-1/2)^2/(2*bernoulliSharpBeta (1/2)) < bernoulliKL (1/2) θ := by
  let t := (θ-1/2)/bernoulliSharpBeta (1/2)
  have ht : t/2 ≠ 0 := by
    dsimp [t]; rw [bernoulliSharpBeta_half]
    intro h; apply hne; linarith
  have hcosh := real_log_cosh_lt_sq_div_two ht
  have hs : bernoulliCenteredLogMGF (1/2) t < bernoulliSharpBeta (1/2)*t^2/2 := by
    rw [bernoulli_half_centered_log_mgf_eq_log_cosh, bernoulliSharpBeta_half]
    nlinarith [hcosh]
  have hf := bernoulli_fenchel_upper (1/2) θ t (by norm_num) (by norm_num) hθ0 hθ1
  have hf' : t*(θ-1/2)-bernoulliCenteredLogMGF (1/2) t ≤ bernoulliKL (1/2) θ := by
    convert hf using 1 <;> unfold bernoulliCenteredLogMGF <;> ring
  have hid : t*(θ-1/2)-bernoulliSharpBeta (1/2)*t^2/2 =
      (θ-1/2)^2/(2*bernoulliSharpBeta (1/2)) := by
    dsimp [t]; rw [bernoulliSharpBeta_half]; ring
  linarith

/-- The scaled KL envelope dominates the Gaussian rate with its own sharp
Bernoulli coefficient, on the entire affine Bernoulli support. -/
theorem scaledKLRate_ge_sharp_gaussian (M p a μ v : ℝ)
    (hM : 0 < M) (ha : a ≠ 0) (hp : 0 < p) (hp1 : p < 1)
    (hθ : p+a*(v-μ)/M ∈ Set.Icc 0 1) :
    (v-μ)^2/(2*(M*bernoulliSharpBeta p)) ≤ scaledKLRate M p a μ v := by
  have hβ := bernoulliSharpBeta_pos_interior p hp hp1
  have h := mul_le_mul_of_nonneg_left
    (bernoulliKL_ge_sharp_gaussian p (p+a*(v-μ)/M) hp hp1 hθ.1 hθ.2)
    (show 0 ≤ M/a^2 by positivity)
  have hid : M/a^2 * ((p+a*(v-μ)/M-p)^2/(2*bernoulliSharpBeta p)) =
      (v-μ)^2/(2*(M*bernoulliSharpBeta p)) := by
    field_simp [hM.ne', ha, hβ.ne']
    <;> ring
  rw [hid] at h
  exact h

/-- For a sub-half law, the scaled Gaussian rate contacts exactly at zero
displacement and at the reflected Bernoulli target. -/
theorem scaledKLRate_sharp_gaussian_eq_iff_subhalf (M p a μ v : ℝ)
    (hM : 0 < M) (ha : a ≠ 0) (hp : 0 < p) (hph : p < 1/2)
    (hθ : p+a*(v-μ)/M ∈ Set.Icc 0 1) :
    scaledKLRate M p a μ v = (v-μ)^2/(2*(M*bernoulliSharpBeta p)) ↔
      v=μ ∨ v-μ=M*(1-2*p)/a := by
  have hp1 : p < 1 := by linarith
  have hβ := bernoulliSharpBeta_pos_interior p hp hp1
  have hid : M/a^2 * ((p+a*(v-μ)/M-p)^2/(2*bernoulliSharpBeta p)) =
      (v-μ)^2/(2*(M*bernoulliSharpBeta p)) := by
    field_simp [hM.ne', ha, hβ.ne'] <;> ring
  rw [← hid]
  unfold scaledKLRate
  rw [mul_right_inj' (show M/a^2 ≠ 0 by positivity)]
  rw [bernoulliKL_sharp_gaussian_eq_iff_subhalf p _ hp hph hθ.1 hθ.2]
  constructor
  · rintro (h | h)
    · left
      have hz : a*(v-μ)=0 := by
        have hh : a*(v-μ)/M=0 := by linarith
        exact (div_eq_zero_iff.mp hh).resolve_right hM.ne'
      exact (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha))
    · right
      apply (eq_div_iff ha).2
      have hh : a*(v-μ)/M=1-2*p := by linarith
      have hmul := (div_eq_iff hM.ne').mp hh
      nlinarith [hmul]
  · rintro (h | h)
    · left; rw [h]; simp
    · right; rw [h]; field_simp [hM.ne', ha] <;> ring

/-- The balanced scaled rate has only the zero-displacement Gaussian contact. -/
theorem scaledKLRate_sharp_gaussian_strict_half (M a μ v : ℝ)
    (hM : 0 < M) (ha : a ≠ 0) (hne : v ≠ μ)
    (hθ : 1/2+a*(v-μ)/M ∈ Set.Icc 0 1) :
    (v-μ)^2/(2*(M*bernoulliSharpBeta (1/2))) < scaledKLRate M (1/2) a μ v := by
  have hθne : 1/2+a*(v-μ)/M ≠ 1/2 := by
    intro heq
    have hh : a*(v-μ)/M = 0 := by linarith
    have hz := (div_eq_zero_iff.mp hh).resolve_right hM.ne'
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left ha))
  have h := mul_lt_mul_of_pos_left
    (bernoulliKL_sharp_gaussian_strict_half _ hθ.1 hθ.2 hθne)
    (show 0 < M/a^2 by positivity)
  have hid : M/a^2 * ((1/2+a*(v-μ)/M-1/2)^2/(2*bernoulliSharpBeta (1/2))) =
      (v-μ)^2/(2*(M*bernoulliSharpBeta (1/2))) := by
    rw [bernoulliSharpBeta_half]
    field_simp [hM.ne', ha]
    <;> ring
  rw [hid] at h
  exact h

/-- The manuscript's parity-uniform Bernoulli coefficient κ_N. -/
def parityUniformKappa (N : ℕ) : ℝ :=
  if Even N then 1 else 1/((N:ℝ)*Real.artanh (1/(N:ℝ)))

/-- The exact uniform quadratic coefficient V_* in unnormalized variance units. -/
def hypergeomUniformQuadraticVariance (N m : ℕ) : ℝ :=
  envelopeM (N:ℝ) (m:ℝ) * parityUniformKappa N / 4

private theorem bernoulliSharpBeta_fraction_imbalance (N k : ℝ)
    (hN : N ≠ 0) (hk : k ≠ 0) (hph : k/N < 1/2) :
    bernoulliSharpBeta (k/N) = imbalanceFactor (1-2*k/N)/4 := by
  rw [bernoulliSharpBeta_eq_formula _ (by linarith)]
  unfold imbalanceFactor
  rw [logOdds_success_fraction N k hN hk]
  ring

/-- On an odd population lattice the sharp Bernoulli coefficient is at
most its nearest-central value; the equality condition is exact. -/
theorem bernoulliSharpBeta_odd_lattice (n k : ℕ)
    (hn : 0 < n) (hk : 0 < k) (hkn : k ≤ n) :
    bernoulliSharpBeta ((k:ℝ)/((2*n+1:ℕ):ℝ)) ≤ parityUniformKappa (2*n+1)/4 ∧
      (bernoulliSharpBeta ((k:ℝ)/((2*n+1:ℕ):ℝ)) =
        parityUniformKappa (2*n+1)/4 ↔ k=n) := by
  let N : ℝ := ((2*n+1:ℕ):ℝ)
  have hN : 1 < N := by dsimp [N]; exact_mod_cast (show 1<2*n+1 by omega)
  have hp : (k:ℝ)/N < 1/2 := by
    apply (div_lt_iff₀ (show 0<N by linarith)).2
    have hh : (2:ℝ)*k < N := by dsimp [N]; exact_mod_cast (show 2*k<2*n+1 by omega)
    linarith
  have hform := bernoulliSharpBeta_fraction_imbalance N (k:ℝ)
    (by linarith) (by exact_mod_cast hk.ne') hp
  have hne : ¬Even (2*n+1) := by rintro ⟨r,hr⟩; omega
  have hκ : parityUniformKappa (2*n+1)/4 =
      ((N-1)/(4*N))*oddHypergeomConstant (2*n+1) := by
    rw [parityUniformKappa, if_neg hne,
      oddHypergeomConstant_eq_artanh (2*n+1) (by omega)]
    dsimp [N]
    field_simp
  have hscale : 0 < (N-1)/(4*N) := by positivity
  have hid : ((N-1)/(4*N)) * (N/(N-1)*imbalanceFactor (1-2*(k:ℝ)/N)) =
      bernoulliSharpBeta ((k:ℝ)/N) := by
    rw [hform]; field_simp [ne_of_gt (show 0<N by linarith), ne_of_gt (show 0<N-1 by linarith)]
  have hbound := mul_le_mul_of_nonneg_left (odd_imbalance_bound n k hn hk hkn) hscale.le
  change (N-1)/(4*N)*(N/(N-1)*imbalanceFactor (1-2*(k:ℝ)/N)) ≤ _ at hbound
  rw [hid, ← hκ] at hbound
  refine ⟨hbound, ?_⟩
  rw [hκ, ← hid, mul_right_inj' hscale.ne']
  exact odd_imbalance_bound_equality_iff n k hn hk hkn

/-- The lattice Bernoulli coefficient is bounded by the parity-uniform
coefficient, including balanced even populations. -/
theorem bernoulliSharpBeta_le_parityUniformKappa (N k : ℕ)
    (hN : 2 ≤ N) (hk : 0 < k) (hkhalf : 2*k ≤ N) :
    bernoulliSharpBeta ((k:ℝ)/N) ≤ parityUniformKappa N/4 := by
  obtain ⟨n, he | ho⟩ := Nat.even_or_odd' N
  · subst N
    have hE : Even (2*n) := ⟨n, by omega⟩
    rw [parityUniformKappa, if_pos hE]
    exact bernoulliSharpBeta_le_quarter _ (by positivity)
      ((div_le_one (by exact_mod_cast (show 0<2*n by omega))).2
        (by exact_mod_cast (show k≤2*n by omega)))
  · subst N
    exact (bernoulliSharpBeta_odd_lattice n k (by omega) hk (by omega)).1

/-- The nearest central reduced success count is the complete equality
set for the parity-uniform Bernoulli coefficient. -/
theorem bernoulliSharpBeta_parityUniformKappa_eq_iff (N k : ℕ)
    (hN : 2 ≤ N) (hk : 0 < k) (hkhalf : 2*k ≤ N) :
    bernoulliSharpBeta ((k:ℝ)/N) = parityUniformKappa N/4 ↔ k=N/2 := by
  obtain ⟨n, he | ho⟩ := Nat.even_or_odd' N
  · subst N
    have hE : Even (2*n) := ⟨n, by omega⟩
    have hn : 0 < n := by omega
    have hNR : (0:ℝ) < (2*n:ℕ) := by exact_mod_cast (show 0<2*n by omega)
    have hp : 0 < (k:ℝ)/((2*n:ℕ):ℝ) := div_pos (by exact_mod_cast hk) hNR
    have hp1 : (k:ℝ)/((2*n:ℕ):ℝ) < 1 :=
      (div_lt_one hNR).2 (by exact_mod_cast (show k<2*n by omega))
    have hdiv : (2*n)/2=n := by omega
    rw [hdiv, parityUniformKappa, if_pos hE]
    constructor
    · intro heq
      by_contra hkn
      have hpne : (k:ℝ)/((2*n:ℕ):ℝ) ≠ 1/2 := by
        intro hh
        have hc := (div_eq_iff hNR.ne').mp hh
        have hknR : (k:ℝ) ≠ n := by exact_mod_cast hkn
        apply hknR
        push_cast at hc
        linarith
      exact (ne_of_lt (bernoulliSharpBeta_lt_quarter hp hp1 hpne)) heq
    · intro hkn
      rw [hkn]
      have hf : (n:ℝ)/((2*n:ℕ):ℝ) = 1/2 := by
        push_cast
        field_simp [show (n:ℝ) ≠ 0 by exact_mod_cast hn.ne']
      rw [hf, bernoulliSharpBeta_half]
  · subst N
    have hdiv : (2*n+1)/2=n := by omega
    rw [hdiv]
    exact (bernoulliSharpBeta_odd_lattice n k (by omega) hk (by omega)).2

/-- The actual sample-scale coefficient Mβ is no larger than V_*. -/
theorem scaledBernoulliVariance_le_uniform (N k m : ℕ)
    (hN : 2 ≤ N) (hk : 0 < k) (hkhalf : 2*k ≤ N)
    (hm : 0 < m) (hmN : m < N) :
    envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/N) ≤
      hypergeomUniformQuadraticVariance N m := by
  have hNreal : (1:ℝ) ≤ N := by exact_mod_cast (show 1≤N by omega)
  have hM : 0 ≤ envelopeM (N:ℝ) (m:ℝ) := by
    unfold envelopeM
    exact div_nonneg (mul_nonneg (by positivity)
      (sub_nonneg.mpr (by exact_mod_cast hmN.le))) (by linarith)
  have h := mul_le_mul_of_nonneg_left
    (bernoulliSharpBeta_le_parityUniformKappa N k hN hk hkhalf) hM
  simpa only [hypergeomUniformQuadraticVariance, mul_div_assoc] using h

/-- Exact equality of the scaled Bernoulli and parity-uniform variance coefficients. -/
theorem scaledBernoulliVariance_eq_uniform_iff (N k m : ℕ)
    (hN : 2 ≤ N) (hk : 0 < k) (hkhalf : 2*k ≤ N)
    (hm : 0 < m) (hmN : m < N) :
    envelopeM (N:ℝ) (m:ℝ)*bernoulliSharpBeta ((k:ℝ)/N) =
      hypergeomUniformQuadraticVariance N m ↔ k=N/2 := by
  have hM : 0 < envelopeM (N:ℝ) (m:ℝ) := by
    unfold envelopeM
    have hmR : (0:ℝ)<m := by exact_mod_cast hm
    have hNm : (0:ℝ)<(N:ℝ)-m := sub_pos.mpr (by exact_mod_cast hmN)
    have hN1 : (0:ℝ)<(N:ℝ)-1 := by
      have h : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
      linarith
    exact div_pos (mul_pos hmR hNm) hN1
  unfold hypergeomUniformQuadraticVariance
  rw [mul_div_assoc, mul_right_inj' hM.ne']
  exact bernoulliSharpBeta_parityUniformKappa_eq_iff N k hN hk hkhalf

/-- The full Gaussian chain printed as A:quadratic, with the original
piecewise and scaled KL rates, on the closed canonical support. -/
theorem hypergeom_piecewise_gaussian_chain (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    let μ : ℝ := (m:ℝ)*k/N
    let M := envelopeM (N:ℝ) (m:ℝ)
    let IP := scaledKLRate M ((k:ℝ)/N) (envelopeScale (N:ℝ) (m:ℝ)) μ v
    let B := (v-μ)^2/(2*(M*bernoulliSharpBeta ((k:ℝ)/N)))
    let U := (v-μ)^2/(2*hypergeomUniformQuadraticVariance N m)
    IP ≤ canonicalPiecewiseRate N k m v ∧ B ≤ IP ∧ U ≤ B := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hM := envelopeM_positive (N:ℝ) (m:ℝ) hmR hhR
  have hp : 0<(k:ℝ)/N := div_pos (by exact_mod_cast (show 0<k by omega)) hNR
  have hp1 : (k:ℝ)/N<1 := (div_lt_one hNR).2 (by exact_mod_cast (show k<N by omega))
  have hβ := bernoulliSharpBeta_pos_interior ((k:ℝ)/N) hp hp1
  have ha : envelopeScale (N:ℝ) (m:ℝ) ≠ 0 := by
    unfold envelopeScale
    exact div_ne_zero (by linarith) (by linarith)
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hv0 hvm
  have hbound := scaledBernoulliVariance_le_uniform N k m (by omega)
    (by omega) hk (by omega) (by omega)
  dsimp only
  refine ⟨(canonicalPiecewiseRate_quadratic_comparison hmR hmkR hkR hhR hv0 hvm).1,
    scaledKLRate_ge_sharp_gaussian _ _ _ _ _ hM ha hp hp1 ⟨hθ.1.le,hθ.2.le⟩, ?_⟩
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_left hbound (by norm_num))

/-- Two Gaussian rates with positive coefficients have a nonzero contact
exactly when their variance coefficients coincide. -/
theorem gaussianRates_eq_iff (A B x : ℝ) (hA : 0 < A) (hB : 0 < B) :
    x^2/(2*A) = x^2/(2*B) ↔ x=0 ∨ A=B := by
  by_cases hx : x=0
  · simp [hx]
  · constructor
    · intro heq
      have hh := (div_eq_div_iff (show 2*A ≠ 0 by positivity)
        (show 2*B ≠ 0 by positivity)).mp heq
      have hden : 2*B = 2*A := mul_left_cancel₀ (pow_ne_zero 2 hx) hh
      exact Or.inr (by linarith)
    · rintro (h | h)
      · exact False.elim (hx h)
      · rw [h]

/-- The final Gaussian step has exactly the zero displacement and central
lattice contacts, with no assumption that either rate inequality holds. -/
theorem hypergeom_gaussian_uniform_eq_iff (N k m : ℕ)
    (hN : 2 ≤ N) (hk : 0 < k) (hkhalf : 2*k ≤ N)
    (hm : 0 < m) (hmN : m < N) (v : ℝ) :
    (v-(m:ℝ)*k/N)^2/(2*(envelopeM N m*bernoulliSharpBeta ((k:ℝ)/N))) =
      (v-(m:ℝ)*k/N)^2/(2*hypergeomUniformQuadraticVariance N m) ↔
      v=(m:ℝ)*k/N ∨ k=N/2 := by
  have hNR : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (0:ℝ)<(N:ℝ)-1 := by
    have h : (1:ℝ)<N := by exact_mod_cast (show 1<N by omega)
    linarith
  have hM : 0 < envelopeM (N:ℝ) (m:ℝ) := by
    unfold envelopeM
    exact div_pos (mul_pos (by exact_mod_cast hm)
      (sub_pos.mpr (by exact_mod_cast hmN))) hN1
  have hp : 0<(k:ℝ)/N := div_pos (by exact_mod_cast hk) hNR
  have hp1 : (k:ℝ)/N<1 := (div_lt_one hNR).2 (by exact_mod_cast (show k<N by omega))
  have hβ := bernoulliSharpBeta_pos_interior ((k:ℝ)/N) hp hp1
  have hV : 0 < hypergeomUniformQuadraticVariance N m :=
    lt_of_lt_of_le (mul_pos hM hβ)
      (scaledBernoulliVariance_le_uniform N k m hN hk hkhalf hm hmN)
  rw [gaussianRates_eq_iff _ _ _ (mul_pos hM hβ) hV,
    sub_eq_zero, scaledBernoulliVariance_eq_uniform_iff N k m hN hk hkhalf hm hmN]

/-- The complete supported sub-half equality classification for the
scaled-KL Gaussian step, including zero displacement and support endpoints. -/
theorem hypergeom_scaledKL_gaussian_eq_iff_subhalf (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k < N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    scaledKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) ((m:ℝ)*k/N) v =
      (v-(m:ℝ)*k/N)^2/(2*(envelopeM N m*bernoulliSharpBeta ((k:ℝ)/N))) ↔
      v=(m:ℝ)*k/N ∨
        v-(m:ℝ)*k/N=envelopeM N m*(1-2*((k:ℝ)/N))/envelopeScale N m := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) < N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hNR : (0:ℝ)<N := by linarith
  have hM := envelopeM_positive (N:ℝ) (m:ℝ) hmR hhR
  have hp : 0<(k:ℝ)/N := div_pos (by exact_mod_cast (show 0<k by omega)) hNR
  have hph : (k:ℝ)/N<1/2 := by apply (div_lt_iff₀ hNR).2; linarith
  have ha : envelopeScale (N:ℝ) (m:ℝ) ≠ 0 := by
    unfold envelopeScale
    exact div_ne_zero (by linarith) (by linarith)
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR.le hhR hv0 hvm
  exact scaledKLRate_sharp_gaussian_eq_iff_subhalf _ _ _ _ _ hM ha hp hph
    ⟨hθ.1.le,hθ.2.le⟩

/-- At the balanced success margin, the scaled-KL Gaussian comparison is
strict at every nonzero supported displacement. -/
theorem hypergeom_scaledKL_gaussian_strict_balanced (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k = N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) (hne : v ≠ (m:ℝ)*k/N) :
    (v-(m:ℝ)*k/N)^2/(2*(envelopeM N m*bernoulliSharpBeta ((k:ℝ)/N))) <
      scaledKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) ((m:ℝ)*k/N) v := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) = N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hNR : (0:ℝ)<N := by linarith
  have hp : (k:ℝ)/N=1/2 := by apply (div_eq_iff hNR.ne').2; linarith
  have hM := envelopeM_positive (N:ℝ) (m:ℝ) hmR hhR
  have ha : envelopeScale (N:ℝ) (m:ℝ) ≠ 0 := by
    unfold envelopeScale
    exact div_ne_zero (by linarith) (by linarith)
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR.le hhR hv0 hvm
  rw [hp] at hθ ⊢
  exact scaledKLRate_sharp_gaussian_strict_half _ _ _ _ hM ha hne ⟨hθ.1.le,hθ.2.le⟩

/-- In an even population the scaled KL envelope strictly improves the
uniform Gaussian rate at every nonzero supported deviation. -/
theorem hypergeom_scaledKL_uniform_strict_even (N k m : ℕ)
    (hE : Even N) (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) (hne : v ≠ (m:ℝ)*k/N) :
    (v-(m:ℝ)*k/N)^2/(2*hypergeomUniformQuadraticVariance N m) <
      scaledKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) ((m:ℝ)*k/N) v := by
  have hchain := hypergeom_piecewise_gaussian_chain N k m hm hmk hk hhalf v hv0 hvm
  dsimp only at hchain
  by_cases hb : 2*k=N
  · have hs := hypergeom_scaledKL_gaussian_strict_balanced N k m hm hmk hb hhalf v hv0 hvm hne
    exact lt_of_le_of_lt hchain.2.2 hs
  · have hkc : k ≠ N/2 := by
      rintro rfl
      obtain ⟨q,hq⟩ := hE
      omega
    have hneq := (hypergeom_gaussian_uniform_eq_iff N k m (by omega)
      (by omega) hk (by omega) (by omega) v).not.mpr (not_or.mpr ⟨hne,hkc⟩)
    have hlt := lt_of_le_of_ne hchain.2.2 (Ne.symm hneq)
    exact hlt.trans_le hchain.2.1

/-- In an odd population the uniform Gaussian contact occurs exactly at
the mean or at the central margin and reflected Bernoulli target. -/
theorem hypergeom_scaledKL_uniform_eq_iff_odd (n k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : k ≤ n) (hhalf : 2*m < 2*n+1)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    scaledKLRate (envelopeM ((2*n+1:ℕ):ℝ) m) ((k:ℝ)/((2*n+1:ℕ):ℝ))
      (envelopeScale ((2*n+1:ℕ):ℝ) m) ((m:ℝ)*k/((2*n+1:ℕ):ℝ)) v =
      (v-(m:ℝ)*k/((2*n+1:ℕ):ℝ))^2/
        (2*hypergeomUniformQuadraticVariance (2*n+1) m) ↔
      v=(m:ℝ)*k/((2*n+1:ℕ):ℝ) ∨
        (k=n ∧ v-(m:ℝ)*k/((2*n+1:ℕ):ℝ)=
          envelopeM ((2*n+1:ℕ):ℝ) m*(1-2*((k:ℝ)/((2*n+1:ℕ):ℝ)))/envelopeScale ((2*n+1:ℕ):ℝ) m) := by
  have hchain := hypergeom_piecewise_gaussian_chain (2*n+1) k m hm hmk (by omega) hhalf v hv0 hvm
  dsimp only at hchain
  have hmiddle := hypergeom_scaledKL_gaussian_eq_iff_subhalf (2*n+1) k m hm hmk
    (by omega) hhalf v hv0 hvm
  have hfinal := hypergeom_gaussian_uniform_eq_iff (2*n+1) k m (by omega)
    (by omega) (by omega) (by omega) (by omega) v
  have hdiv : (2*n+1)/2=n := by omega
  rw [hdiv] at hfinal
  constructor
  · intro heq
    have hmid : scaledKLRate (envelopeM ((2*n+1:ℕ):ℝ) m) ((k:ℝ)/((2*n+1:ℕ):ℝ))
      (envelopeScale ((2*n+1:ℕ):ℝ) m) ((m:ℝ)*k/((2*n+1:ℕ):ℝ)) v =
      (v-(m:ℝ)*k/((2*n+1:ℕ):ℝ))^2/
        (2*(envelopeM ((2*n+1:ℕ):ℝ) m*bernoulliSharpBeta ((k:ℝ)/((2*n+1:ℕ):ℝ)))) := by
      linarith [hchain.2.1,hchain.2.2]
    have hend := hfinal.mp (by linarith [hchain.2.1,hchain.2.2])
    rcases hmiddle.mp hmid with hzero | hreflect
    · exact Or.inl hzero
    · rcases hend with hzero | hcenter
      · exact Or.inl hzero
      · exact Or.inr ⟨hcenter,hreflect⟩
  · rintro (hzero | ⟨hcenter,hreflect⟩)
    · have hmid := hmiddle.mpr (Or.inl hzero)
      have hend := hfinal.mpr (Or.inl hzero)
      exact hmid.trans hend
    · have hmid := hmiddle.mpr (Or.inr hreflect)
      have hend := hfinal.mpr (Or.inr hcenter)
      exact hmid.trans hend

end
end ExactHoeffding
