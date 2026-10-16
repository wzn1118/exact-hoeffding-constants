import ExactHoeffding.BernoulliKL
import ExactHoeffding.RiccatiCertificates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algebraic core of the piecewise KL rate

The quadratic envelopes in the tail note differ by a quadratic polynomial in
`y = u - μ`.  This file proves the discriminant, the two switching points,
the sign pattern, and the branch formula for the integrated rate.  The strict-comparison theorem uses the central KL comparison and switching
slope signs to propagate the improvement along both tangent-corrected tails.
-/

namespace ExactHoeffding

noncomputable def varianceEnvelopeDifference (c h b y : ℝ) : ℝ :=
  c * y ^ 2 - h * y - b

noncomputable def varianceSwitchDiscriminant (c h b : ℝ) : ℝ :=
  h ^ 2 + 4 * c * b

noncomputable def varianceSwitchRootMinus (c h b : ℝ) : ℝ :=
  (h - Real.sqrt (varianceSwitchDiscriminant c h b)) / (2 * c)

noncomputable def varianceSwitchRootPlus (c h b : ℝ) : ℝ :=
  (h + Real.sqrt (varianceSwitchDiscriminant c h b)) / (2 * c)

noncomputable def varianceSwitchMinus (mu c h b : ℝ) : ℝ :=
  mu + varianceSwitchRootMinus c h b

noncomputable def varianceSwitchPlus (mu c h b : ℝ) : ℝ :=
  mu + varianceSwitchRootPlus c h b

lemma varianceSwitchDiscriminant_pos {c h b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    0 < varianceSwitchDiscriminant c h b := by
  have hcb : 0 < c * b := mul_pos hc hb
  dsimp [varianceSwitchDiscriminant]
  have hs : 0 ≤ h ^ 2 := sq_nonneg h
  linarith

lemma varianceSwitch_sqrt_sq {c h b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    (Real.sqrt (varianceSwitchDiscriminant c h b)) ^ 2 =
      varianceSwitchDiscriminant c h b := by
  exact Real.sq_sqrt (le_of_lt (varianceSwitchDiscriminant_pos hc hb))

lemma varianceSwitch_abs_lt_sqrt {c h b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    |h| < Real.sqrt (varianceSwitchDiscriminant c h b) := by
  have hs : 0 ≤ Real.sqrt (varianceSwitchDiscriminant c h b) := Real.sqrt_nonneg _
  have hsq := varianceSwitch_sqrt_sq (h := h) hc hb
  have hcb : 0 < c * b := mul_pos hc hb
  have hsq' : h ^ 2 < (Real.sqrt (varianceSwitchDiscriminant c h b)) ^ 2 := by
    dsimp [varianceSwitchDiscriminant] at hsq ⊢
    linarith
  have habs : |h| ^ 2 = h ^ 2 := sq_abs h
  exact (sq_lt_sq₀ (abs_nonneg h) hs).mp (by simpa [habs] using hsq')

lemma varianceSwitchRootMinus_lt_zero {c h b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    varianceSwitchRootMinus c h b < 0 := by
  have ha := varianceSwitch_abs_lt_sqrt (h := h) hc hb
  have hden : 0 < 2 * c := by linarith
  dsimp [varianceSwitchRootMinus]
  apply div_neg_of_neg_of_pos _ hden
  have hh : h ≤ |h| := le_abs_self h
  linarith

lemma varianceSwitchRootPlus_pos {c h b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    0 < varianceSwitchRootPlus c h b := by
  have ha := varianceSwitch_abs_lt_sqrt (h := h) hc hb
  have hden : 0 < 2 * c := by linarith
  dsimp [varianceSwitchRootPlus]
  apply div_pos _ hden
  have hh : -|h| ≤ h := neg_abs_le h
  linarith

lemma varianceSwitchRootMinus_lt_rootPlus {c h b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    varianceSwitchRootMinus c h b < varianceSwitchRootPlus c h b := by
  have ha := varianceSwitch_abs_lt_sqrt (h := h) hc hb
  have hden : 0 < 2*c := by linarith
  dsimp [varianceSwitchRootMinus, varianceSwitchRootPlus]
  apply (div_lt_div_iff_of_pos_right hden).2
  have habs : 0 ≤ |h| := abs_nonneg h
  linarith

lemma varianceEnvelopeDifference_factorization (c h b x : ℝ)
    (hc : c ≠ 0)
    (hdisc : 0 ≤ varianceSwitchDiscriminant c h b) :
    varianceEnvelopeDifference c h b x =
      c * (x - varianceSwitchRootMinus c h b) *
        (x - varianceSwitchRootPlus c h b) := by
  rw [varianceSwitchRootMinus, varianceSwitchRootPlus]
  dsimp [varianceEnvelopeDifference, varianceSwitchDiscriminant]
  field_simp [hc]
  have hs : (Real.sqrt (h ^ 2 + 4*c*b)) ^ 2 = h ^ 2 + 4*c*b := by
    exact Real.sq_sqrt hdisc
  ring_nf at hs ⊢
  nlinarith

lemma varianceEnvelopeDifference_at_root_minus {c h b : ℝ}
    (hc : 0 < c) (hb : 0 < b) :
    varianceEnvelopeDifference c h b (varianceSwitchRootMinus c h b) = 0 := by
  rw [varianceEnvelopeDifference_factorization _ _ _ _ (ne_of_gt hc)
    (le_of_lt (varianceSwitchDiscriminant_pos hc hb))]
  simp

lemma varianceEnvelopeDifference_at_root_plus {c h b : ℝ}
    (hc : 0 < c) (hb : 0 < b) :
    varianceEnvelopeDifference c h b (varianceSwitchRootPlus c h b) = 0 := by
  rw [varianceEnvelopeDifference_factorization _ _ _ _ (ne_of_gt hc)
    (le_of_lt (varianceSwitchDiscriminant_pos hc hb))]
  simp

lemma varianceEnvelopeDifference_sign_iff {c h b x : ℝ}
    (hc : 0 < c) (hb : 0 < b) :
    varianceEnvelopeDifference c h b x ≤ 0 ↔
      varianceSwitchRootMinus c h b ≤ x ∧ x ≤ varianceSwitchRootPlus c h b := by
  rw [varianceEnvelopeDifference_factorization _ _ _ _ (ne_of_gt hc)
    (le_of_lt (varianceSwitchDiscriminant_pos hc hb))]
  have hroots := varianceSwitchRootMinus_lt_rootPlus (h := h) hc hb
  constructor
  · intro hle
    have hp : (x - varianceSwitchRootMinus c h b) *
        (x - varianceSwitchRootPlus c h b) ≤ 0 := by
      have hh : c * ((x - varianceSwitchRootMinus c h b) *
          (x - varianceSwitchRootPlus c h b)) ≤ c * 0 := by
        simpa [mul_assoc] using hle
      exact le_of_mul_le_mul_left hh hc
    rcases mul_nonpos_iff.mp hp with hcase | hcase
    · exact ⟨by linarith [hcase.1], by linarith [hcase.2]⟩
    · exfalso
      linarith [hcase.1, hcase.2]
  · rintro ⟨hlo, hhi⟩
    have h1 : 0 ≤ x - varianceSwitchRootMinus c h b := by linarith
    have h2 : x - varianceSwitchRootPlus c h b ≤ 0 := by linarith
    have hp := mul_nonpos_of_nonneg_of_nonpos h1 h2
    simpa [mul_assoc] using mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hp

lemma varianceSwitchMinus_lt_mu {mu c h b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    varianceSwitchMinus mu c h b < mu := by
  dsimp [varianceSwitchMinus]
  have := varianceSwitchRootMinus_lt_zero (h := h) hc hb
  linarith

lemma mu_lt_varianceSwitchPlus {mu c h b : ℝ} (hc : 0 < c) (hb : 0 < b) :
    mu < varianceSwitchPlus mu c h b := by
  dsimp [varianceSwitchPlus]
  have := varianceSwitchRootPlus_pos (h := h) hc hb
  linarith

lemma varianceSwitchMinus_lt_varianceSwitchPlus {mu c h b : ℝ}
    (hc : 0 < c) (hb : 0 < b) :
    varianceSwitchMinus mu c h b < varianceSwitchPlus mu c h b := by
  dsimp [varianceSwitchMinus, varianceSwitchPlus]
  simpa [add_comm] using add_lt_add_left (varianceSwitchRootMinus_lt_rootPlus (h := h) hc hb) mu

/-- Endpoint positivity places both switching points strictly inside the
support.  The hypotheses are the exact endpoint checks used for the
hypergeometric parameters. -/
lemma varianceSwitch_mem_interval
    {mu upper c h b : ℝ}
    (hmu : 0 < mu) (hupper : mu < upper)
    (hc : 0 < c) (hb : 0 < b)
    (hleft : 0 < varianceEnvelopeDifference c h b (-mu))
    (hright : 0 < varianceEnvelopeDifference c h b (upper - mu)) :
    0 < varianceSwitchMinus mu c h b ∧
      varianceSwitchMinus mu c h b < mu ∧
      mu < varianceSwitchPlus mu c h b ∧
      varianceSwitchPlus mu c h b < upper := by
  have hrm := varianceSwitchMinus_lt_mu (mu := mu) (h := h) hc hb
  have hmr := mu_lt_varianceSwitchPlus (mu := mu) (h := h) hc hb
  have hl : 0 < c * (-mu - varianceSwitchRootMinus c h b) *
      (-mu - varianceSwitchRootPlus c h b) := by
    rw [← varianceEnvelopeDifference_factorization c h b (-mu) (ne_of_gt hc)
      (le_of_lt (varianceSwitchDiscriminant_pos hc hb))]
    exact hleft
  have hr : 0 < c * (upper-mu - varianceSwitchRootMinus c h b) *
      (upper-mu - varianceSwitchRootPlus c h b) := by
    rw [← varianceEnvelopeDifference_factorization c h b (upper-mu) (ne_of_gt hc)
      (le_of_lt (varianceSwitchDiscriminant_pos hc hb))]
    exact hright
  have hrootord := varianceSwitchRootMinus_lt_rootPlus (h := h) hc hb
  have hminuspos : 0 < mu + varianceSwitchRootMinus c h b := by
    have hp : -mu - varianceSwitchRootPlus c h b < 0 := by
      have := varianceSwitchRootPlus_pos (h := h) hc hb
      linarith
    have hfirst : -mu - varianceSwitchRootMinus c h b < 0 := by
      by_contra hn
      have hnon : 0 ≤ -mu - varianceSwitchRootMinus c h b := le_of_not_gt hn
      have : c * (-mu - varianceSwitchRootMinus c h b) *
          (-mu - varianceSwitchRootPlus c h b) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (le_of_lt hc) hnon) (le_of_lt hp)
      linarith
    linarith
  have hpluslt : mu + varianceSwitchRootPlus c h b < upper := by
    have hfirst : 0 ≤ upper-mu - varianceSwitchRootMinus c h b := by
      have := varianceSwitchRootMinus_lt_zero (h := h) hc hb
      linarith
    have hsecond : 0 < upper-mu - varianceSwitchRootPlus c h b := by
      by_contra hn
      have hnon : upper-mu - varianceSwitchRootPlus c h b ≤ 0 := le_of_not_gt hn
      have : c * (upper-mu - varianceSwitchRootMinus c h b) *
          (upper-mu - varianceSwitchRootPlus c h b) ≤ 0 := by
        exact mul_nonpos_of_nonneg_of_nonpos
          (mul_nonneg (le_of_lt hc) hfirst) hnon
      linarith
    linarith
  exact ⟨hminuspos, hrm, hmr, hpluslt⟩

noncomputable def piecewiseKLRate
    (IP IB sP sB : ℝ → ℝ) (rminus rplus v : ℝ) : ℝ :=
  if v < rminus then
    IB v + IP rminus - IB rminus + (v-rminus) * (sP rminus-sB rminus)
  else if v ≤ rplus then IP v
  else
    IB v + IP rplus - IB rplus + (v-rplus) * (sP rplus-sB rplus)

lemma piecewiseKLRate_eq_left {IP IB sP sB : ℝ → ℝ}
    {rm rp v : ℝ} (hv : v < rm) :
    piecewiseKLRate IP IB sP sB rm rp v =
      IB v + IP rm - IB rm + (v-rm) * (sP rm-sB rm) := by
  simp [piecewiseKLRate, hv]

lemma piecewiseKLRate_eq_central {IP IB sP sB : ℝ → ℝ}
    {rm rp v : ℝ} (hlo : rm ≤ v) (hhi : v ≤ rp) :
    piecewiseKLRate IP IB sP sB rm rp v = IP v := by
  simp [piecewiseKLRate, not_lt.mpr hlo, hhi]

lemma piecewiseKLRate_eq_right {IP IB sP sB : ℝ → ℝ}
    {rm rp v : ℝ} (hr : rp < v) (hroot : rm ≤ rp) :
    piecewiseKLRate IP IB sP sB rm rp v =
      IB v + IP rp - IB rp + (v-rp) * (sP rp-sB rp) := by
  have hnot : ¬ v < rm := by linarith
  have hnot' : ¬ v ≤ rp := by linarith
  simp [piecewiseKLRate, hnot, hnot']

/-- Strict binomial improvement from the central comparison and the signs of
its first derivative at the switching points.  The tangent correction remains
positive on each outward branch. -/
theorem piecewiseKLRate_strict_improves
    {IP IB sP sB : ℝ → ℝ} {rm rp mu : ℝ}
    (hmuL : rm < mu) (hmuR : mu < rp)
    (hcenter : ∀ v, v ≠ mu → rm ≤ v → v ≤ rp → IB v < IP v)
    (hsL : sP rm-sB rm ≤ 0) (hsR : 0 ≤ sP rp-sB rp) :
    ∀ v, v ≠ mu → IB v < piecewiseKLRate IP IB sP sB rm rp v := by
  intro v hv
  have hroot : rm ≤ rp := le_of_lt (lt_trans hmuL hmuR)
  by_cases hl : v < rm
  · rw [piecewiseKLRate_eq_left hl]
    have hgap := hcenter rm (ne_of_lt hmuL) le_rfl hroot
    have hcor : 0 ≤ (v-rm)*(sP rm-sB rm) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hsL
    linarith
  · by_cases hc : v ≤ rp
    · rw [piecewiseKLRate_eq_central (le_of_not_gt hl) hc]
      exact hcenter v hv (le_of_not_gt hl) hc
    · rw [piecewiseKLRate_eq_right (lt_of_not_ge hc) hroot]
      have hgap := hcenter rp (ne_of_gt hmuR) hroot le_rfl
      have hcor : 0 ≤ (v-rp)*(sP rp-sB rp) :=
        mul_nonneg (by linarith) hsR
      linarith

/-- The left switching point is a contact of the two rate branches. -/
lemma piecewiseKLRate_left_contact {IP IB sP sB : ℝ → ℝ}
    {rm rp : ℝ} (hroot : rm ≤ rp) :
    piecewiseKLRate IP IB sP sB rm rp rm = IP rm := by
  exact piecewiseKLRate_eq_central le_rfl hroot

/-- The right switching point is a contact of the two rate branches. -/
lemma piecewiseKLRate_right_contact {IP IB sP sB : ℝ → ℝ}
    {rm rp : ℝ} (hroot : rm ≤ rp) :
    piecewiseKLRate IP IB sP sB rm rp rp = IP rp := by
  exact piecewiseKLRate_eq_central hroot le_rfl

/-- The analogous non-strict comparison with the quadratic-envelope rate. -/
lemma piecewiseKLRate_ge_quadratic
    {IP IB sP sB : ℝ → ℝ} {rm rp : ℝ}
    (hroot : rm ≤ rp)
    (hleft : ∀ v, v < rm →
      IB v + IP rm - IB rm + (v-rm) * (sP rm-sB rm) ≥ IP v)
    (hright : ∀ v, rp < v →
      IB v + IP rp - IB rp + (v-rp) * (sP rp-sB rp) ≥ IP v) :
    ∀ v, piecewiseKLRate IP IB sP sB rm rp v ≥ IP v := by
  intro v
  by_cases hl : v < rm
  · rw [piecewiseKLRate_eq_left hl]
    exact hleft v hl
  · by_cases hc : v ≤ rp
    · rw [piecewiseKLRate_eq_central (le_of_not_gt hl) hc]
    · rw [piecewiseKLRate_eq_right (lt_of_not_ge hc) hroot]
      exact hright v (lt_of_not_ge hc)


/-- The ordinary binomial variance envelope in the mean coordinate. -/
noncomputable def klBinomialEnvelope (m u : ℝ) : ℝ := u*(m-u)/m

/-- The quadratic envelope used in the finite-population KL theorem. -/
noncomputable def klQuadraticEnvelope (N k m u : ℝ) : ℝ :=
  varianceBarrier N m (1-2*k/N) (u-m*k/N)

noncomputable def klSwitchC (N m : ℝ) : ℝ :=
  1/m - (envelopeScale N m)^2 / envelopeM N m

noncomputable def klSwitchH (N k m : ℝ) : ℝ :=
  (1-envelopeScale N m)*(1-2*k/N)

noncomputable def klSwitchB (N k m : ℝ) : ℝ :=
  (m-envelopeM N m)*(k/N)*(1-k/N)

/-- Exact quadratic difference, with the coefficients used in the explicit
switching-point formula. -/
lemma kl_variance_envelope_difference (N k m u : ℝ) (hm : m ≠ 0) :
    klQuadraticEnvelope N k m u - klBinomialEnvelope m u =
      varianceEnvelopeDifference (klSwitchC N m) (klSwitchH N k m)
        (klSwitchB N k m) (u-m*k/N) := by
  unfold klQuadraticEnvelope klBinomialEnvelope varianceBarrier
    varianceEnvelopeDifference klSwitchC klSwitchH klSwitchB
  field_simp [hm]
  ring

lemma klSwitchC_expansion (N m : ℝ)
    (hm : m ≠ 0) (hN1 : N-1 ≠ 0) (hN2 : N-2 ≠ 0)
    (hNm : N-m ≠ 0) :
    klSwitchC N m =
      (m-1)*(3*N^2-4*N-4*m*(N-1))/(m*(N-m)*(N-2)^2) := by
  unfold klSwitchC envelopeM envelopeScale
  field_simp [hm,hN1,hN2,hNm]
  ring

lemma klSwitchC_pos (N m : ℝ) (hm : 3 ≤ m) (hhalf : 2*m < N) :
    0 < klSwitchC N m := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m-1 := by linarith
  have hN : 0 < N := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hN2 : 0 < N-2 := by linarith
  have hNm : 0 < N-m := by linarith
  have hgap : 0 < N-2*m := by linarith
  have hbracket : 0 < 3*N^2-4*N-4*m*(N-1) := by
    have he : 3*N^2-4*N-4*m*(N-1) =
        N*(N-2)+2*(N-1)*(N-2*m) := by ring
    rw [he]
    positivity
  rw [klSwitchC_expansion N m (ne_of_gt hm0) (ne_of_gt hN1)
    (ne_of_gt hN2) (ne_of_gt hNm)]
  positivity

lemma klSwitchB_pos (N k m : ℝ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    0 < klSwitchB N k m := by
  have hm0 : 0 < m := by linarith
  have hm1 : 0 < m-1 := by linarith
  have hk0 : 0 < k := by linarith
  have hN : 0 < N := by linarith
  have hN1 : 0 < N-1 := by linarith
  have hNk : k < N := by linarith
  have hgap : 0 < m-envelopeM N m := by
    have he : m-envelopeM N m = m*(m-1)/(N-1) := by
      unfold envelopeM
      field_simp [ne_of_gt hN1]
      ring
    rw [he]
    positivity
  have hp : 0 < k/N := div_pos hk0 hN
  have hp1 : k/N < 1 := (div_lt_one hN).2 hNk
  unfold klSwitchB
  exact mul_pos (mul_pos hgap hp) (sub_pos.mpr hp1)

/-- All four strict inequalities for the actual finite-population switching
points.  No root-location premise is left for the caller. -/
theorem kl_switching_points_full_domain (N k m : ℝ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    0 < varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m)
        (klSwitchB N k m) ∧
    varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m)
        (klSwitchB N k m) < m*k/N ∧
    m*k/N < varianceSwitchPlus (m*k/N) (klSwitchC N m) (klSwitchH N k m)
        (klSwitchB N k m) ∧
    varianceSwitchPlus (m*k/N) (klSwitchC N m) (klSwitchH N k m)
        (klSwitchB N k m) < m := by
  have hm0 : 0 < m := by linarith
  have hk0 : 0 < k := by linarith
  have hN : 0 < N := by linarith
  have hNk : k < N := by linarith
  have hmu : 0 < m*k/N := div_pos (mul_pos hm0 hk0) hN
  have hmuupper : m*k/N < m := by
    apply (div_lt_iff₀ hN).2
    exact mul_lt_mul_of_pos_left hNk hm0
  have heps := barrier_endpoints_positive N k m hm hmk hk hhalf
  apply varianceSwitch_mem_interval hmu hmuupper (klSwitchC_pos N m hm hhalf)
    (klSwitchB_pos N k m hm hmk hk hhalf)
  · have hid := kl_variance_envelope_difference N k m 0 (ne_of_gt hm0)
    simp only [klQuadraticEnvelope,klBinomialEnvelope,zero_mul,zero_div,zero_sub] at hid
    rw [← hid]
    have harg : -m*k/N = -(m*k/N) := by ring
    rw [harg] at heps
    simpa only [sub_zero] using heps.1
  · have hid := kl_variance_envelope_difference N k m m (ne_of_gt hm0)
    simp only [klQuadraticEnvelope,klBinomialEnvelope,sub_self,mul_zero,zero_div,sub_zero] at hid
    rw [← hid]
    exact heps.2

/-- On the full hypergeometric parameter domain, the smaller envelope is the
quadratic envelope exactly between the two explicit switching points. -/
theorem kl_quadratic_envelope_le_binomial_iff (N k m u : ℝ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N) :
    klQuadraticEnvelope N k m u ≤ klBinomialEnvelope m u ↔
      varianceSwitchMinus (m*k/N) (klSwitchC N m) (klSwitchH N k m)
        (klSwitchB N k m) ≤ u ∧
      u ≤ varianceSwitchPlus (m*k/N) (klSwitchC N m) (klSwitchH N k m)
        (klSwitchB N k m) := by
  rw [← sub_nonpos, kl_variance_envelope_difference N k m u (by linarith)]
  have hi := varianceEnvelopeDifference_sign_iff (h := klSwitchH N k m) (x := u-m*k/N)
    (klSwitchC_pos N m hm hhalf) (klSwitchB_pos N k m hm hmk hk hhalf)
  constructor
  · intro hle
    rcases hi.mp hle with ⟨hlo,hhi⟩
    dsimp [varianceSwitchMinus,varianceSwitchPlus]
    constructor <;> linarith
  · rintro ⟨hlo,hhi⟩
    apply hi.mpr
    dsimp [varianceSwitchMinus,varianceSwitchPlus] at hlo hhi
    constructor <;> linarith

end ExactHoeffding
