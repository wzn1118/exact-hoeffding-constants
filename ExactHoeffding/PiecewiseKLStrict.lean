import ExactHoeffding.PiecewiseKLComparison

open Set
open scoped Topology
namespace ExactHoeffding
noncomputable section

theorem hypergeom_upper_outer_kl_strict_fenchel (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (c v : ℝ) (hμc : (m:ℝ)*(k:ℝ)/(N:ℝ) < c) (hcm : c < m)
    (hcv : c ≤ v) (hvm : v < m) :
    ∃ t : ℝ, 0 ≤ t ∧
      outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) m
        ((m:ℝ)*(k:ℝ)/N) c v < t*(v-(m:ℝ)*k/N)-hypergeomCenteredLogMGF N k m t := by
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hp : 0 < (k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/(N:ℝ) < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hmu0 : (0:ℝ) < (m:ℝ)*(k:ℝ)/N := div_pos (mul_pos (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast (show 0 < k by omega))) hN
  have hc0 : 0 < c := hmu0.trans hμc
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hc0.le hcm.le
  have hdata := hypergeom_kl_riccati_data N k m hm hmk hk hhalf
  let μ : ℝ := (m:ℝ)*((k:ℝ)/(N:ℝ))
  have hμid : μ = (m:ℝ)*(k:ℝ)/(N:ℝ) := by dsimp [μ]; ring
  have hFc : Continuous (hypergeomCenteredLogMGF N k m) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t).continuousAt
  have hyc : Continuous (fun t => hypergeomTiltMean N k m t-μ) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).continuousAt).sub continuous_const
  have hFd : ∀ t, HasDerivAt (hypergeomCenteredLogMGF N k m)
      (hypergeomTiltMean N k m t-μ) t := by
    intro t
    rw [hμid]
    exact hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t
  obtain ⟨t,ht,hR⟩ := stitched_right_fenchel_strict
    (M := envelopeM N m) (p := (k:ℝ)/N) (a := envelopeScale N m)
    (m := (m:ℝ)) (μ := μ) (c := c) (v := v)
    (envelopeM_positive N m hmR hhR)
    (div_pos (by linarith : 0 < (N:ℝ)-2*(m:ℝ)) (by linarith : 0 < (N:ℝ)-2))
    (by positivity) hp hp1 rfl hFc hyc
    (fun t => (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).sub_const μ)
    hFd (hypergeomCenteredLogMGF_zero N k m (by omega) (by omega))
    (by rw [hypergeomTiltMean_zero N k m (by omega) (by omega),hμid]; ring)
    hdata.1 hdata.2 (hypergeom_laplace_envelope N k m hm hmk hk hhalf).2 (by simpa [hμid] using hμc) hcm hcv hvm
    (by simpa [hμid] using hθ.1) (by simpa [hμid] using hθ.2)
  rw [hμid] at hR
  exact ⟨t,ht,hR⟩


theorem hypergeom_lower_outer_kl_strict_fenchel (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (c v : ℝ) (hcμ : c < (m:ℝ)*(k:ℝ)/(N:ℝ)) (hc0 : 0 < c)
    (hvc : v ≤ c) (hv0 : 0 < v) :
    ∃ t : ℝ, t ≤ 0 ∧
      outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) m
        ((m:ℝ)*(k:ℝ)/N) c v < t*(v-(m:ℝ)*k/N)-hypergeomCenteredLogMGF N k m t := by
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hp : 0 < (k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/(N:ℝ) < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hcm : c < m := by
    have := mul_lt_mul_of_pos_left hp1 (by positivity : (0:ℝ)<m)
    rw [← mul_div_assoc] at this
    linarith
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hc0.le hcm.le
  have hdata := hypergeom_kl_riccati_data N k m hm hmk hk hhalf
  let μ : ℝ := (m:ℝ)*((k:ℝ)/(N:ℝ))
  have hμid : μ = (m:ℝ)*(k:ℝ)/(N:ℝ) := by dsimp [μ]; ring
  have hFc : Continuous (hypergeomCenteredLogMGF N k m) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t).continuousAt
  have hyc : Continuous (fun t => hypergeomTiltMean N k m t-μ) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).continuousAt).sub continuous_const
  have hFd : ∀ t, HasDerivAt (hypergeomCenteredLogMGF N k m)
      (hypergeomTiltMean N k m t-μ) t := by
    intro t
    rw [hμid]
    exact hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t
  obtain ⟨t,ht,hR⟩ := stitched_left_fenchel_strict
    (M := envelopeM N m) (p := (k:ℝ)/N) (a := envelopeScale N m)
    (m := (m:ℝ)) (μ := μ) (c := c) (v := v)
    (envelopeM_positive N m hmR hhR)
    (div_pos (by linarith : 0 < (N:ℝ)-2*(m:ℝ)) (by linarith : 0 < (N:ℝ)-2))
    (by positivity) hp hp1 rfl hFc hyc
    (fun t => (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).sub_const μ)
    hFd (hypergeomCenteredLogMGF_zero N k m (by omega) (by omega))
    (by rw [hypergeomTiltMean_zero N k m (by omega) (by omega),hμid]; ring)
    hdata.1 hdata.2 (hypergeom_laplace_envelope N k m hm hmk hk hhalf).2 (by simpa [hμid] using hcμ) hc0 hvc hv0
    (by simpa [hμid] using hθ.1) (by simpa [hμid] using hθ.2)
  rw [hμid] at hR
  exact ⟨t,ht,hR⟩


end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The actual finite-support Legendre transform, in the uncentered mean coordinate. -/
def hypergeomKLRate (N k m : ℕ) (v : ℝ) : ℝ :=
  sSup (Set.range (fun t : ℝ => t*(v-(m:ℝ)*k/N)-hypergeomCenteredLogMGF N k m t))

lemma hypergeomKLRate_bddAbove (N k m : ℕ) (hmk : m ≤ k) (hkm : k+m ≤ N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    BddAbove (Set.range (fun t : ℝ => t*(v-(m:ℝ)*k/N)-hypergeomCenteredLogMGF N k m t)) := by
  refine ⟨max (-Real.log (hypergeomMass N k m 0)) (-Real.log (hypergeomMass N k m m)), ?_⟩
  rintro z ⟨t,rfl⟩
  have h0 := hypergeomMass_pos_of_margins N k m 0 hmk hkm (by omega)
  have hm := hypergeomMass_pos_of_margins N k m m hmk hkm le_rfl
  have hterm (i : ℕ) (hi : i ≤ m) :
      hypergeomMass N k m i*Real.exp (t*(i:ℝ)) ≤ hypergeomMGF N k m t := by
    change _ ≤ ∑ j ∈ Finset.range (m+1), hypergeomMass N k m j*Real.exp (t*(j:ℝ))
    apply Finset.single_le_sum (fun j _ => mul_nonneg (hypergeomMass_nonneg N k m j)
      (Real.exp_pos (t*(j:ℝ))).le)
    exact Finset.mem_range.mpr (by omega : i < m+1)
  by_cases ht : 0 ≤ t
  · have hlog := Real.log_le_log (mul_pos hm (Real.exp_pos _)) (hterm m le_rfl)
    rw [Real.log_mul hm.ne' (Real.exp_pos _).ne',Real.log_exp] at hlog
    have htv : t*v ≤ t*(m:ℝ) := mul_le_mul_of_nonneg_left hvm ht
    have : t*(v-(m:ℝ)*k/N)-hypergeomCenteredLogMGF N k m t ≤
        -Real.log (hypergeomMass N k m m) := by unfold hypergeomCenteredLogMGF; linarith
    exact this.trans (le_max_right _ _)
  · have hlog := Real.log_le_log (mul_pos h0 (Real.exp_pos _)) (hterm 0 (by omega))
    simp only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at hlog
    have htv : t*v ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge ht) hv0
    have : t*(v-(m:ℝ)*k/N)-hypergeomCenteredLogMGF N k m t ≤
        -Real.log (hypergeomMass N k m 0) := by unfold hypergeomCenteredLogMGF; linarith
    exact this.trans (le_max_left _ _)

lemma hypergeomKLRate_ge_fenchel (N k m : ℕ) (hmk : m ≤ k) (hkm : k+m ≤ N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) (t : ℝ) :
    t*(v-(m:ℝ)*k/N)-hypergeomCenteredLogMGF N k m t ≤ hypergeomKLRate N k m v :=
  le_csSup (hypergeomKLRate_bddAbove N k m hmk hkm v hv0 hvm) ⟨t,rfl⟩

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

theorem hypergeom_upper_outer_kl_contact_gap (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (c v : ℝ) (hμc : (m:ℝ)*(k:ℝ)/(N:ℝ) < c) (hcm : c < m)
    (hcv : c ≤ v) (hvm : v < m) :
    ∃ t : ℝ, 0 ≤ t ∧
      outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) m
        ((m:ℝ)*(k:ℝ)/N) c v +
        (scaledBernoulliLogLaplace (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m)
          (bernoulliFenchelTilt ((k:ℝ)/N)
            ((k:ℝ)/N+envelopeScale N m*(c-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m)-
          hypergeomCenteredLogMGF N k m
          (bernoulliFenchelTilt ((k:ℝ)/N)
            ((k:ℝ)/N+envelopeScale N m*(c-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m)) ≤
        t*(v-(m:ℝ)*k/N)-hypergeomCenteredLogMGF N k m t := by
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hp : 0 < (k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/(N:ℝ) < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hmu0 : (0:ℝ) < (m:ℝ)*(k:ℝ)/N := div_pos (mul_pos (by exact_mod_cast (show 0 < m by omega)) (by exact_mod_cast (show 0 < k by omega))) hN
  have hc0 : 0 < c := hmu0.trans hμc
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hc0.le hcm.le
  have hdata := hypergeom_kl_riccati_data N k m hm hmk hk hhalf
  let μ : ℝ := (m:ℝ)*((k:ℝ)/(N:ℝ))
  have hμid : μ = (m:ℝ)*(k:ℝ)/(N:ℝ) := by dsimp [μ]; ring
  have hFc : Continuous (hypergeomCenteredLogMGF N k m) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t).continuousAt
  have hyc : Continuous (fun t => hypergeomTiltMean N k m t-μ) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).continuousAt).sub continuous_const
  have hFd : ∀ t, HasDerivAt (hypergeomCenteredLogMGF N k m)
      (hypergeomTiltMean N k m t-μ) t := by
    intro t
    rw [hμid]
    exact hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t
  obtain ⟨t,ht,hR⟩ := stitched_right_fenchel_contact_gap
    (M := envelopeM N m) (p := (k:ℝ)/N) (a := envelopeScale N m)
    (m := (m:ℝ)) (μ := μ) (c := c) (v := v)
    (envelopeM_positive N m hmR hhR)
    (div_pos (by linarith : 0 < (N:ℝ)-2*(m:ℝ)) (by linarith : 0 < (N:ℝ)-2))
    (by positivity) hp hp1 rfl hFc hyc
    (fun t => (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).sub_const μ)
    hFd (hypergeomCenteredLogMGF_zero N k m (by omega) (by omega))
    (by rw [hypergeomTiltMean_zero N k m (by omega) (by omega),hμid]; ring)
    hdata.1 hdata.2 (hypergeom_laplace_envelope N k m hm hmk hk hhalf).2 (by simpa [hμid] using hμc) hcm hcv hvm
    (by simpa [hμid] using hθ.1) (by simpa [hμid] using hθ.2)
  rw [hμid] at hR
  exact ⟨t,ht,hR⟩


end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

theorem hypergeom_lower_outer_kl_contact_gap (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (c v : ℝ) (hcμ : c < (m:ℝ)*(k:ℝ)/(N:ℝ)) (hc0 : 0 < c)
    (hvc : v ≤ c) (hv0 : 0 < v) :
    ∃ t : ℝ, t ≤ 0 ∧
      outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) m
        ((m:ℝ)*(k:ℝ)/N) c v +
        (scaledBernoulliLogLaplace (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m)
          (bernoulliFenchelTilt ((k:ℝ)/N)
            ((k:ℝ)/N+envelopeScale N m*(c-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m)-
          hypergeomCenteredLogMGF N k m
          (bernoulliFenchelTilt ((k:ℝ)/N)
            ((k:ℝ)/N+envelopeScale N m*(c-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m)) ≤
        t*(v-(m:ℝ)*k/N)-hypergeomCenteredLogMGF N k m t := by
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hp : 0 < (k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/(N:ℝ) < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hcm : c < m := by
    have := mul_lt_mul_of_pos_left hp1 (by positivity : (0:ℝ)<m)
    rw [← mul_div_assoc] at this
    linarith
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hc0.le hcm.le
  have hdata := hypergeom_kl_riccati_data N k m hm hmk hk hhalf
  let μ : ℝ := (m:ℝ)*((k:ℝ)/(N:ℝ))
  have hμid : μ = (m:ℝ)*(k:ℝ)/(N:ℝ) := by dsimp [μ]; ring
  have hFc : Continuous (hypergeomCenteredLogMGF N k m) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t).continuousAt
  have hyc : Continuous (fun t => hypergeomTiltMean N k m t-μ) :=
    (continuous_iff_continuousAt.mpr fun t =>
      (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).continuousAt).sub continuous_const
  have hFd : ∀ t, HasDerivAt (hypergeomCenteredLogMGF N k m)
      (hypergeomTiltMean N k m t-μ) t := by
    intro t
    rw [hμid]
    exact hypergeomCenteredLogMGF_hasDerivAt N k m (by omega) (by omega) t
  obtain ⟨t,ht,hR⟩ := stitched_left_fenchel_contact_gap
    (M := envelopeM N m) (p := (k:ℝ)/N) (a := envelopeScale N m)
    (m := (m:ℝ)) (μ := μ) (c := c) (v := v)
    (envelopeM_positive N m hmR hhR)
    (div_pos (by linarith : 0 < (N:ℝ)-2*(m:ℝ)) (by linarith : 0 < (N:ℝ)-2))
    (by positivity) hp hp1 rfl hFc hyc
    (fun t => (hypergeomTiltMean_hasDerivAt N k m (by omega) (by omega) t).sub_const μ)
    hFd (hypergeomCenteredLogMGF_zero N k m (by omega) (by omega))
    (by rw [hypergeomTiltMean_zero N k m (by omega) (by omega),hμid]; ring)
    hdata.1 hdata.2 (hypergeom_laplace_envelope N k m hm hmk hk hhalf).2 (by simpa [hμid] using hcμ) hc0 hvc hv0
    (by simpa [hμid] using hθ.1) (by simpa [hμid] using hθ.2)
  rw [hμid] at hR
  exact ⟨t,ht,hR⟩

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

theorem hypergeom_central_kl_strict_fenchel (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) (hvne : v ≠ (m:ℝ)*k/N) :
    let μ : ℝ := (m:ℝ)*(k:ℝ)/N
    let θ := (k:ℝ)/N + envelopeScale N m*(v-μ)/envelopeM N m
    let t := bernoulliFenchelTilt ((k:ℝ)/N) θ / envelopeScale N m
    scaledKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) μ v <
      t*(v-μ)-hypergeomCenteredLogMGF N k m t := by
  dsimp only
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < (k:ℝ)/(N:ℝ) := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/(N:ℝ) < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hM := envelopeM_positive (N:ℝ) m hmR hhR
  have ha : 0 < envelopeScale N m := div_pos (by linarith) (by linarith)
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hv0 hvm
  have hval := scaledBernoulliLogLaplace_at_fenchel hM ha hp hp1 hθ.1 hθ.2
  have hscale : envelopeM N m/envelopeScale N m*
      ((k:ℝ)/N+envelopeScale N m*(v-(m:ℝ)*k/N)/envelopeM N m-(k:ℝ)/N) =
      v-(m:ℝ)*k/N := by field_simp [hM.ne',ha.ne']; ring
  rw [hscale] at hval
  let t := bernoulliFenchelTilt ((k:ℝ)/N)
    ((k:ℝ)/N+envelopeScale N m*(v-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m
  have htne : t ≠ 0 := by
    intro ht
    have hc := scaledBernoulliMean_at_fenchel hM ha hp hp1 hθ.1 hθ.2
    rw [hscale] at hc
    change scaledBernoulliMean (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) t = _ at hc
    rw [ht] at hc
    simp only [scaledBernoulliMean_zero] at hc
    exact hvne (by linarith)
  have hglobal := (hypergeom_laplace_envelope N k m hm hmk hk hhalf).2
    (bernoulliFenchelTilt ((k:ℝ)/N)
      ((k:ℝ)/N+envelopeScale N m*(v-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m) htne
  dsimp [scaledKLRate]
  linarith [hval]

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

lemma hypergeom_contact_gap_pos (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (c : ℝ) (hc0 : 0 ≤ c) (hcm : c ≤ m) (hcne : c ≠ (m:ℝ)*k/N) :
    let t := bernoulliFenchelTilt ((k:ℝ)/N)
      ((k:ℝ)/N+envelopeScale N m*(c-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m
    0 < scaledBernoulliLogLaplace (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) t-
      hypergeomCenteredLogMGF N k m t := by
  dsimp only
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : 0 < (k:ℝ)/N := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/N < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hM := envelopeM_positive (N:ℝ) m hmR hhR
  have ha : 0 < envelopeScale N m := div_pos (by linarith) (by linarith)
  have hθ := scaledKL_argument_mem_Ioo hmR hmkR hkR hhR hc0 hcm
  let t := bernoulliFenchelTilt ((k:ℝ)/N)
    ((k:ℝ)/N+envelopeScale N m*(c-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m
  have htne : t ≠ 0 := by
    intro ht
    have hc := scaledBernoulliMean_at_fenchel hM ha hp hp1 hθ.1 hθ.2
    have hid : envelopeM N m/envelopeScale N m*
        ((k:ℝ)/N+envelopeScale N m*(c-(m:ℝ)*k/N)/envelopeM N m-(k:ℝ)/N) =
        c-(m:ℝ)*k/N := by field_simp [hM.ne',ha.ne']; ring
    rw [hid] at hc
    change scaledBernoulliMean (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) t = _ at hc
    rw [ht] at hc
    simp only [scaledBernoulliMean_zero] at hc
    exact hcne (by linarith)
  exact sub_pos.mpr ((hypergeom_laplace_envelope N k m hm hmk hk hhalf).2 t htne)

lemma outerKLRate_continuous {M p a m μ c : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Continuous (outerKLRate M p a m μ c) := by
  have hIB : Continuous (binomialKLRate m p) :=
    continuous_const.mul ((bernoulliKL_continuous p hp hp1).comp (continuous_id.div_const m))
  exact (((hIB.add continuous_const).sub continuous_const).add
    ((continuous_id.sub continuous_const).mul continuous_const))

/-- The strict contact gap survives the upper support endpoint. -/
theorem hypergeom_upper_outer_endpoint_strict (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (c : ℝ) (hμc : (m:ℝ)*k/N < c) (hcm : c < m) :
    outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) m ((m:ℝ)*k/N) c m <
      hypergeomKLRate N k m m := by
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hk0 : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hp : 0 < (k:ℝ)/N := div_pos hk0 hN
  have hp1 : (k:ℝ)/N < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hc0 : 0 < c := (div_pos (mul_pos hm0 hk0) hN).trans hμc
  let t := bernoulliFenchelTilt ((k:ℝ)/N)
    ((k:ℝ)/N+envelopeScale N m*(c-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m
  let δ := scaledBernoulliLogLaplace (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) t-
    hypergeomCenteredLogMGF N k m t
  have hδ : 0 < δ := hypergeom_contact_gap_pos N k m hm hmk hk hhalf c hc0.le hcm.le
    (ne_of_gt hμc)
  have hcont := ((outerKLRate_continuous (M := envelopeM N m) (a := envelopeScale N m)
    (m := (m:ℝ)) (μ := (m:ℝ)*k/N) (c := c) hp hp1).add (continuous_const (y := δ))).neg
  have hend : -(hypergeomKLRate N k m m) ≤
      -(outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) m ((m:ℝ)*k/N) c m+δ) := by
    apply le_at_right_endpoint hcont hcm
    intro v hcv hvm
    obtain ⟨s,hs,hgap⟩ := hypergeom_upper_outer_kl_contact_gap N k m hm hmk hk hhalf c v hμc hcm hcv hvm
    change outerKLRate _ _ _ _ _ _ v+δ ≤ _ at hgap
    have hmono : s*(v-(m:ℝ)*k/N) ≤ s*((m:ℝ)-(m:ℝ)*k/N) :=
      mul_le_mul_of_nonneg_left (by linarith) hs
    have hI := hypergeomKLRate_ge_fenchel N k m hmk (by omega) m hm0.le le_rfl s
    change -hypergeomKLRate N k m m ≤ -(outerKLRate _ _ _ _ _ _ v+δ)
    linarith
  linarith

/-- The strict contact gap survives the lower support endpoint. -/
theorem hypergeom_lower_outer_endpoint_strict (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (c : ℝ) (hcμ : c < (m:ℝ)*k/N) (hc0 : 0 < c) :
    outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) m ((m:ℝ)*k/N) c 0 <
      hypergeomKLRate N k m 0 := by
  have hN : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hp : 0 < (k:ℝ)/N := div_pos (by exact_mod_cast (show 0 < k by omega)) hN
  have hp1 : (k:ℝ)/N < 1 := (div_lt_one hN).2 (by exact_mod_cast (show k < N by omega))
  have hμm : (m:ℝ)*k/N < m := by
    apply (div_lt_iff₀ hN).2
    exact mul_lt_mul_of_pos_left (show (k:ℝ) < N by exact_mod_cast (show k < N by omega)) hm0
  have hcm : c < m := hcμ.trans hμm
  let t := bernoulliFenchelTilt ((k:ℝ)/N)
    ((k:ℝ)/N+envelopeScale N m*(c-(m:ℝ)*k/N)/envelopeM N m)/envelopeScale N m
  let δ := scaledBernoulliLogLaplace (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) t-
    hypergeomCenteredLogMGF N k m t
  have hδ : 0 < δ := hypergeom_contact_gap_pos N k m hm hmk hk hhalf c hc0.le hcm.le
    (ne_of_lt hcμ)
  have hcont := ((outerKLRate_continuous (M := envelopeM N m) (a := envelopeScale N m)
    (m := (m:ℝ)) (μ := (m:ℝ)*k/N) (c := c) hp hp1).add (continuous_const (y := δ))).neg
  have hend : -(hypergeomKLRate N k m 0) ≤
      -(outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) m ((m:ℝ)*k/N) c 0+δ) := by
    apply le_at_left_endpoint hcont hc0
    intro v hv0 hvc
    obtain ⟨s,hs,hgap⟩ := hypergeom_lower_outer_kl_contact_gap N k m hm hmk hk hhalf c v hcμ hc0 hvc hv0
    change outerKLRate _ _ _ _ _ _ v+δ ≤ _ at hgap
    have hmono : s*(v-(m:ℝ)*k/N) ≤ s*(0-(m:ℝ)*k/N) :=
      mul_le_mul_of_nonpos_left (by linarith) hs
    have hI := hypergeomKLRate_ge_fenchel N k m hmk (by omega) 0 le_rfl hm0.le s
    change -hypergeomKLRate N k m 0 ≤ -(outerKLRate _ _ _ _ _ _ v+δ)
    linarith
  linarith

end
end ExactHoeffding

namespace ExactHoeffding
noncomputable section

/-- The actual hypergeometric Legendre rate strictly dominates the closed
piecewise KL rate throughout the support, except at the mean. -/
theorem hypergeomKLRate_strict_piecewise (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) (hvne : v ≠ (m:ℝ)*k/N) :
    canonicalPiecewiseRate N k m v < hypergeomKLRate N k m v := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  let μ : ℝ := (m:ℝ)*k/N
  let rm := varianceSwitchMinus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
  let rp := varianceSwitchPlus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
  have hr := kl_switching_points_full_domain (N:ℝ) k m hmR hmkR hkR hhR
  change 0 < rm ∧ rm < μ ∧ μ < rp ∧ rp < m at hr
  by_cases hl : v < rm
  · have hJ : canonicalPiecewiseRate N k m v =
        outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) m μ rm v := by
      unfold canonicalPiecewiseRate
      rw [piecewiseKLRate_eq_left hl]
      rfl
    rw [hJ]
    rcases hv0.eq_or_lt with hv | hv
    · rw [← hv]
      exact hypergeom_lower_outer_endpoint_strict N k m hm hmk hk hhalf rm hr.2.1 hr.1
    · obtain ⟨t,ht,hR⟩ := hypergeom_lower_outer_kl_strict_fenchel N k m hm hmk hk hhalf
        rm v hr.2.1 hr.1 hl.le hv
      exact hR.trans_le (hypergeomKLRate_ge_fenchel N k m hmk (by omega) v hv0 hvm t)
  · by_cases hh : v ≤ rp
    · have hJ : canonicalPiecewiseRate N k m v =
          scaledKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) μ v := by
        unfold canonicalPiecewiseRate
        rw [piecewiseKLRate_eq_central (le_of_not_gt hl) hh]
        rfl
      rw [hJ]
      have hR := hypergeom_central_kl_strict_fenchel N k m hm hmk hk hhalf v hv0 hvm hvne
      exact hR.trans_le (hypergeomKLRate_ge_fenchel N k m hmk (by omega) v hv0 hvm _)
    · have hroot : rm ≤ rp := by linarith [hr.2.1,hr.2.2.1]
      have hJ : canonicalPiecewiseRate N k m v =
          outerKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) m μ rp v := by
        unfold canonicalPiecewiseRate
        rw [piecewiseKLRate_eq_right (lt_of_not_ge hh) hroot]
        rfl
      rw [hJ]
      rcases hvm.eq_or_lt with hv | hv
      · rw [hv]
        exact hypergeom_upper_outer_endpoint_strict N k m hm hmk hk hhalf rp hr.2.2.1 hr.2.2.2
      · obtain ⟨t,ht,hR⟩ := hypergeom_upper_outer_kl_strict_fenchel N k m hm hmk hk hhalf
          rp v hr.2.2.1 hr.2.2.2 (le_of_not_ge hh) hv
        exact hR.trans_le (hypergeomKLRate_ge_fenchel N k m hmk (by omega) v hv0 hvm t)

/-- End-to-end piecewise KL theorem for the actual finite law: both tails,
strict comparison with the binomial KL rate and the actual Legendre rate,
and the exact central equality interval against the scaled KL rate. -/
theorem hypergeom_piecewise_kl_end_to_end (N k m : ℕ)
    (hm : 3 ≤ m) (hmk : m ≤ k) (hk : 2*k ≤ N) (hhalf : 2*m < N)
    (v : ℝ) (hv0 : 0 ≤ v) (hvm : v ≤ m) :
    let μ : ℝ := (m:ℝ)*k/N
    let J := canonicalPiecewiseRate N k m v
    let IP := scaledKLRate (envelopeM N m) ((k:ℝ)/N) (envelopeScale N m) μ v
    let rm := varianceSwitchMinus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
    let rp := varianceSwitchPlus μ (klSwitchC N m) (klSwitchH N k m) (klSwitchB N k m)
    (μ ≤ v → (∑ i ∈ Finset.range (m+1),
      if v ≤ (i:ℝ) then hypergeomMass N k m i else 0) ≤ Real.exp (-J)) ∧
    (v ≤ μ → (∑ i ∈ Finset.range (m+1),
      if (i:ℝ) ≤ v then hypergeomMass N k m i else 0) ≤ Real.exp (-J)) ∧
    (v ≠ μ → m*bernoulliKL ((k:ℝ)/N) (v/m) < J ∧ J < hypergeomKLRate N k m v) ∧
    IP ≤ J ∧ (IP = J ↔ rm ≤ v ∧ v ≤ rp) ∧ (IP < J ↔ v < rm ∨ rp < v) := by
  have hmR : (3:ℝ) ≤ m := by exact_mod_cast hm
  have hmkR : (m:ℝ) ≤ k := by exact_mod_cast hmk
  have hkR : 2*(k:ℝ) ≤ N := by exact_mod_cast hk
  have hhR : 2*(m:ℝ) < N := by exact_mod_cast hhalf
  exact ⟨(fun h => hypergeom_upper_tail_piecewise_kl N k m hm hmk hk hhalf v h hvm),
    (fun h => hypergeom_lower_tail_piecewise_kl N k m hm hmk hk hhalf v h hv0),
    (fun h => ⟨canonicalPiecewiseRate_strict_improves_binomial hmR hmkR hkR hhR v h,
      hypergeomKLRate_strict_piecewise N k m hm hmk hk hhalf v hv0 hvm h⟩),
    canonicalPiecewiseRate_quadratic_comparison hmR hmkR hkR hhR hv0 hvm⟩

end
end ExactHoeffding
