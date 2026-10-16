import ExactHoeffding.ProxyQuotient
import ExactHoeffding.RescaledActualProxy
import ExactHoeffding.GoalBOddVariation

namespace ExactHoeffding
noncomputable section

open Set Filter
open scoped Topology

/-- A continuous real curve with positive value at zero and vanishing tails
attains a global maximum. -/
theorem exists_global_max_of_continuous_tails_pos {f : ℝ → ℝ}
    (hc : Continuous f) (hpos : 0 < f 0)
    (hbot : Tendsto f atBot (𝓝 0)) (htop : Tendsto f atTop (𝓝 0)) :
    ∃ t : ℝ, ∀ u : ℝ, f u ≤ f t := by
  obtain ⟨L, hL⟩ := eventually_atBot.mp
    (hbot.eventually (Iio_mem_nhds hpos))
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (htop.eventually (Iio_mem_nhds hpos))
  let a := min L 0 - 1
  let b := max R 0 + 1
  have ha : a ≤ 0 := by
    dsimp [a]
    linarith [min_le_right L 0]
  have hb : 0 ≤ b := by
    dsimp [b]
    linarith [le_max_right R 0]
  have hab : a ≤ b := ha.trans hb
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc a b).Nonempty from ⟨0, ha, hb⟩) hc.continuousOn
  refine ⟨x, ?_⟩
  intro t
  by_cases hleft : t < a
  · have htL : t ≤ L := by
      have haL : a ≤ L := by
        dsimp [a]
        linarith [min_le_left L 0]
      exact (le_of_lt hleft).trans haL
    exact (hL t htL).le.trans (hmax ⟨ha, hb⟩)
  · by_cases hright : b < t
    · have hRt : R ≤ t := by
        have hRb : R ≤ b := by
          dsimp [b]
          linarith [le_max_left R 0]
        exact hRb.trans (le_of_lt hright)
      exact (hR t hRt).le.trans (hmax ⟨ha, hb⟩)
    · exact hmax ⟨le_of_not_gt hleft, le_of_not_gt hright⟩

/-- The completed quadratic proxy agrees pointwise with the actual
hypergeometric proxy, including the removable zero-tilt value. -/
theorem actualHypergeomProxy_eq_hypergeomProxyQuotient (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    actualHypergeomProxy N k m t = hypergeomProxyQuotient N k m t := by
  by_cases ht : t = 0
  · subst t
    simp [actualHypergeomProxy, hypergeomProxyQuotient,
      hypergeom_cumulant2_complete N k m hk hm,
      hypergeomTiltVariance_zero N k m hk hm]
  · simp only [actualHypergeomProxy, if_neg ht, hypergeomProxyQuotient,
      Function.update_of_ne ht]
    rw [hypergeom_centered_log_identity N k m hk hm]
    field_simp [ht]
    unfold hypergeomCenteredLogMGF
    ring

/-- Every nondegenerate canonical finite hypergeometric law has an attained
maximum of its actual quadratic proxy. -/
theorem actualHypergeomProxy_exists_global_max_canonical (k m r : ℕ)
    (hmk : m ≤ k) (hm : 0 < m) :
    ∃ t : ℝ, ∀ u : ℝ,
      actualHypergeomProxy (k + m + r) k m u ≤
        actualHypergeomProxy (k + m + r) k m t := by
  let N := k + m + r
  have hN : 2 ≤ N := by
    dsimp [N]
    omega
  have hkN : k ≤ N := by dsimp [N]; omega
  have hmN : m ≤ N := by dsimp [N]; omega
  have hcont : Continuous (hypergeomProxyQuotient N k m) :=
    hypergeomProxyQuotient_continuous N k m hkN hmN
  have hvar : 0 < hypergeomTiltVariance N k m 0 := by
    dsimp [N]
    exact hypergeomTiltVariance_pos k m r hmk hm 0
  have hzero : hypergeomProxyQuotient N k m 0 =
      hypergeomTiltVariance N k m 0 := by
    simp [hypergeomProxyQuotient]
  have hpos : 0 < hypergeomProxyQuotient N k m 0 := by
    rw [hzero]
    exact hvar
  have hbot : Tendsto (hypergeomProxyQuotient N k m) atBot (𝓝 0) := by
    dsimp [N]
    exact hypergeomProxyQuotient_tendsto_atBot k m r hmk hm
  have htop : Tendsto (hypergeomProxyQuotient N k m) atTop (𝓝 0) := by
    dsimp [N]
    exact hypergeomProxyQuotient_tendsto_atTop k m r hmk hm
  obtain ⟨t, ht⟩ := exists_global_max_of_continuous_tails_pos
    hcont hpos hbot htop
  refine ⟨t, ?_⟩
  intro u
  rw [actualHypergeomProxy_eq_hypergeomProxyQuotient N k m hkN hmN]
  rw [actualHypergeomProxy_eq_hypergeomProxyQuotient N k m hkN hmN]
  exact ht u

end
end ExactHoeffding


namespace ExactHoeffding
noncomputable section

/-- Actual proxy commutes with transposition of the hypergeometric table. -/
theorem actualHypergeomProxy_transpose (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (t : ℝ) :
    actualHypergeomProxy N k m t = actualHypergeomProxy N m k t := by
  rw [actualHypergeomProxy_eq_hypergeomProxyQuotient N k m hk hm t,
    actualHypergeomProxy_eq_hypergeomProxyQuotient N m k hm hk t]
  unfold hypergeomProxyQuotient
  by_cases ht : t = 0
  · simp [ht, hypergeomTiltVariance_transpose N k m hk hm]
  · simp only [Function.update_of_ne ht]
    rw [hypergeomCenteredLogMGF_transpose N k m hk hm t]

/-- Actual proxy commutes with success complementation, with reflected tilt. -/
theorem actualHypergeomProxy_success_complement (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (hN : 0 < N) (t : ℝ) :
    actualHypergeomProxy N k m t =
      actualHypergeomProxy N (N - k) m (-t) := by
  rw [actualHypergeomProxy_eq_hypergeomProxyQuotient N k m hk hm t,
    actualHypergeomProxy_eq_hypergeomProxyQuotient N (N-k) m (Nat.sub_le _ _) hm (-t)]
  unfold hypergeomProxyQuotient
  by_cases ht : t = 0
  · simp [ht, hypergeomTiltVariance_success_complement N k m hk hm]
  · have hneg : -t ≠ 0 := neg_ne_zero.mpr ht
    simp only [Function.update_of_ne ht, Function.update_of_ne hneg]
    rw [hypergeomCenteredLogMGF_success_complement N k m hk hm hN t]
    ring

/-- Actual proxy commutes with sample complementation, with reflected tilt. -/
theorem actualHypergeomProxy_sample_complement (N k m : ℕ)
    (hk : k ≤ N) (hm : m ≤ N) (hN : 0 < N) (t : ℝ) :
    actualHypergeomProxy N k m t =
      actualHypergeomProxy N k (N - m) (-t) := by
  rw [actualHypergeomProxy_transpose N k m hk hm t,
    actualHypergeomProxy_success_complement N m k hm hk hN t,
    actualHypergeomProxy_transpose N (N-m) k (Nat.sub_le _ _) hk (-t)]

/-- Canonical-parameter form of the attained-maximizer theorem. -/
theorem actualHypergeomProxy_exists_global_max_canonical_params (N k m : ℕ)
    (hmk : m ≤ k) (hkm : k + m ≤ N) (hm : 0 < m) :
    ∃ t : ℝ, ∀ u : ℝ,
      actualHypergeomProxy N k m u ≤
        actualHypergeomProxy N k m t := by
  obtain ⟨t, ht⟩ := actualHypergeomProxy_exists_global_max_canonical
    k m (N - (k + m)) hmk hm
  have hsum : k + m + (N - (k + m)) = N := Nat.add_sub_of_le hkm
  rw [hsum] at ht
  exact ⟨t, ht⟩

end
end ExactHoeffding


namespace ExactHoeffding
noncomputable section

/-- A global maximum transports through a sign change of the tilt. -/
theorem exists_global_max_of_sign_reparam {f g : ℝ → ℝ} (σ : ℝ)
    (hσ : σ = 1 ∨ σ = -1)
    (hrel : ∀ t : ℝ, f t = g (σ * t))
    (hg : ∃ s : ℝ, ∀ u : ℝ, g u ≤ g s) :
    ∃ t : ℝ, ∀ u : ℝ, f u ≤ f t := by
  rcases hσ with rfl | rfl
  · obtain ⟨s, hs⟩ := hg
    refine ⟨s, ?_⟩
    intro u
    rw [hrel u, hrel s]
    simpa using hs u
  · obtain ⟨s, hs⟩ := hg
    refine ⟨-s, ?_⟩
    intro u
    rw [hrel u, hrel (-s)]
    simpa using hs (-u)

/-- Every nondegenerate finite hypergeometric proxy attains its global
maximum.  Complementing either margin reduces to the canonical half-table
case; transposition then orders the two reduced margins. -/
theorem actualHypergeomProxy_exists_global_max (N k m : ℕ)
    (hN : 2 ≤ N) (hk0 : 0 < k) (hkN : k < N)
    (hm0 : 0 < m) (hmN : m < N) :
    ∃ t : ℝ, ∀ u : ℝ,
      actualHypergeomProxy N k m u ≤ actualHypergeomProxy N k m t := by
  let kb : ℕ := min k (N - k)
  let mb : ℕ := min m (N - m)
  have hNpos : 0 < N := by omega
  have hk_le : k ≤ N := hkN.le
  have hm_le : m ≤ N := hmN.le
  have hkb_pos : 0 < kb := by
    by_cases hhalf : k ≤ N - k
    · rw [show kb = k by simp [kb, min_eq_left hhalf]]
      exact hk0
    · have hhalf' : N - k ≤ k := le_of_not_ge hhalf
      rw [show kb = N - k by simp [kb, min_eq_right hhalf']]
      omega
  have hmb_pos : 0 < mb := by
    by_cases hhalf : m ≤ N - m
    · rw [show mb = m by simp [mb, min_eq_left hhalf]]
      exact hm0
    · have hhalf' : N - m ≤ m := le_of_not_ge hhalf
      rw [show mb = N - m by simp [mb, min_eq_right hhalf']]
      omega
  have hkb_leN : kb ≤ N := by
    have hle : kb ≤ k := by
      dsimp [kb]
      exact min_le_left _ _
    exact hle.trans hk_le
  have hmb_leN : mb ≤ N := by
    have hle : mb ≤ m := by
      dsimp [mb]
      exact min_le_left _ _
    exact hle.trans hm_le
  have hkb_half : 2 * kb ≤ N := by
    by_cases hhalf : k ≤ N - k
    · rw [show kb = k by simp [kb, min_eq_left hhalf]]
      omega
    · have hhalf' : N - k ≤ k := le_of_not_ge hhalf
      rw [show kb = N - k by simp [kb, min_eq_right hhalf']]
      omega
  have hmb_half : 2 * mb ≤ N := by
    by_cases hhalf : m ≤ N - m
    · rw [show mb = m by simp [mb, min_eq_left hhalf]]
      omega
    · have hhalf' : N - m ≤ m := le_of_not_ge hhalf
      rw [show mb = N - m by simp [mb, min_eq_right hhalf']]
      omega
  have hsum : kb + mb ≤ N := by omega
  have hreduce : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∀ t : ℝ,
        actualHypergeomProxy N k m t =
          actualHypergeomProxy N kb mb (σ * t) := by
    by_cases hkhalf : k ≤ N - k
    · have hkb : kb = k := by simp [kb, min_eq_left hkhalf]
      by_cases hmhalf : m ≤ N - m
      · have hmb : mb = m := by simp [mb, min_eq_left hmhalf]
        refine ⟨1, Or.inl rfl, ?_⟩
        intro t
        simp [hkb, hmb]
      · have hmhalf' : N - m ≤ m := le_of_not_ge hmhalf
        have hmb : mb = N - m := by
          simp [mb, min_eq_right hmhalf']
        refine ⟨-1, Or.inr rfl, ?_⟩
        intro t
        rw [hkb, hmb]
        simpa using
          (actualHypergeomProxy_sample_complement N k m hk_le hm_le hNpos t)
    · have hkhalf' : N - k ≤ k := le_of_not_ge hkhalf
      have hkb : kb = N - k := by
        simp [kb, min_eq_right hkhalf']
      by_cases hmhalf : m ≤ N - m
      · have hmb : mb = m := by simp [mb, min_eq_left hmhalf]
        refine ⟨-1, Or.inr rfl, ?_⟩
        intro t
        rw [hkb, hmb]
        simpa using
          (actualHypergeomProxy_success_complement N k m hk_le hm_le hNpos t)
      · have hmhalf' : N - m ≤ m := le_of_not_ge hmhalf
        have hmb : mb = N - m := by
          simp [mb, min_eq_right hmhalf']
        refine ⟨1, Or.inl rfl, ?_⟩
        intro t
        rw [hkb, hmb]
        calc
          actualHypergeomProxy N k m t =
              actualHypergeomProxy N (N - k) m (-t) :=
            actualHypergeomProxy_success_complement N k m hk_le hm_le hNpos t
          _ = actualHypergeomProxy N (N - k) (N - m) (-(-t)) :=
            actualHypergeomProxy_sample_complement N (N - k) m
              (Nat.sub_le _ _) hm_le hNpos (-t)
          _ = actualHypergeomProxy N (N - k) (N - m) (1 * t) := by
            congr 1
            ring
  obtain ⟨σ, hσ, hred⟩ := hreduce
  by_cases horder : mb ≤ kb
  · exact exists_global_max_of_sign_reparam σ hσ hred
      (actualHypergeomProxy_exists_global_max_canonical_params N kb mb
        horder hsum hmb_pos)
  · have horder' : kb ≤ mb := le_of_not_ge horder
    have hcanon := actualHypergeomProxy_exists_global_max_canonical_params N mb kb
      horder' (by omega) hkb_pos
    apply exists_global_max_of_sign_reparam σ hσ
    · intro t
      calc
        actualHypergeomProxy N k m t =
            actualHypergeomProxy N kb mb (σ * t) := hred t
        _ = actualHypergeomProxy N mb kb (σ * t) :=
          actualHypergeomProxy_transpose N kb mb hkb_leN hmb_leN (σ * t)
    exact hcanon

end
end ExactHoeffding
