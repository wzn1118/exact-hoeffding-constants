import ExactHoeffding.FixedSampleDiscreteBounds
import ExactHoeffding.FixedMarginSeparation

/-! # Eventual all-success-count extremizers for every fixed sample size

A single off-center singleton envelope bounds every interior noncentral
success count. Its second-order coefficient is strictly smaller than the
central fixed-sample coefficient. Boundary counts have an algebraic bound
below one, whereas the central normalized variance is above one.
-/

namespace ExactHoeffding
noncomputable section
open Set Filter
open scoped Topology

/-- The central fixed-sample optimum eventually exceeds the one singleton
envelope controlling every noncentral interior success count. -/
theorem odd_fixed_sample_center_eventually_gt_offcenter_singleton
    (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop,
      normalizedHypergeomProxy (2 * n + 1) (n - 1) 1 <
        normalizedHypergeomProxy (2 * n + 1) n m := by
  have hN : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  apply normalizedHypergeomProxy_fixed_margin_eventually_lt
    m 1 hm (by omega) 1 3 (by norm_num) (by norm_num)
    (fun n => 2 * n + 1) (fun n => n) (fun n => n - 1) hN
  · filter_upwards [eventually_ge_atTop m] with n hn
    refine ⟨by omega, by omega, ?_⟩
    push_cast
    ring
  · filter_upwards [eventually_ge_atTop 1] with n hn
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.cast_sub hn]
    push_cast
    ring

/-- Uniform over all success counts: for every fixed sample size at least
two, the central success counts are eventually the only maximizers. -/
theorem odd_fixed_sample_all_success_eventually (m : ℕ) (hm : 2 ≤ m) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, 0 < k → k < 2 * n + 1 →
      normalizedHypergeomProxy (2 * n + 1) k m ≤
          normalizedHypergeomProxy (2 * n + 1) n m ∧
        (normalizedHypergeomProxy (2 * n + 1) k m =
          normalizedHypergeomProxy (2 * n + 1) n m ↔ k = n ∨ k = n + 1) := by
  filter_upwards [odd_fixed_sample_center_eventually_gt_offcenter_singleton m (by omega),
    eventually_ge_atTop (2 * m * (m + 1))] with n hsep hn
  have hn0 : 0 < n := by nlinarith
  have hmN : m < 2 * n + 1 := by nlinarith
  have hlarge : 2 * m * (m + 1) ≤ 2 * n + 1 := by omega
  have hcenter : 1 < normalizedHypergeomProxy (2 * n + 1) n m :=
    odd_normalized_proxy_center_gt_one n m hn0 (by omega) hmN
  have hlower (k : ℕ) (hk : 0 < k) (hkn : k < n) :
      normalizedHypergeomProxy (2 * n + 1) k m <
        normalizedHypergeomProxy (2 * n + 1) n m := by
    by_cases hmk : m ≤ k
    · exact (odd_normalized_proxy_interior_lt_offcenter_singleton n k m hm hmk hkn).trans hsep
    · exact (normalizedHypergeomProxy_boundary_lt_one (2 * n + 1) k m
        (by omega) (by omega) hlarge).trans hcenter
  intro k hk hkN
  have hequal (h : k = n ∨ k = n + 1) :
      normalizedHypergeomProxy (2 * n + 1) k m =
        normalizedHypergeomProxy (2 * n + 1) n m := by
    rcases h with rfl | rfl
    · rfl
    · rw [normalizedHypergeomProxy_success_complement (2 * n + 1) (n + 1) m
        (by omega) hmN.le (by omega)]
      rw [show 2 * n + 1 - (n + 1) = n by omega]
  by_cases hcentral : k = n ∨ k = n + 1
  · exact ⟨(hequal hcentral).le, ⟨fun _ => hcentral, hequal⟩⟩
  · have hstrict : normalizedHypergeomProxy (2 * n + 1) k m <
        normalizedHypergeomProxy (2 * n + 1) n m := by
      by_cases hkn : k ≤ n
      · exact hlower k hk (by omega)
      · rw [normalizedHypergeomProxy_success_complement (2 * n + 1) k m
          hkN.le hmN.le (by omega)]
        exact hlower (2 * n + 1 - k) (by omega) (by omega)
    exact ⟨hstrict.le, ⟨fun heq => False.elim ((ne_of_lt hstrict) heq),
      fun h => False.elim (hcentral h)⟩⟩

/-- The fixed-sample result includes the singleton case and supplies the
strict comparison with the odd global constant when the sample has at least
two elements. -/
theorem odd_fixed_sample_global_extremizers (m : ℕ) (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, m < 2 * n + 1 ∧
      (∀ k : ℕ, 0 < k → k < 2 * n + 1 →
        normalizedHypergeomProxy (2 * n + 1) k m ≤
            normalizedHypergeomProxy (2 * n + 1) n m ∧
          (normalizedHypergeomProxy (2 * n + 1) k m =
            normalizedHypergeomProxy (2 * n + 1) n m ↔ k = n ∨ k = n + 1)) ∧
      (2 ≤ m → normalizedHypergeomProxy (2 * n + 1) n m <
        oddHypergeomConstant (2 * n + 1)) := by
  by_cases hm1 : m = 1
  · subst m
    filter_upwards [eventually_ge_atTop 1] with n hn
    have heq : normalizedHypergeomProxy (2 * n + 1) n 1 =
        oddHypergeomConstant (2 * n + 1) :=
      (odd_normalized_proxy_all_equality n n 1 (by omega) (by omega)
        (by omega) (by omega) (by omega)).mpr ⟨Or.inl rfl, Or.inl rfl⟩
    refine ⟨by omega, ?_, by omega⟩
    intro k hk hkN
    rw [heq]
    refine ⟨odd_normalized_proxy_all_upper n k 1 (by omega) hk hkN
      (by omega) (by omega), ?_⟩
    rw [odd_normalized_proxy_all_equality n k 1 (by omega) hk hkN
      (by omega) (by omega)]
    simp
  · have hm2 : 2 ≤ m := by omega
    filter_upwards [odd_fixed_sample_all_success_eventually m hm2,
      eventually_ge_atTop m] with n hn hnm
    have hn0 : 0 < n := by omega
    have hmN : m < 2 * n + 1 := by omega
    refine ⟨hmN, hn, ?_⟩
    intro _
    have hle := odd_normalized_proxy_all_upper n n m hn0 hn0 (by omega) hm hmN
    apply lt_of_le_of_ne hle
    intro heq
    have hbad := (odd_normalized_proxy_all_equality n n m hn0 hn0
      (by omega) hm hmN).mp heq
    omega

/-- Original population notation: one threshold controls every success
count at each fixed sample size, and exactly the two central counts attain
the maximum. -/
theorem odd_fixed_sample_global_extremizers_population (m : ℕ) (hm : 0 < m) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Odd N →
      m < N ∧
        (∀ k : ℕ, 0 < k → k < N →
          normalizedHypergeomProxy N k m ≤ normalizedHypergeomProxy N (N / 2) m ∧
            (normalizedHypergeomProxy N k m = normalizedHypergeomProxy N (N / 2) m ↔
              k = N / 2 ∨ k = N / 2 + 1)) ∧
        (2 ≤ m → normalizedHypergeomProxy N (N / 2) m < oddHypergeomConstant N) := by
  obtain ⟨n₀, hn₀⟩ := (eventually_atTop.mp (odd_fixed_sample_global_extremizers m hm))
  refine ⟨2 * n₀ + 1, ?_⟩
  intro N hN hodd
  rcases hodd with ⟨n, rfl⟩
  have hhalf : (2 * n + 1) / 2 = n := by omega
  simpa only [hhalf] using hn₀ n (by omega)

/-- Every finite set of fixed sample sizes shares one population threshold.
The conclusion includes the maximum and all equality cases for each sample. -/
theorem odd_fixed_sample_finite_range_extremizers (M : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Odd N → ∀ m : ℕ, 0 < m → m ≤ M →
      m < N ∧
        (∀ k : ℕ, 0 < k → k < N →
          normalizedHypergeomProxy N k m ≤ normalizedHypergeomProxy N (N / 2) m ∧
            (normalizedHypergeomProxy N k m = normalizedHypergeomProxy N (N / 2) m ↔
              k = N / 2 ∨ k = N / 2 + 1)) ∧
        (2 ≤ m → normalizedHypergeomProxy N (N / 2) m < oddHypergeomConstant N) := by
  induction M with
  | zero =>
      refine ⟨0, ?_⟩
      intros
      omega
  | succ M hM =>
      obtain ⟨N₀, hN₀⟩ := hM
      obtain ⟨N₁, hN₁⟩ := odd_fixed_sample_global_extremizers_population (M + 1) (by omega)
      refine ⟨max N₀ N₁, ?_⟩
      intro N hN hodd m hm hmM
      by_cases hmM' : m ≤ M
      · exact hN₀ N (le_trans (le_max_left _ _) hN) hodd m hm hmM'
      · have hmeq : m = M + 1 := by omega
        subst m
        exact hN₁ N (le_trans (le_max_right _ _) hN) hodd

/-- The paper's simultaneous strict singleton comparison for every sample
size in a fixed finite range and every success count. -/
theorem odd_fixed_sample_finite_range_below_singleton (M : ℕ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Odd N → ∀ m k : ℕ,
      2 ≤ m → m ≤ M → 0 < k → k < N →
        normalizedHypergeomProxy N k m < oddHypergeomConstant N := by
  obtain ⟨N₀, hN₀⟩ := odd_fixed_sample_finite_range_extremizers M
  refine ⟨N₀, ?_⟩
  intro N hN hodd m k hm hmM hk hkN
  obtain ⟨_, hmax, hstrict⟩ := hN₀ N hN hodd m (by omega) hmM
  exact (hmax k hk hkN).1.trans_lt (hstrict hm)

end
end ExactHoeffding
