import ExactHoeffding.SharpCurvatureTheorem
import ExactHoeffding.CanonicalCurvatureEquality
import ExactHoeffding.SmallSupportEquality

namespace ExactHoeffding

theorem hypergeomTiltVariance_canonical_equality_iff (N k m : ℕ)
    (hmk : m≤k) (hkm : k+m≤N) (hm : 2≤m) (t : ℝ) :
    hypergeomTiltVariance N k m t=sharpCurvatureConstant N k m ↔
      t=0 ∧ 2*k=N := by
  have horder := canonical_margin_product_order (N:ℝ) (k:ℝ) (m:ℝ)
    (by exact_mod_cast hmk) (by exact_mod_cast hkm)
  unfold sharpCurvatureConstant
  rw [min_eq_right horder]
  by_cases hm2 : m=2
  · subst m
    rw [← hypergeomLogMGF_second_deriv_eq_variance N k 2 (by omega) (by omega) t]
    have hN1 : (N:ℝ)-1≠0 := by
      have hn : (4:ℝ)≤N := by exact_mod_cast (show 4≤N by omega)
      linarith
    have hB : (2:ℝ)*((N:ℝ)-2)/(4*((N:ℝ)-1))=((N:ℝ)-2)/(2*((N:ℝ)-1)) := by
      field_simp [hN1]
      ring
    simp only [Nat.cast_ofNat]
    rw [hB,hypergeom_two_draw_curvature_equality_iff N k hmk hkm t]
    constructor
    · rintro ⟨hN,ht⟩; exact ⟨ht,hN.symm⟩
    · rintro ⟨ht,hN⟩; exact ⟨hN.symm,ht⟩
  · have hm3 : 3≤m := by omega
    let r := N-(k+m)
    have hN : k+m+r=N := Nat.add_sub_of_le hkm
    have hr : (r:ℝ)=(N:ℝ)-k-m := by dsimp [r]; rw [Nat.cast_sub hkm,Nat.cast_add]; ring
    have h := hypergeomTiltVariance_sharp_canonical_equality_iff k m r hmk hm3 t
    rw [hN,hr] at h
    have hB : (m:ℝ)*((k:ℝ)+((N:ℝ)-k-m))/(4*((k:ℝ)+m+((N:ℝ)-k-m)-1))=
        (m:ℝ)*((N:ℝ)-m)/(4*((N:ℝ)-1)) := by ring
    rw [hB] at h
    rw [h]
    constructor
    · rintro ⟨hkbal,ht⟩
      exact ⟨ht,by omega⟩
    · rintro ⟨ht,hkbal⟩
      exact ⟨by omega,ht⟩

theorem hypergeomTiltVariance_half_margins_equality_iff (N k m : ℕ)
    (hk2 : 2≤k) (hm2 : 2≤m) (hkhalf : 2*k≤N) (hmhalf : 2*m≤N) (t : ℝ) :
    hypergeomTiltVariance N k m t=sharpCurvatureConstant N k m ↔
      t=0 ∧ (2*k=N ∨ 2*m=N) := by
  by_cases hmk : m≤k
  · rw [hypergeomTiltVariance_canonical_equality_iff N k m hmk (by omega) hm2 t]
    constructor
    · rintro ⟨ht,hk⟩; exact ⟨ht,Or.inl hk⟩
    · rintro ⟨ht,hk | hm⟩
      · exact ⟨ht,hk⟩
      · exact ⟨ht,by omega⟩
  · rw [hypergeomTiltVariance_transpose N k m (by omega) (by omega) t,
      sharpCurvatureConstant_transpose N k m,
      hypergeomTiltVariance_canonical_equality_iff N m k (by omega) (by omega) hk2 t]
    constructor
    · rintro ⟨ht,hm⟩; exact ⟨ht,Or.inr hm⟩
    · rintro ⟨ht,hk | hm⟩
      · exact ⟨ht,by omega⟩
      · exact ⟨ht,hm⟩

/-- All non-singleton and nondegenerate original margins attain the sharp
curvature envelope exactly at zero tilt with at least one balanced margin. -/
theorem hypergeomTiltVariance_interior_equality_iff (N k m : ℕ)
    (hk2 : 2≤k) (hkN2 : k+2≤N) (hm2 : 2≤m) (hmN2 : m+2≤N) (t : ℝ) :
    hypergeomTiltVariance N k m t=sharpCurvatureConstant N k m ↔
      t=0 ∧ (2*k=N ∨ 2*m=N) := by
  have hk : k≤N := by omega
  have hm : m≤N := by omega
  have hkc : 2*(N-k)=N ↔ 2*k=N := by omega
  have hmc : 2*(N-m)=N ↔ 2*m=N := by omega
  by_cases hkhalf : 2*k≤N
  · by_cases hmhalf : 2*m≤N
    · exact hypergeomTiltVariance_half_margins_equality_iff N k m hk2 hm2 hkhalf hmhalf t
    · rw [hypergeomTiltVariance_sample_complement N k m hk hm t,
        ← sharpCurvatureConstant_sample_complement N k m hm,
        hypergeomTiltVariance_half_margins_equality_iff N k (N-m) hk2 (by omega)
          hkhalf (by omega) (-t),neg_eq_zero,hmc]
  · rw [hypergeomTiltVariance_success_complement N k m hk hm t,
      ← sharpCurvatureConstant_success_complement N k m hk]
    by_cases hmhalf : 2*m≤N
    · rw [hypergeomTiltVariance_half_margins_equality_iff N (N-k) m (by omega) hm2
        (by omega) hmhalf (-t),neg_eq_zero,hkc]
    · rw [hypergeomTiltVariance_sample_complement N (N-k) m (Nat.sub_le _ _) hm (-t),
        ← sharpCurvatureConstant_sample_complement N (N-k) m hm,
        hypergeomTiltVariance_half_margins_equality_iff N (N-k) (N-m) (by omega) (by omega)
          (by omega) (by omega) (-(-t)),neg_neg,hkc,hmc]

theorem sharpCurvatureConstant_one_draw (N k : ℕ) (hk0 : 0<k) (hkN : k<N) :
    sharpCurvatureConstant N k 1=1/4 := by
  have horder := canonical_margin_product_order (N:ℝ) (k:ℝ) 1
    (by exact_mod_cast hk0) (by exact_mod_cast (show k+1≤N by omega))
  have hN1 : (N:ℝ)-1≠0 := by
    have hN : (2:ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
    linarith
  unfold sharpCurvatureConstant
  simp only [Nat.cast_one,one_mul] at horder ⊢
  rw [min_eq_right horder]
  field_simp [hN1]

theorem hypergeomTiltVariance_one_draw_equality_iff (N k : ℕ)
    (hk0 : 0<k) (hkN : k<N) (t : ℝ) :
    hypergeomTiltVariance N k 1 t=sharpCurvatureConstant N k 1 ↔
      t=Real.log (((N:ℝ)-k)/k) := by
  rw [sharpCurvatureConstant_one_draw N k hk0 hkN,
    ← hypergeomLogMGF_second_deriv_eq_variance N k 1 hkN.le (by omega) t]
  exact hypergeom_one_draw_curvature_equality_iff N k hk0 hkN t

theorem hypergeomTiltVariance_one_mark_equality_iff (N m : ℕ)
    (hm0 : 0<m) (hmN : m<N) (t : ℝ) :
    hypergeomTiltVariance N 1 m t=sharpCurvatureConstant N 1 m ↔
      t=Real.log (((N:ℝ)-m)/m) := by
  rw [hypergeomTiltVariance_transpose N 1 m (by omega) hmN.le t,
    sharpCurvatureConstant_transpose N 1 m]
  exact hypergeomTiltVariance_one_draw_equality_iff N m hm0 hmN t

theorem hypergeomTiltVariance_complement_one_draw_equality_iff (N k : ℕ)
    (hk0 : 0<k) (hkN : k<N) (t : ℝ) :
    hypergeomTiltVariance N k (N-1) t=sharpCurvatureConstant N k (N-1) ↔
      t= -Real.log (((N:ℝ)-k)/k) := by
  rw [hypergeomTiltVariance_sample_complement N k (N-1) hkN.le (Nat.sub_le _ _) t,
    ← sharpCurvatureConstant_sample_complement N k (N-1) (Nat.sub_le _ _)]
  have hN : N-(N-1)=1 := by omega
  rw [hN,hypergeomTiltVariance_one_draw_equality_iff N k hk0 hkN (-t)]
  constructor <;> intro h <;> linarith

theorem hypergeomTiltVariance_complement_one_mark_equality_iff (N m : ℕ)
    (hm0 : 0<m) (hmN : m<N) (t : ℝ) :
    hypergeomTiltVariance N (N-1) m t=sharpCurvatureConstant N (N-1) m ↔
      t= -Real.log (((N:ℝ)-m)/m) := by
  rw [hypergeomTiltVariance_transpose N (N-1) m (Nat.sub_le _ _) hmN.le t,
    sharpCurvatureConstant_transpose N (N-1) m]
  exact hypergeomTiltVariance_complement_one_draw_equality_iff N m hm0 hmN t

theorem hypergeomTiltVariance_zero_marks_equality (N m : ℕ) (hm : m≤N) (t : ℝ) :
    hypergeomTiltVariance N 0 m t=sharpCurvatureConstant N 0 m := by
  rw [← hypergeomLogMGF_second_deriv_eq_variance N 0 m (by omega) hm t,
    hypergeom_curvature_zero_marks N m hm t]
  have hp : 0≤(m:ℝ)*((N:ℝ)-m) := by
    apply mul_nonneg (Nat.cast_nonneg _)
    exact sub_nonneg.mpr (by exact_mod_cast hm)
  simp [sharpCurvatureConstant,min_eq_left hp]

theorem hypergeomTiltVariance_zero_draws_equality (N k : ℕ) (hk : k≤N) (t : ℝ) :
    hypergeomTiltVariance N k 0 t=sharpCurvatureConstant N k 0 := by
  rw [hypergeomTiltVariance_transpose N k 0 hk (by omega) t,
    sharpCurvatureConstant_transpose N k 0]
  exact hypergeomTiltVariance_zero_marks_equality N k hk t

theorem hypergeomTiltVariance_full_marks_equality (N m : ℕ) (hm : m≤N) (t : ℝ) :
    hypergeomTiltVariance N N m t=sharpCurvatureConstant N N m := by
  rw [hypergeomTiltVariance_success_complement N N m le_rfl hm t,
    ← sharpCurvatureConstant_success_complement N N m le_rfl,Nat.sub_self]
  exact hypergeomTiltVariance_zero_marks_equality N m hm (-t)

theorem hypergeomTiltVariance_full_draws_equality (N k : ℕ) (hk : k≤N) (t : ℝ) :
    hypergeomTiltVariance N k N t=sharpCurvatureConstant N k N := by
  rw [hypergeomTiltVariance_transpose N k N hk le_rfl t,
    sharpCurvatureConstant_transpose N k N]
  exact hypergeomTiltVariance_full_marks_equality N k hk t


end ExactHoeffding
