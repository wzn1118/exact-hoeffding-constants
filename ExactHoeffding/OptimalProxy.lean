import ExactHoeffding.VarianceOptimality
import ExactHoeffding.Symmetries

namespace ExactHoeffding
noncomputable section

/-- The least global quadratic coefficient, using the manuscript's
supremum over all nonzero real tilts. -/
def optimalProxy (ψ : ℝ→ℝ) : ℝ :=
  sSup {v : ℝ | ∃t : ℝ, t≠0 ∧ v=2*ψ t/t^2}

theorem proxyQuotientSet_nonempty (ψ : ℝ→ℝ) :
    ({v : ℝ | ∃t : ℝ, t≠0 ∧ v=2*ψ t/t^2} : Set ℝ).Nonempty := by
  exact ⟨2*ψ 1/1^2,1,by norm_num,rfl⟩

theorem proxyQuotientSet_bddAbove (ψ : ℝ→ℝ) (C : ℝ) (hC : IsQuadraticProxy ψ C) :
    BddAbove {v : ℝ | ∃t : ℝ, t≠0 ∧ v=2*ψ t/t^2} := by
  refine ⟨C,?_⟩
  rintro v ⟨t,ht,rfl⟩
  apply (div_le_iff₀ (sq_pos_of_ne_zero ht)).2
  nlinarith only [hC t]

theorem optimalProxy_le (ψ : ℝ→ℝ) (C : ℝ) (hC : IsQuadraticProxy ψ C) :
    optimalProxy ψ≤C := by
  apply csSup_le (proxyQuotientSet_nonempty ψ)
  rintro v ⟨t,ht,rfl⟩
  apply (div_le_iff₀ (sq_pos_of_ne_zero ht)).2
  nlinarith only [hC t]

theorem optimalProxy_isQuadraticProxy (ψ : ℝ→ℝ) (h0 : ψ 0=0)
    (C : ℝ) (hC : IsQuadraticProxy ψ C) : IsQuadraticProxy ψ (optimalProxy ψ) := by
  intro t
  by_cases ht : t=0
  · subst t
    simp [h0]
  · have h := le_csSup (proxyQuotientSet_bddAbove ψ C hC)
      (show 2*ψ t/t^2∈{v : ℝ | ∃s : ℝ,s≠0 ∧ v=2*ψ s/s^2} from ⟨t,ht,rfl⟩)
    have hh := (div_le_iff₀ (sq_pos_of_ne_zero ht)).mp h
    change ψ t≤optimalProxy ψ*t^2/2
    dsimp [optimalProxy]
    nlinarith only [hh]

theorem optimalProxy_eq_of_optimal (ψ : ℝ→ℝ) (h0 : ψ 0=0) (C : ℝ)
    (hC : IsOptimalQuadraticProxy ψ C) : optimalProxy ψ=C := by
  apply le_antisymm (optimalProxy_le ψ C hC.1)
  exact hC.2 _ (optimalProxy_isQuadraticProxy ψ h0 C hC.1)

def hypergeomOptimalProxy (N k m : ℕ) : ℝ := optimalProxy (hypergeomCenteredLogMGF N k m)

theorem hypergeomOptimalProxy_isOptimal (N k m : ℕ) (hk : k≤N) (hm : m≤N) :
    IsOptimalQuadraticProxy (hypergeomCenteredLogMGF N k m) (hypergeomOptimalProxy N k m) := by
  refine ⟨optimalProxy_isQuadraticProxy _ (hypergeomCenteredLogMGF_zero N k m hk hm)
    (sharpCurvatureConstant N k m) (hypergeom_uniform_log_laplace_domination N k m hk hm),?_⟩
  intro D hD
  exact optimalProxy_le _ D hD

theorem hypergeomOptimalProxy_ge_variance (N k m : ℕ) (hk : k≤N) (hm : m≤N) :
    hypergeomTiltVariance N k m 0≤hypergeomOptimalProxy N k m :=
  hypergeom_quadratic_proxy_ge_variance N k m hk hm _ (hypergeomOptimalProxy_isOptimal N k m hk hm).1

theorem hypergeomOptimalProxy_le_curvature (N k m : ℕ) (hk : k≤N) (hm : m≤N) :
    hypergeomOptimalProxy N k m≤sharpCurvatureConstant N k m :=
  optimalProxy_le _ _ (hypergeom_uniform_log_laplace_domination N k m hk hm)

theorem optimalProxy_reflection (ψ : ℝ→ℝ) :
    optimalProxy (fun t => ψ (-t))=optimalProxy ψ := by
  unfold optimalProxy
  congr 1
  ext v
  constructor
  · rintro ⟨t,ht,hv⟩
    refine ⟨-t,neg_ne_zero.mpr ht,?_⟩
    simpa only [neg_sq] using hv
  · rintro ⟨t,ht,hv⟩
    refine ⟨-t,neg_ne_zero.mpr ht,?_⟩
    simpa only [neg_neg,neg_sq] using hv

theorem hypergeomCenteredLogMGF_transpose (N k m : ℕ)
    (hk : k≤N) (hm : m≤N) (t : ℝ) :
    hypergeomCenteredLogMGF N k m t=hypergeomCenteredLogMGF N m k t := by
  unfold hypergeomCenteredLogMGF
  rw [hypergeomMGF_transpose N k m hk hm t]
  ring

theorem hypergeomCenteredLogMGF_success_complement (N k m : ℕ)
    (hk : k≤N) (hm : m≤N) (hN : 0<N) (t : ℝ) :
    hypergeomCenteredLogMGF N k m t=hypergeomCenteredLogMGF N (N-k) m (-t) := by
  unfold hypergeomCenteredLogMGF
  rw [hypergeomMGF_success_complement N k m hk hm t,
    Real.log_mul (Real.exp_ne_zero _)
      (ne_of_gt (hypergeomMGF_pos N (N-k) m (Nat.sub_le _ _) hm (-t))),
    Real.log_exp,Nat.cast_sub hk]
  have hN0 : (N:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  field_simp [hN0]
  ring

theorem hypergeomOptimalProxy_transpose (N k m : ℕ) (hk : k≤N) (hm : m≤N) :
    hypergeomOptimalProxy N k m=hypergeomOptimalProxy N m k := by
  unfold hypergeomOptimalProxy
  congr 1
  funext t
  exact hypergeomCenteredLogMGF_transpose N k m hk hm t

theorem hypergeomOptimalProxy_success_complement (N k m : ℕ)
    (hk : k≤N) (hm : m≤N) (hN : 0<N) :
    hypergeomOptimalProxy N k m=hypergeomOptimalProxy N (N-k) m := by
  unfold hypergeomOptimalProxy
  have hf : hypergeomCenteredLogMGF N k m=(fun t => hypergeomCenteredLogMGF N (N-k) m (-t)) :=
    funext (hypergeomCenteredLogMGF_success_complement N k m hk hm hN)
  rw [hf,optimalProxy_reflection]

theorem hypergeomOptimalProxy_sample_complement (N k m : ℕ)
    (hk : k≤N) (hm : m≤N) (hN : 0<N) :
    hypergeomOptimalProxy N k m=hypergeomOptimalProxy N k (N-m) := by
  rw [hypergeomOptimalProxy_transpose N k m hk hm,
    hypergeomOptimalProxy_success_complement N m k hm hk hN,
    hypergeomOptimalProxy_transpose N (N-m) k (Nat.sub_le _ _) hk]

theorem hypergeomOptimalProxy_two_draw (N k : ℕ) (hk : 2≤k) (hNk : k+2≤N) :
    hypergeomOptimalProxy N k 2=threeMassProxy (hypergeomMass N k 2 0) (hypergeomMass N k 2 2) := by
  apply optimalProxy_eq_of_optimal _ (hypergeomCenteredLogMGF_zero N k 2 (by omega) (by omega))
  have h := hypergeom_two_draw_optimal_proxy N k hk hNk
  convert h using 1
  funext t
  unfold hypergeomCenteredLogMGF
  norm_num

theorem hypergeomOptimalProxy_balanced_marks (q m : ℕ) (hq : 0<q) (hm : m≤2*q) :
    hypergeomOptimalProxy (2*q) q m=sharpCurvatureConstant (2*q) q m := by
  exact optimalProxy_eq_of_optimal _
    (hypergeomCenteredLogMGF_zero (2*q) q m (by omega) hm) _
    (hypergeom_balanced_marks_optimal_proxy q m hq hm)

end
end ExactHoeffding
