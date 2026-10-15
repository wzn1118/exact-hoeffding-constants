import ExactHoeffding.UniformLaplace
import ExactHoeffding.Chernoff
import ExactHoeffding.Sampling

namespace ExactHoeffding

theorem centeredHypergeomMGF_eq_exp_log (N k m : ℕ) (hk : k≤N) (hm : m≤N) (t : ℝ) :
    centeredHypergeomMGF N k m t=Real.exp (hypergeomCenteredLogMGF N k m t) := by
  rw [centeredHypergeomMGF_factor]
  unfold hypergeomCenteredLogMGF
  rw [sub_eq_add_neg,Real.exp_add,Real.exp_log (hypergeomMGF_pos N k m hk hm t)]
  have he : t*(-(k:ℝ)*(m:ℝ)/(N:ℝ))=-(((m:ℝ)*(k:ℝ)/(N:ℝ))*t) := by ring
  rw [he]
  exact mul_comm _ _

theorem hypergeom_centered_mgf_upper (N k m : ℕ) (hk : k≤N) (hm : m≤N) (t : ℝ) :
    centeredHypergeomMGF N k m t≤Real.exp (sharpCurvatureConstant N k m*t^2/2) := by
  rw [centeredHypergeomMGF_eq_exp_log N k m hk hm t]
  exact Real.exp_le_exp.mpr (hypergeom_uniform_log_laplace_domination N k m hk hm t)

/-- The optimized exponential upper-tail bound for the actual finite law. -/
theorem hypergeom_upper_tail_bound (N k m : ℕ) (hk : k≤N) (hm : m≤N)
    (hC : 0<sharpCurvatureConstant N k m) (s : ℝ) (hs : 0≤s) :
    (∑i∈Finset.range (m+1),
      if s≤(i:ℝ)-(k:ℝ)*(m:ℝ)/(N:ℝ) then hypergeomMass N k m i else 0)≤
      Real.exp (-s^2/(2*sharpCurvatureConstant N k m)) := by
  let C := sharpCurvatureConstant N k m
  let t := s/C
  have ht : 0≤t := div_nonneg hs hC.le
  have hmark := finite_markov_exp_bound (Finset.range (m+1)) (hypergeomMass N k m)
    (fun i => (i:ℝ)-(k:ℝ)*(m:ℝ)/(N:ℝ))
    (fun i => s≤(i:ℝ)-(k:ℝ)*(m:ℝ)/(N:ℝ))
    (fun i _ => hypergeomMass_nonneg N k m i) t s ht (fun i _ hi => hi)
  change _≤Real.exp (-t*s)*centeredHypergeomMGF N k m t at hmark
  have h := hmark.trans (mul_le_mul_of_nonneg_left
    (hypergeom_centered_mgf_upper N k m hk hm t) (Real.exp_pos _).le)
  rw [← Real.exp_add] at h
  convert h using 1
  congr 1
  dsimp [t,C]
  field_simp [ne_of_gt hC]
  ring

end ExactHoeffding
