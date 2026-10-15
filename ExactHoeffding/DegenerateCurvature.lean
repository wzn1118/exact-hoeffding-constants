import ExactHoeffding.Support
import ExactHoeffding.TiltedVariance

namespace ExactHoeffding

theorem finiteLogMGF_curvature_point_mass {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀∈s) (w x : ι→ℝ)
    (hw : ∀i∈s, w i=if i=i₀ then 1 else 0) (t : ℝ) :
    deriv (deriv (fun u => Real.log (finiteMGF s w x u))) t=0 := by
  have hfun : (fun u => Real.log (finiteMGF s w x u))=(fun u => u*x i₀) := by
    funext u
    unfold finiteMGF
    have hsum : (∑i∈s,w i*Real.exp (u*x i))=Real.exp (u*x i₀) := by
      calc
        _ = ∑i∈s, if i=i₀ then Real.exp (u*x i₀) else 0 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hw i hi]
          by_cases h : i=i₀ <;> simp [h]
        _ = _ := by simp [hi₀]
    rw [hsum,Real.log_exp]
  rw [hfun]
  have hd : deriv (fun u : ℝ => u*x i₀)=(fun _ => x i₀) := by
    funext u
    exact (hasDerivAt_mul_const (x i₀)).deriv
  rw [hd]
  exact deriv_const t _

theorem hypergeom_curvature_zero_marks (N m : ℕ) (hm : m≤N) (t : ℝ) :
    deriv (deriv (fun u => Real.log (hypergeomMGF N 0 m u))) t=0 := by
  exact finiteLogMGF_curvature_point_mass (Finset.range (m+1)) 0
    (Finset.mem_range.mpr (by omega)) (hypergeomMass N 0 m) (fun i => (i:ℝ))
    (fun i hi => hypergeomMass_zero_marks N m i hm
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) t

theorem hypergeom_curvature_zero_draws (N k : ℕ) (t : ℝ) :
    deriv (deriv (fun u => Real.log (hypergeomMGF N k 0 u))) t=0 := by
  apply finiteLogMGF_curvature_point_mass (Finset.range 1) 0
    (Finset.mem_range.mpr (by omega)) (hypergeomMass N k 0) (fun i => (i:ℝ)) _ t
  intro i hi
  have hi0 : i=0 := by have := Finset.mem_range.mp hi; omega
  subst i
  simp [hypergeomMass_zero_draws]

theorem hypergeom_curvature_full_marks (N m : ℕ) (hm : m≤N) (t : ℝ) :
    deriv (deriv (fun u => Real.log (hypergeomMGF N N m u))) t=0 := by
  exact finiteLogMGF_curvature_point_mass (Finset.range (m+1)) m
    (Finset.mem_range.mpr (by omega)) (hypergeomMass N N m) (fun i => (i:ℝ))
    (fun i hi => hypergeomMass_full_marks N m i hm
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) t

theorem hypergeom_curvature_full_draws (N k : ℕ) (hk : k≤N) (t : ℝ) :
    deriv (deriv (fun u => Real.log (hypergeomMGF N k N u))) t=0 := by
  exact finiteLogMGF_curvature_point_mass (Finset.range (N+1)) k
    (Finset.mem_range.mpr (by omega)) (hypergeomMass N k N) (fun i => (i:ℝ))
    (fun i hi => hypergeomMass_full_draws N k i hk
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) t

end ExactHoeffding
