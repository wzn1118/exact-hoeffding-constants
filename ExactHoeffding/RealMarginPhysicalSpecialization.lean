import ExactHoeffding.RealMarginExactImbalance
import ExactHoeffding.BernoulliOptimal
import ExactHoeffding.RescaledActualProxy

/-! # Physical hypergeometric specialization and the explicit Bernoulli envelope -/
namespace ExactHoeffding
noncomputable section
open Filter Finset
open scoped Topology

/-- One actual real-margin draw is exactly the centered Bernoulli law. -/
theorem realMarginCenteredLogMGF_singleton (N:ℕ) (d:ℝ) :
    realMarginCenteredLogMGF N 1 d = bernoulliCenteredLogMGF ((1-d)/2) := by
  funext t
  unfold realMarginCenteredLogMGF
  norm_num only [Nat.cast_one,one_mul]
  exact realMarginCenteredLogMGF_one (1/(N:ℝ)) ((1-d)/2) t

/-- The least one-draw proxy has the closed Bernoulli formula on the entire
closed real success-proportion interval. -/
theorem realMargin_singleton_optimalProxy (N:ℕ) (d:ℝ) (hd0:-1≤d) (hd1:d≤1) :
    optimalProxy (realMarginCenteredLogMGF N 1 d)=bernoulliSharpBeta ((1-d)/2) := by
  rw [realMarginCenteredLogMGF_singleton]
  exact optimalProxy_eq_of_optimal _ (by simp [bernoulliCenteredLogMGF,bernoulliMGF]) _
    (bernoulli_sharp_quadratic_optimal _ (by linarith) (by linarith))

/-- Exact finite-N local separation is strict domination by the explicit
sharp Bernoulli coefficient, including the real-parameter extension. -/
theorem realMargin_optimal_proxy_eventually_lt_bernoulli (N m:ℕ) (hN:5≤N)
    (hm:2≤m) (hNm:2*m≤N) :
    ∀ᶠ d in 𝓝 (0:ℝ),d≠0 →
      4*(N:ℝ)*optimalProxy (realMarginCenteredLogMGF N m d)/((m:ℝ)*((N:ℝ)-m)) <
        4*(N:ℝ)*bernoulliSharpBeta ((1-d)/2)/((N:ℝ)-1) := by
  filter_upwards [realMargin_optimal_proxy_eventually_lt_singleton N m hN hm hNm,
    isOpen_Ioo.mem_nhds (show (0:ℝ)∈Set.Ioo (-1:ℝ) 1 by constructor <;> norm_num)]
    with d hgap hd
  simpa only [realMargin_singleton_optimalProxy N d hd.1.le hd.2.le] using hgap

/-- The actual centered Laplace transform agrees at every physical margin. -/
theorem realMarginCenteredLogMGF_physical (N k m:ℕ) (hN:0<N)
    (hk:k≤N) (hm:m≤N) (d:ℝ) (hd:(1-d)/2=(k:ℝ)/N) :
    realMarginCenteredLogMGF N m d=hypergeomCenteredLogMGF N k m := by
  funext t
  unfold realMarginCenteredLogMGF hypergeomCenteredLogMGF hypergeomMGF
  rw [hd]
  have hmgf : finiteMGF (range (m+1))
      (realMarginMass m (1/(N:ℝ)) ((k:ℝ)/N)) (fun i=>(i:ℝ)) t=
      finiteMGF (range (m+1)) (hypergeomMass N k m) (fun i=>(i:ℝ)) t := by
    unfold finiteMGF
    apply Finset.sum_congr rfl
    intro i hi
    rw [realMarginMass_hypergeom N k m i hN hk hm
      (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  rw [hmgf]
  ring

/-- The removable objective, including its zero-tilt variance branch,
is exactly the physical hypergeometric objective. -/
theorem realMarginProxy_physical (N k m:ℕ) (hN:0<N) (hk:k≤N) (hm:m≤N)
    (d t:ℝ) (hd:(1-d)/2=(k:ℝ)/N) :
    realMarginProxy N m d t=actualHypergeomProxy N k m t := by
  have hden := (realMarginPopulationDenom_pos N m hN hm).ne'
  by_cases ht:t=0
  · subst t
    rw [realMarginProxy_zero N m d hden]
    simp only [actualHypergeomProxy]
    rw [←realMarginMass_cumulant2 N m d hden]
    have hraw (r:ℕ) : finiteRawMoment (range (m+1)) (fun i=>(i:ℝ))
        (realMarginMass m (1/(N:ℝ)) ((1-d)/2)) r=hypergeomRawMoment N k m r := by
      unfold finiteRawMoment hypergeomRawMoment
      rw [hd]
      apply Finset.sum_congr rfl
      intro i hi
      rw [realMarginMass_hypergeom N k m i hN hk hm
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    change finiteRawMoment _ _ _ 2-(finiteRawMoment _ _ _ 1)^2=
      hypergeomRawMoment N k m 2-(hypergeomRawMoment N k m 1)^2
    rw [hraw 2,hraw 1]
  · rw [realMarginProxy_eq_quotient N m d t hden ht,
      actualHypergeomProxy,if_neg ht,hypergeom_centered_log_identity N k m hk hm t]
    rw [congrFun (realMarginCenteredLogMGF_physical N k m hN hk hm d hd) t]
    rfl

end
end ExactHoeffding
