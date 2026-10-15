import ExactHoeffding.LimitProxyStrict
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact

/-! # Joint analyticity along the limiting axis and compact convergence

This is convergence of the genuine inverse-population family. In particular,
the compact convergence includes the removable tilt zero, rather than only
compact sets disjoint from zero.
-/

namespace ExactHoeffding

noncomputable section

open Set Filter
open scoped Topology

theorem rescaledProxyExtension_joint_analytic_axis (m : ℕ) (s t : ℝ) :
    AnalyticAt ℝ (fun u : ℝ × ℝ => rescaledProxyExtension m s u.1 u.2) (0, t) := by
  by_cases hm0 : m = 0
  · subst m
    simpa [rescaledProxyExtension, rescaledMGFSlope, rescaledMGFQuadratic,
      rescaledMean] using
      (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ × ℝ => (0 : ℝ)) (0, t))
  have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  by_cases ht : t = 0
  · subst t
    exact rescaledProxyExtension_joint_analytic m s
  have hpos : 0 < rescaledMGF m s 0 t := by
    rw [rescaledMGF_at_zero]
    positivity
  have hmean : AnalyticAt ℝ (fun u : ℝ × ℝ => rescaledMean m s u.1) (0, t) := by
    unfold rescaledMean
    exact (analyticAt_const.mul
      (analyticAt_const.sub (analyticAt_const.mul analyticAt_fst))).div_const
  have hlog : AnalyticAt ℝ
      (fun u : ℝ × ℝ => Real.log (rescaledMGF m s u.1 u.2)) (0, t) := by
    exact (analyticAt_log hpos).comp_of_eq (rescaledMGF_joint_analytic m s t) rfl
  have hquot : AnalyticAt ℝ
      (fun u : ℝ × ℝ =>
        2 * (Real.log (rescaledMGF m s u.1 u.2) - rescaledMean m s u.1 * u.2) /
          u.2 ^ 2) (0, t) := by
    apply AnalyticAt.div
    · exact analyticAt_const.mul (hlog.sub (hmean.mul analyticAt_snd))
    · exact analyticAt_snd.pow 2
    · exact pow_ne_zero 2 ht
  apply hquot.congr
  filter_upwards [(continuousAt_snd :
    ContinuousAt (fun u : ℝ × ℝ => u.2) (0, t)).eventually_ne ht] with u hu
  exact (rescaledProxyExtension_eq_quotient m hm s u.1 u.2 hu).symm

theorem rescaledProxyExtension_joint_continuous_axis (m : ℕ) (s t : ℝ) :
    ContinuousAt (fun u : ℝ × ℝ => rescaledProxyExtension m s u.1 u.2) (0, t) :=
  (rescaledProxyExtension_joint_analytic_axis m s t).continuousAt

/-- Compactness upgrades joint continuity along a fiber to uniform convergence. -/
theorem compact_uniform_convergence_of_joint_continuous
    (F : ℝ → ℝ → ℝ) (K : Set ℝ) (hK : IsCompact K)
    (hF : ∀ t ∈ K, ContinuousAt (fun u : ℝ × ℝ => F u.1 u.2) (0, t)) :
    TendstoUniformlyOn F (F 0) (𝓝 0) K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  apply hK.eventually_forall_of_forall_eventually
  intro t ht
  have hlimit : ContinuousAt (fun u : ℝ × ℝ => F 0 u.2) (0, t) := by
    have hslice : ContinuousAt (F 0) t :=
      (hF t ht).comp (continuousAt_const.prodMk continuousAt_id)
    exact hslice.comp continuousAt_snd
  have hdist := hlimit.dist (hF t ht)
  exact hdist.eventually_lt continuousAt_const (by simpa using hε)

theorem rescaledProxyExtension_uniform_on_compact (m : ℕ) (s : ℝ)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (rescaledProxyExtension m s)
      (rescaledProxyExtension m s 0) (𝓝 0) K := by
  exact compact_uniform_convergence_of_joint_continuous _ K hK
    (fun t _ => rescaledProxyExtension_joint_continuous_axis m s t)

theorem rescaledProxyExtension_limit_strict (m : ℕ) (hm : 0 < m)
    (s t : ℝ) (ht : t ≠ 0) :
    rescaledProxyExtension m s 0 t < rescaledProxyExtension m s 0 0 := by
  rw [rescaledProxyExtension_limit_formula m s t ht,
    rescaledProxyExtension_at_zero]
  exact limiting_proxy_strict m hm t ht

end

end ExactHoeffding
