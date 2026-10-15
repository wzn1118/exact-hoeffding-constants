import ExactHoeffding.TiltedVariance
import Mathlib.Topology.Algebra.Order.Field

open Filter
open scoped Topology

namespace ExactHoeffding
noncomputable section

/-- Shifting every exponent by a common endpoint preserves normalized
tilted expectations. -/
theorem tilted_ratio_shift {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x g : ι → ℝ) (t c : ℝ) :
    (∑ i ∈ s, w i*g i*Real.exp (t*x i))/(∑ i ∈ s, w i*Real.exp (t*x i))=
    (∑ i ∈ s, w i*g i*Real.exp (t*(x i-c)))/
      (∑ i ∈ s, w i*Real.exp (t*(x i-c))) := by
  have hshift (a : ι → ℝ) :
      (∑ i ∈ s, a i*Real.exp (t*x i))=
        Real.exp (t*c)*(∑ i ∈ s, a i*Real.exp (t*(x i-c))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have he : t*x i=t*c+t*(x i-c) := by ring
    rw [he,Real.exp_add]
    ring
  rw [hshift (fun i => w i*g i),hshift w]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

theorem finite_exp_sum_tendsto_atTop {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a x : ι → ℝ) (i₀ : ι) (hi₀ : i₀∈s)
    (hmax : ∀ i∈s, i≠i₀ → x i<x i₀) :
    Tendsto (fun t : ℝ => ∑ i∈s, a i*Real.exp (t*(x i-x i₀)))
      atTop (𝓝 (a i₀)) := by
  have hs : (∑ i∈s, if i=i₀ then a i₀ else 0)=a i₀ := by simp [hi₀]
  rw [← hs]
  apply tendsto_finsetSum
  intro i hi
  by_cases he : i=i₀
  · subst i
    simp only [sub_self,mul_zero,Real.exp_zero,mul_one,ite_true]
    exact tendsto_const_nhds
  · rw [if_neg he]
    have hx : x i-x i₀<0 := sub_neg.mpr (hmax i hi he)
    have ht := Real.tendsto_exp_atBot.comp
      (tendsto_id.atTop_mul_const_of_neg hx)
    simpa only [mul_zero,Function.comp_apply,id_eq] using ht.const_mul (a i)

theorem finite_exp_sum_tendsto_atBot {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a x : ι → ℝ) (i₀ : ι) (hi₀ : i₀∈s)
    (hmin : ∀ i∈s, i≠i₀ → x i₀<x i) :
    Tendsto (fun t : ℝ => ∑ i∈s, a i*Real.exp (t*(x i-x i₀)))
      atBot (𝓝 (a i₀)) := by
  have hs : (∑ i∈s, if i=i₀ then a i₀ else 0)=a i₀ := by simp [hi₀]
  rw [← hs]
  apply tendsto_finsetSum
  intro i hi
  by_cases he : i=i₀
  · subst i
    simp only [sub_self,mul_zero,Real.exp_zero,mul_one,ite_true]
    exact tendsto_const_nhds
  · rw [if_neg he]
    have hx : 0<x i-x i₀ := sub_pos.mpr (hmin i hi he)
    have ht := Real.tendsto_exp_atBot.comp (tendsto_id.atBot_mul_const hx)
    simpa only [mul_zero,Function.comp_apply,id_eq] using ht.const_mul (a i)

theorem finite_tilted_expectation_tendsto_atTop {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x g : ι → ℝ) (i₀ : ι) (hi₀ : i₀∈s)
    (hw : w i₀≠0) (hmax : ∀ i∈s, i≠i₀ → x i<x i₀) :
    Tendsto (fun t : ℝ =>
      (∑ i∈s, w i*g i*Real.exp (t*x i))/(∑ i∈s, w i*Real.exp (t*x i)))
      atTop (𝓝 (g i₀)) := by
  have hnum := finite_exp_sum_tendsto_atTop s (fun i => w i*g i) x i₀ hi₀ hmax
  have hden := finite_exp_sum_tendsto_atTop s w x i₀ hi₀ hmax
  have hratio := hnum.div hden hw
  have hf : (fun t : ℝ =>
      (∑ i∈s, w i*g i*Real.exp (t*x i))/(∑ i∈s, w i*Real.exp (t*x i)))=
      (fun t : ℝ => (∑ i∈s, w i*g i*Real.exp (t*(x i-x i₀)))/
        (∑ i∈s, w i*Real.exp (t*(x i-x i₀)))) := by
    funext t
    exact tilted_ratio_shift s w x g t (x i₀)
  rw [hf]
  convert hratio using 1
  · ext t
    rfl
  · congr 1
    exact (mul_div_cancel_left₀ _ hw).symm

theorem finite_tilted_expectation_tendsto_atBot {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x g : ι → ℝ) (i₀ : ι) (hi₀ : i₀∈s)
    (hw : w i₀≠0) (hmin : ∀ i∈s, i≠i₀ → x i₀<x i) :
    Tendsto (fun t : ℝ =>
      (∑ i∈s, w i*g i*Real.exp (t*x i))/(∑ i∈s, w i*Real.exp (t*x i)))
      atBot (𝓝 (g i₀)) := by
  have hnum := finite_exp_sum_tendsto_atBot s (fun i => w i*g i) x i₀ hi₀ hmin
  have hden := finite_exp_sum_tendsto_atBot s w x i₀ hi₀ hmin
  have hratio := hnum.div hden hw
  have hf : (fun t : ℝ =>
      (∑ i∈s, w i*g i*Real.exp (t*x i))/(∑ i∈s, w i*Real.exp (t*x i)))=
      (fun t : ℝ => (∑ i∈s, w i*g i*Real.exp (t*(x i-x i₀)))/
        (∑ i∈s, w i*Real.exp (t*(x i-x i₀)))) := by
    funext t
    exact tilted_ratio_shift s w x g t (x i₀)
  rw [hf]
  convert hratio using 1
  · ext t
    rfl
  · congr 1
    exact (mul_div_cancel_left₀ _ hw).symm

end
end ExactHoeffding
