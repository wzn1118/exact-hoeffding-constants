import ExactHoeffding.Basic

namespace ExactHoeffding

theorem cross_sum_identity {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x a b : ι → ℝ) :
    (∑ i∈s, ∑ j∈s, (x i-x j)*(a i*b j-a j*b i))=
      2*((∑ i∈s, x i*a i)*(∑ i∈s,b i)-
        (∑ i∈s, x i*b i)*(∑ i∈s,a i)) := by
  have expand (f g : ι → ℝ) :
      (∑i∈s,f i)*(∑j∈s,g j)=∑i∈s,∑j∈s,f i*g j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have hs : (∑i∈s,∑j∈s,(x i-x j)*(a i*b j-a j*b i))=
      (∑i∈s,∑j∈s,(x i*a i)*b j)-
      (∑i∈s,∑j∈s,(x i*b i)*a j)-
      (∑i∈s,∑j∈s,a i*(x j*b j))+
      (∑i∈s,∑j∈s,b i*(x j*a j)) := by
    simp only [← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs,← expand,← expand,← expand,← expand]
  ring

theorem cross_sum_order {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x a b : ι → ℝ)
    (h : ∀i∈s, ∀j∈s, (x i-x j)*(a i*b j-a j*b i)≤0) :
    (∑i∈s,x i*a i)*(∑i∈s,b i)≤
      (∑i∈s,x i*b i)*(∑i∈s,a i) := by
  have hn : (∑i∈s,∑j∈s,(x i-x j)*(a i*b j-a j*b i))≤0 :=
    Finset.sum_nonpos (fun i hi => Finset.sum_nonpos (fun j hj => h i hi j hj))
  rw [cross_sum_identity] at hn
  linarith

end ExactHoeffding
