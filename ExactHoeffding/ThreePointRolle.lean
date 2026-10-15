import ExactHoeffding.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Rolle's theorem for three double zeros

The finite chain is written explicitly. No generalized Rolle or Hermite
remainder conclusion is introduced as an assumption.
-/

namespace ExactHoeffding

private theorem rolle_between {f g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : ∀ x, HasDerivAt f (g x) x) (ha : f a = 0) (hb : f b = 0) :
    ∃ c, a < c ∧ c < b ∧ g c = 0 := by
  obtain ⟨c, hc, hz⟩ := exists_hasDerivAt_eq_zero hab
    (fun x _ => (hd x).continuousAt.continuousWithinAt) (ha.trans hb.symm)
    (fun x _ => hd x)
  exact ⟨c, hc.1, hc.2, hz⟩

/-- Three ordered zeros at which the derivative also vanishes force a zero
of the fifth derivative between the outside nodes. -/
theorem three_double_zeros_fifth_zero (f₀ f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ)
    (hd₀ : ∀ x, HasDerivAt f₀ (f₁ x) x)
    (hd₁ : ∀ x, HasDerivAt f₁ (f₂ x) x)
    (hd₂ : ∀ x, HasDerivAt f₂ (f₃ x) x)
    (hd₃ : ∀ x, HasDerivAt f₃ (f₄ x) x)
    (hd₄ : ∀ x, HasDerivAt f₄ (f₅ x) x)
    (x y z : ℝ) (hxy : x < y) (hyz : y < z)
    (h₀x : f₀ x = 0) (h₀y : f₀ y = 0) (h₀z : f₀ z = 0)
    (h₁x : f₁ x = 0) (h₁y : f₁ y = 0) (h₁z : f₁ z = 0) :
    ∃ c, x < c ∧ c < z ∧ f₅ c = 0 := by
  obtain ⟨a, hxa, hay, h₁a⟩ := rolle_between hxy hd₀ h₀x h₀y
  obtain ⟨b, hyb, hbz, h₁b⟩ := rolle_between hyz hd₀ h₀y h₀z
  obtain ⟨c₁, hxc₁, hc₁a, h₂c₁⟩ := rolle_between hxa hd₁ h₁x h₁a
  obtain ⟨c₂, hac₂, hc₂y, h₂c₂⟩ := rolle_between hay hd₁ h₁a h₁y
  obtain ⟨c₃, hyc₃, hc₃b, h₂c₃⟩ := rolle_between hyb hd₁ h₁y h₁b
  obtain ⟨c₄, hbc₄, hc₄z, h₂c₄⟩ := rolle_between hbz hd₁ h₁b h₁z
  obtain ⟨d₁, hc₁d₁, hd₁c₂, h₃d₁⟩ := rolle_between (hc₁a.trans hac₂) hd₂ h₂c₁ h₂c₂
  obtain ⟨d₂, hc₂d₂, hd₂c₃, h₃d₂⟩ := rolle_between (hc₂y.trans hyc₃) hd₂ h₂c₂ h₂c₃
  obtain ⟨d₃, hc₃d₃, hd₃c₄, h₃d₃⟩ := rolle_between (hc₃b.trans hbc₄) hd₂ h₂c₃ h₂c₄
  obtain ⟨e₁, hd₁e₁, he₁d₂, h₄e₁⟩ := rolle_between (hd₁c₂.trans hc₂d₂) hd₃ h₃d₁ h₃d₂
  obtain ⟨e₂, hd₂e₂, he₂d₃, h₄e₂⟩ := rolle_between (hd₂c₃.trans hc₃d₃) hd₃ h₃d₂ h₃d₃
  obtain ⟨c, he₁c, hce₂, h₅c⟩ := rolle_between (he₁d₂.trans hd₂e₂) hd₄ h₄e₁ h₄e₂
  exact ⟨c, hxc₁.trans (hc₁d₁.trans (hd₁e₁.trans he₁c)),
    hce₂.trans (he₂d₃.trans (hd₃c₄.trans hc₄z)), h₅c⟩

end ExactHoeffding
