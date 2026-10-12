import Std

/-!
# Scalar interpolation for metric type amalgamation

The manuscript extends a prescribed distance rule by clipping it to the
interval allowed over the larger base. This file proves the arithmetic core
for natural-number-valued bounds. It does not formalize metric full types,
the all-continuations property, or the metric amalgamation theorem itself.
-/
namespace AllThoseBigRamsey.MetricInterpolation

/-- Projection to the closed interval when `lower ≤ upper`. -/
def clip (lower upper original : Nat) : Nat :=
  max lower (min original upper)

theorem clip_bounds {lower upper original : Nat} (h : lower ≤ upper) :
    lower ≤ clip lower upper original ∧ clip lower upper original ≤ upper := by
  unfold clip
  omega

theorem clip_fixed {lower upper original : Nat}
    (hl : lower ≤ original) (hu : original ≤ upper) :
    clip lower upper original = original := by
  unfold clip
  omega

theorem clip_pos {lower upper original : Nat}
    (hu : 0 < upper) (hh : 0 < original) :
    0 < clip lower upper original := by
  unfold clip
  omega

/-- Maximum and minimum preserve the directional Lipschitz inequality. -/
theorem clip_lipschitz {l₁ u₁ h₁ l₂ u₂ h₂ d : Nat}
    (hl : l₁ ≤ l₂ + d) (hu : u₁ ≤ u₂ + d) (hh : h₁ ≤ h₂ + d) :
    clip l₁ u₁ h₁ ≤ clip l₂ u₂ h₂ + d := by
  unfold clip
  omega

/-- Three pair bounds suffice after both original values are clipped. -/
theorem clip_sum_lower {l₁ u₁ h₁ l₂ u₂ h₂ t : Nat}
    (hb₁ : l₁ ≤ u₁) (hb₂ : l₂ ≤ u₂)
    (hh : t ≤ h₁ + h₂)
    (hc₁ : t ≤ u₁ + l₂) (hc₂ : t ≤ l₁ + u₂) :
    t ≤ clip l₁ u₁ h₁ + clip l₂ u₂ h₂ := by
  unfold clip
  omega

/-- The scalar core of the type-distance extension, with all premises visible.
The geometric lemmas producing these premises remain manuscript obligations. -/
theorem interpolation {Q : Type} (lower upper original : Q → Nat)
    (delta bound : Q → Q → Nat)
    (interval : ∀ q, lower q ≤ upper q)
    (positiveUpper : ∀ q, 0 < upper q)
    (positiveOriginal : ∀ q, 0 < original q)
    (lipLower : ∀ q r, lower q ≤ lower r + delta q r)
    (lipUpper : ∀ q r, upper q ≤ upper r + delta q r)
    (lipOriginal : ∀ q r, original q ≤ original r + delta q r)
    (sumOriginal : ∀ q r, bound q r ≤ original q + original r)
    (crossLeft : ∀ q r, bound q r ≤ upper q + lower r)
    (crossRight : ∀ q r, bound q r ≤ lower q + upper r) :
    let result := fun q => clip (lower q) (upper q) (original q)
    (∀ q, lower q ≤ result q ∧ result q ≤ upper q) ∧
    (∀ q, 0 < result q) ∧
    (∀ q, lower q ≤ original q → original q ≤ upper q →
      result q = original q) ∧
    (∀ q r, result q ≤ result r + delta q r) ∧
    (∀ q r, bound q r ≤ result q + result r) := by
  dsimp
  exact ⟨fun q => clip_bounds (interval q),
    fun q => clip_pos (positiveUpper q) (positiveOriginal q),
    fun _ hl hu => clip_fixed hl hu,
    fun q r => clip_lipschitz (lipLower q r) (lipUpper q r) (lipOriginal q r),
    fun q r => clip_sum_lower (interval q) (interval r) (sumOriginal q r)
      (crossLeft q r) (crossRight q r)⟩

end AllThoseBigRamsey.MetricInterpolation
