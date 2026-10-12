import Std

/-!
# Lattice-valued interpolation

The scalar part of metric type amalgamation, with no comparison of arbitrary
values. `LatticeAdd` records standard lattice and commutative-monoid laws;
translations preserve both lattice operations. Finiteness and the geometric
meaning of the endpoints are not needed for these scalar proofs. In particular,
this file does not assert the full type-amalgamation theorem.
-/
namespace AllThoseBigRamsey

universe u

/-- The algebraic laws used by the lattice-valued distance argument. -/
structure LatticeAdd (R : Type u) where
  le : R → R → Prop
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  antisymm : ∀ {a b}, le a b → le b a → a = b
  meet : R → R → R
  join : R → R → R
  meet_le_left : ∀ a b, le (meet a b) a
  meet_le_right : ∀ a b, le (meet a b) b
  le_meet : ∀ {a b c}, le a b → le a c → le a (meet b c)
  le_join_left : ∀ a b, le a (join a b)
  le_join_right : ∀ a b, le b (join a b)
  join_le : ∀ {a b c}, le a c → le b c → le (join a b) c
  zero : R
  zero_le : ∀ a, le zero a
  add : R → R → R
  add_zero : ∀ a, add a zero = a
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_mono : ∀ {a b c d}, le a b → le c d → le (add a c) (add b d)
  add_meet : ∀ a b c, add (meet a b) c = meet (add a c) (add b c)
  add_join : ∀ a b c, add (join a b) c = join (add a c) (add b c)

namespace LatticeAdd
variable {R : Type u} (O : LatticeAdd R)

theorem meet_mono {a b c d : R} (hab : O.le a b) (hcd : O.le c d) :
    O.le (O.meet a c) (O.meet b d) :=
  O.le_meet (O.trans (O.meet_le_left a c) hab)
    (O.trans (O.meet_le_right a c) hcd)

theorem join_mono {a b c d : R} (hab : O.le a b) (hcd : O.le c d) :
    O.le (O.join a c) (O.join b d) :=
  O.join_le (O.trans hab (O.le_join_left b d))
    (O.trans hcd (O.le_join_right b d))

theorem meet_of_le {a b : R} (h : O.le a b) : O.meet a b = a :=
  O.antisymm (O.meet_le_left a b) (O.le_meet (O.refl a) h)

theorem join_of_le {a b : R} (h : O.le a b) : O.join a b = b :=
  O.antisymm (O.join_le h (O.refl b)) (O.le_join_right a b)

theorem add_meet_right (a b c : R) :
    O.add a (O.meet b c) = O.meet (O.add a b) (O.add a c) := by
  rw [O.add_comm a (O.meet b c), O.add_meet,
    O.add_comm b a, O.add_comm c a]

/-- Truncate the join with the lower endpoint at the upper endpoint. -/
def clip (lower upper original : R) : R :=
  O.meet (O.join lower original) upper

theorem clip_bounds {lower upper original : R} (h : O.le lower upper) :
    O.le lower (O.clip lower upper original) ∧
    O.le (O.clip lower upper original) upper :=
  ⟨O.le_meet (O.le_join_left lower original) h,
    O.meet_le_right (O.join lower original) upper⟩

theorem clip_fixed {lower upper original : R}
    (hl : O.le lower original) (hu : O.le original upper) :
    O.clip lower upper original = original := by
  unfold clip
  rw [O.join_of_le hl, O.meet_of_le hu]

/-- Meet-irreducibility of zero is an explicit, separate premise. -/
theorem clip_nonzero
    (meet_nonzero : ∀ {a b : R}, a ≠ O.zero → b ≠ O.zero →
      O.meet a b ≠ O.zero)
    {lower upper original : R} (hu : upper ≠ O.zero) (hh : original ≠ O.zero) :
    O.clip lower upper original ≠ O.zero := by
  have hj : O.join lower original ≠ O.zero := by
    intro hz
    have hle : O.le original O.zero := by
      rw [← hz]
      exact O.le_join_right lower original
    exact hh (O.antisymm hle (O.zero_le original))
  exact meet_nonzero hj hu

/-- No linear-order or trichotomy premise is used. -/
theorem clip_nonexpansive {l₁ u₁ h₁ l₂ u₂ h₂ d : R}
    (hl : O.le l₁ (O.add l₂ d))
    (hu : O.le u₁ (O.add u₂ d))
    (hh : O.le h₁ (O.add h₂ d)) :
    O.le (O.clip l₁ u₁ h₁) (O.add (O.clip l₂ u₂ h₂) d) := by
  unfold clip
  rw [O.add_meet, O.add_join]
  exact O.meet_mono (O.join_mono hl hh) hu

/-- Four lower bounds after distributing addition over the two meets. -/
theorem clip_pair_bound {l₁ u₁ h₁ l₂ u₂ h₂ t : R}
    (interval : O.le l₁ u₁ ∧ O.le l₂ u₂)
    (hh : O.le t (O.add h₁ h₂))
    (hc₁ : O.le t (O.add u₁ l₂))
    (hc₂ : O.le t (O.add l₁ u₂)) :
    O.le t (O.add (O.clip l₁ u₁ h₁) (O.clip l₂ u₂ h₂)) := by
  unfold clip
  rw [O.add_meet, O.add_meet_right, O.add_meet_right]
  apply O.le_meet
  · apply O.le_meet
    · exact O.trans hh (O.add_mono (O.le_join_right l₁ h₁)
        (O.le_join_right l₂ h₂))
    · exact O.trans hc₂ (O.add_mono (O.le_join_left l₁ h₁) (O.refl u₂))
  · apply O.le_meet
    · exact O.trans hc₁ (O.add_mono (O.refl u₁) (O.le_join_left l₂ h₂))
    · exact O.trans hc₁ (O.add_mono (O.refl u₁) interval.2)

/-- All scalar conclusions needed to extend a prescribed metric distance rule.
The endpoint geometry and interpretation as a full-type map are separate. -/
theorem interpolation {Q : Type} (lower upper original : Q → R)
    (delta bound : Q → Q → R)
    (meet_nonzero : ∀ {a b : R}, a ≠ O.zero → b ≠ O.zero →
      O.meet a b ≠ O.zero)
    (interval : ∀ q, O.le (lower q) (upper q))
    (positiveUpper : ∀ q, upper q ≠ O.zero)
    (positiveOriginal : ∀ q, original q ≠ O.zero)
    (lipLower : ∀ q r, O.le (lower q) (O.add (lower r) (delta q r)))
    (lipUpper : ∀ q r, O.le (upper q) (O.add (upper r) (delta q r)))
    (lipOriginal : ∀ q r, O.le (original q) (O.add (original r) (delta q r)))
    (sumOriginal : ∀ q r, O.le (bound q r) (O.add (original q) (original r)))
    (crossLeft : ∀ q r, O.le (bound q r) (O.add (upper q) (lower r)))
    (crossRight : ∀ q r, O.le (bound q r) (O.add (lower q) (upper r))) :
    let result := fun q => O.clip (lower q) (upper q) (original q)
    (∀ q, O.le (lower q) (result q) ∧ O.le (result q) (upper q)) ∧
    (∀ q, result q ≠ O.zero) ∧
    (∀ q, O.le (lower q) (original q) → O.le (original q) (upper q) →
      result q = original q) ∧
    (∀ q r, O.le (result q) (O.add (result r) (delta q r))) ∧
    (∀ q r, O.le (bound q r) (O.add (result q) (result r))) := by
  dsimp
  exact ⟨fun q => O.clip_bounds (interval q),
    fun q => O.clip_nonzero meet_nonzero (positiveUpper q) (positiveOriginal q),
    fun _ hl hu => O.clip_fixed hl hu,
    fun q r => O.clip_nonexpansive (lipLower q r) (lipUpper q r) (lipOriginal q r),
    fun q r => O.clip_pair_bound ⟨interval q, interval r⟩ (sumOriginal q r)
      (crossLeft q r) (crossRight q r)⟩

end LatticeAdd
end AllThoseBigRamsey
