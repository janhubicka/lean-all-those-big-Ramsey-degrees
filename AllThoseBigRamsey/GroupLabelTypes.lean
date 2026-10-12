import Std

/-!
# One-types of group-labelled structures

A profile q records the labels from base vertices to a new vertex. Its
compatibility equation is the group label law. These lemmas use only left
cancellation, and prove determination by one anchor, restriction, and coverage
of valid profiles by a type map that is a section of restriction.

They do not formalize the manuscript's all-continuations lifting lemma or the
cycle-completion theorem. No hypothesis of type-respecting amalgamation is used.
-/
namespace AllThoseBigRamsey.GroupLabelTypes

variable {A B X Γ : Type}

def Compatible (mul : Γ → Γ → Γ) (label : B → B → Γ) (q : B → Γ) : Prop :=
  ∀ a b, mul (label a b) (q b) = q a

theorem eq_of_anchor (mul : Γ → Γ → Γ)
    (cancel : ∀ g x y, mul g x = mul g y → x = y)
    {label : B → B → Γ} {p q : B → Γ} (a : B)
    (hp : Compatible mul label p) (hq : Compatible mul label q)
    (ha : p a = q a) : p = q := by
  funext b
  apply cancel (label a b) (p b) (q b)
  exact (hp a b).trans (ha.trans (hq a b).symm)

theorem restrict_compatible (mul : Γ → Γ → Γ)
    {labelA : A → A → Γ} {labelB : B → B → Γ}
    (e : A → B) (he : ∀ a b, labelB (e a) (e b) = labelA a b)
    {q : B → Γ} (hq : Compatible mul labelB q) :
    Compatible mul labelA (fun a => q (e a)) := by
  intro a b
  rw [← he a b]
  exact hq (e a) (e b)

/-- An anchor in the smaller base makes restriction injective on valid profiles. -/
theorem restriction_injective (mul : Γ → Γ → Γ)
    (cancel : ∀ g x y, mul g x = mul g y → x = y)
    {labelB : B → B → Γ} (e : A → B) (a : A)
    {p q : B → Γ} (hp : Compatible mul labelB p)
    (hq : Compatible mul labelB q) (h : ∀ a, p (e a) = q (e a)) : p = q :=
  eq_of_anchor mul cancel (e a) hp hq (h a)

/-- Concrete coverage statement used in the group-labelled TRAP proof.
The map F is required to preserve compatible profiles and to restrict back to
its input. Coverage is a conclusion, not an assumption. -/
theorem typeMap_covers (mul : Γ → Γ → Γ)
    (cancel : ∀ g x y, mul g x = mul g y → x = y)
    {labelA : A → A → Γ} {labelB : B → B → Γ}
    (e : A → B) (he : ∀ a b, labelB (e a) (e b) = labelA a b)
    (a : A) (F : (A → Γ) → (B → Γ))
    (valid : ∀ p, Compatible mul labelA p → Compatible mul labelB (F p))
    (sectionLaw : ∀ p a, F p (e a) = p a)
    (q : B → Γ) (hq : Compatible mul labelB q) :
    F (fun a => q (e a)) = q := by
  have hp := restrict_compatible mul e he hq
  exact eq_of_anchor mul cancel (e a) (valid _ hp) hq (sectionLaw _ a)

/-- Equal labels from an anchor force the identity label on a future pair. -/
theorem same_profile_pair (mul : Γ → Γ → Γ) (one : Γ)
    (cancel : ∀ g x y, mul g x = mul g y → x = y)
    (rightIdentity : ∀ g, mul g one = g)
    (label : X → X → Γ)
    (cocycle : ∀ x y z, mul (label x y) (label y z) = label x z)
    (b x y : X) (h : label b x = label b y) : label x y = one := by
  apply cancel (label b x) (label x y) one
  exact (cocycle b x y).trans (h.symm.trans (rightIdentity _).symm)

end AllThoseBigRamsey.GroupLabelTypes
