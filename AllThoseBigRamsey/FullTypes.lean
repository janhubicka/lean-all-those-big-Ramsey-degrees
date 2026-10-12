import AllThoseBigRamsey.Relational

/-! Full quantifier-free types: the entire induced diagram, not a mixed fragment. -/
namespace AllThoseBigRamsey

/-- A full `k`-type over `A`, with distinct new vertices in their specified order. -/
structure FullType {L : Language} {α : Type} (A : RelStructure L α) (k : Nat) where
  diagram : RelStructure L (Sum α (Fin k))
  over_base : ∀ R q, diagram.rel R (fun i => Sum.inl (q i)) ↔ A.rel R q

/-- Pull back a structure along a map. Injectivity is required when this is used as an induced copy. -/
def RelStructure.pullback {L : Language} {α β : Type}
    (A : RelStructure L α) (f : β → α) : RelStructure L β where
  rel := fun R q => A.rel R (fun i => f (q i))

/-- Evaluate a term naming either an old parameter or one new vertex. -/
def evaluate {α β : Type} {k : Nat} (base : β → α) (s : Fin k → α) : Sum β (Fin k) → α
  | .inl x => base x
  | .inr i => s i

/-- The concrete full type of a tuple over a named parameter set. -/
def typeOf {L : Language} {α β : Type} (A : RelStructure L α)
    (base : β → α) {k : Nat} (s : Fin k → α) : FullType (A.pullback base) k where
  diagram := A.pullback (evaluate base s)
  over_base := fun _ _ => Iff.rfl

/-- Equality of every atomic truth value, including negative, internal and repeated-entry data. -/
def SameFullType {L : Language} {α β : Type} (A : RelStructure L α)
    (base : β → α) {k : Nat} (s t : Fin k → α) : Prop :=
  ∀ R (q : Fin (L.arity R) → Sum β (Fin k)),
    A.rel R (fun i => evaluate base s (q i)) ↔ A.rel R (fun i => evaluate base t (q i))

namespace SameFullType
variable {L : Language} {α β : Type} {A : RelStructure L α} {base : β → α}
variable {k : Nat} {s t u : Fin k → α}

theorem refl (s : Fin k → α) : SameFullType A base s s := fun _ _ => Iff.rfl

theorem symm (h : SameFullType A base s t) : SameFullType A base t s :=
  fun R q => (h R q).symm

theorem trans (h : SameFullType A base s t) (h' : SameFullType A base t u) :
    SameFullType A base s u := fun R q => (h R q).trans (h' R q)

/-- Restriction works for any coordinate map, hence in particular every increasing subtuple. -/
theorem restrict {j : Nat} (ρ : Fin j → Fin k) (h : SameFullType A base s t) :
    SameFullType A base (fun i => s (ρ i)) (fun i => t (ρ i)) := by
  intro R q
  have h' := h R (fun i => match q i with
    | .inl x => .inl x
    | .inr z => .inr (ρ z))
  simpa only [evaluate] using h'

/-- Forgetting parameters preserves equality of full types. -/
theorem restrict_base {δ : Type} (b : δ → β) (h : SameFullType A base s t) :
    SameFullType A (fun x => base (b x)) s t := by
  intro R q
  have h' := h R (fun i => match q i with
    | .inl x => .inl (b x)
    | .inr z => .inr z)
  simpa only [evaluate] using h'
end SameFullType

/-- Pull a full type back along a chosen subtuple. -/
def FullType.restrict {L : Language} {α : Type} {A : RelStructure L α}
    {j k : Nat} (p : FullType A k) (ρ : Fin j → Fin k) : FullType A j where
  diagram := p.diagram.pullback (fun x => match x with
    | .inl a => .inl a
    | .inr i => .inr (ρ i))
  over_base := p.over_base

end AllThoseBigRamsey
