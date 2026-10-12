import AllThoseBigRamsey.Relational

/-! Full quantifier-free types: the entire induced diagram, not a mixed fragment. -/
namespace AllThoseBigRamsey

/-- A full `k`-type over `A`, with distinct new vertices in their specified order. -/
structure FullType {L : Language} {α : Type} (A : RelStructure L α) (k : Nat) where
  diagram : RelStructure L (Sum α (Fin k))
  over_base : ∀ R q, diagram.rel R (fun i => Sum.inl (q i)) ↔ A.rel R q

/-- Pull back a structure along a map; an induced-copy interpretation requires injectivity. -/
def RelStructure.pullback {L : Language} {α β : Type}
    (A : RelStructure L α) (f : β → α) : RelStructure L β where
  rel := fun R q => A.rel R (fun i => f (q i))

/-- Evaluate a term naming either an old parameter or one new vertex. -/
def evaluate {α β : Type} {k : Nat} (base : β → α) (s : Fin k → α) : Sum β (Fin k) → α
  | .inl x => base x
  | .inr i => s i

/-- Evaluation commutes with changing the names of future coordinates. -/
theorem evaluate_reindex {α β : Type} {j k : Nat} (base : β → α)
    (s : Fin k → α) (ρ : Fin j → Fin k) (z : Sum β (Fin j)) :
    evaluate base s (Sum.map (fun x => x) ρ z) =
      evaluate base (fun i => s (ρ i)) z := by
  cases z <;> rfl

/-- Evaluation commutes with changing the names of base parameters. -/
theorem evaluate_rebase {α β δ : Type} {k : Nat} (base : β → α)
    (s : Fin k → α) (b : δ → β) (z : Sum δ (Fin k)) :
    evaluate base s (Sum.map b (fun i => i) z) =
      evaluate (fun x => base (b x)) s z := by
  cases z <;> rfl

/-- Relational diagram on distinct formal names. This is the realised full type
when `evaluate base s` is injective; otherwise it is only a pulled-back diagram. -/
def typeOf {L : Language} {α β : Type} (A : RelStructure L α)
    (base : β → α) {k : Nat} (s : Fin k → α) : FullType (A.pullback base) k where
  diagram := A.pullback (evaluate base s)
  over_base := fun _ _ => Iff.rfl

/-- Equality of every atomic relation value. For distinct tuples disjoint from
the injectively named base this is equality of full quantifier-free types. -/
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

/-- Restriction of atomic diagrams works for every coordinate map. Realised
full subtypes use increasing injections between the coordinate sets. -/
theorem restrict {j : Nat} (ρ : Fin j → Fin k) (h : SameFullType A base s t) :
    SameFullType A base (fun i => s (ρ i)) (fun i => t (ρ i)) := by
  intro R q
  have h' := h R (fun i => Sum.map (fun x => x) ρ (q i))
  simpa only [evaluate_reindex] using h'

/-- Forgetting parameters preserves equality of full types. -/
theorem restrict_base {δ : Type} (b : δ → β) (h : SameFullType A base s t) :
    SameFullType A (fun x => base (b x)) s t := by
  intro R q
  have h' := h R (fun i => Sum.map b (fun x => x) (q i))
  simpa only [evaluate_rebase] using h'
end SameFullType

/-- Pull a formal type diagram back along a coordinate map. -/
def FullType.restrict {L : Language} {α : Type} {A : RelStructure L α}
    {j k : Nat} (p : FullType A k) (ρ : Fin j → Fin k) : FullType A j where
  diagram := p.diagram.pullback (Sum.map (fun a => a) ρ)
  over_base := p.over_base

end AllThoseBigRamsey
