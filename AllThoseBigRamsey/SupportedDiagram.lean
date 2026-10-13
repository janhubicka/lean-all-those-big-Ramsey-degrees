import AllThoseBigRamsey.SupportClosed

/-!
# Support-closed partial relational diagrams

The permitted truth values of a partial diagram are specified precisely
on E-clique supports.  The neutral completion is independent of any
initially chosen full completion.  The main theorem proves that, if a
completion excludes an irreducible induced forbidden structure, the neutral
completion excludes it too.

The actual successor E-spacing and class-level TRAP interfaces are not
asserted here.  This is an arbitrary-arity relational core.
-/
namespace AllThoseBigRamsey.SupportedDiagram

open SupportClosed

/-- On supported tuples both truth and falsity are prescribed. -/
structure Partial (L : Language) (α : Type) where
  mark : α → α → Prop
  value : (R : L.Symbol) → (q : Fin (L.arity R) → α) →
    PairMarked mark q → Prop

namespace Partial
variable {L : Language} {α β : Type}

/-- Every atom outside the supported region is set to false. -/
def neutral (P : Partial L α) : RelStructure L α where
  rel := fun R q => ∃ hm : PairMarked P.mark q, P.value R q hm

/-- A full diagram extends exactly the specified supported atomic diagram. -/
def Extends (P : Partial L α) (D : RelStructure L α) : Prop :=
  ∀ R q (hm : PairMarked P.mark q),
    (D.rel R q ↔ P.value R q hm)

theorem neutral_extends (P : Partial L α) : P.Extends P.neutral := by
  intro R q hm
  constructor
  · rintro ⟨hm', hv⟩
    exact hv
  · intro hv
    exact ⟨hm, hv⟩

/-- The neutral completion of a partial diagram is obtained by
neutralising any of its full completions. -/
theorem neutral_equiv_neutralise
    (P : Partial L α) (D : RelStructure L α) (hD : P.Extends D)
    (R : L.Symbol) (q : Fin (L.arity R) → α) :
    P.neutral.rel R q ↔ (neutralise D P.mark).rel R q := by
  constructor
  · rintro ⟨hm, hv⟩
    exact ⟨(hD R q hm).mpr hv, hm⟩
  · rintro ⟨hv, hm⟩
    exact ⟨hm, (hD R q hm).mp hv⟩

/-- A forbidden induced copy in the neutral completion would already
occur in any valid completion, for every irreducible F. -/
theorem neutral_omits_irreducible
    (P : Partial L α) (D : RelStructure L α)
    (hD : P.Extends D)
    {F : RelStructure L β} (hF : Irreducible F)
    (hfree : ¬ Nonempty (Embedding F D)) :
    ¬ Nonempty (Embedding F P.neutral) := by
  rintro ⟨e⟩
  let e' : Embedding F (neutralise D P.mark) := {
    toFun := e.toFun
    injective := e.injective
    map_rel := by
      intro R q
      exact (e.map_rel R q).trans
        (P.neutral_equiv_neutralise D hD R (fun i => e.toFun (q i))) }
  exact hfree ⟨lift_embedding D P.mark hF e'⟩

/-- Pull back marks and supported values along an injective restriction. -/
def restrict (P : Partial L α) (f : β → α) : Partial L β where
  mark := fun x y => P.mark (f x) (f y)
  value := fun R q hq =>
    P.value R (fun i => f (q i)) (by
      intro i j hij
      exact hq i j (fun heq => hij (congrArg f heq)))

/-- Neutral completion commutes with injective restriction, including
positive, negative, unary, repeated-entry and higher-arity tuples. -/
theorem neutral_restrict
    (P : Partial L α) (f : β → α) (hf : Function.Injective f)
    (R : L.Symbol) (q : Fin (L.arity R) → β) :
    (P.restrict f).neutral.rel R q ↔
      P.neutral.rel R (fun i => f (q i)) := by
  constructor
  · rintro ⟨hm, hv⟩
    have hm' : PairMarked P.mark (fun i => f (q i)) := by
      intro i j hij
      exact hm i j (fun heq => hij (congrArg f heq))
    exact ⟨hm', hv⟩
  · rintro ⟨hm, hv⟩
    have hm' : PairMarked (fun x y => P.mark (f x) (f y)) q := by
      intro i j hij
      exact hm i j (fun h => hij (hf h))
    exact ⟨hm', hv⟩

end Partial
end AllThoseBigRamsey.SupportedDiagram
