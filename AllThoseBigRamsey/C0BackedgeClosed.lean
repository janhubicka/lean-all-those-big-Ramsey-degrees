import AllThoseBigRamsey.UnaryClosedUnion

/-!
# Closure of C0 components and absence of crossing graph edges

The unary closure-component presentation of the big Hrushovski C0 graph
contains the whole component of every vertex and all earlier endpoints
of its back edges.

Hence if A,B are closed under that unary operation, no graph edge joins
A \\ B to B \\ A. Their union is already the free graph amalgam over
their intersection. This is stronger than the predimension cross-edge
bound for disjoint strong substructures.

These are structural implications of the explicit back-edge closure
laws. They do not assume class-level TRAP or the yet-unverified
countable functional limit identification.
-/
namespace AllThoseBigRamsey.C0BackedgeClosed

universe u
variable {α : Type u}

structure Presentation (α : Type u) where
  componentIndex : α → Nat
  graphEdge : α → α → Prop
  symmetric : ∀ x y, graphEdge x y → graphEdge y x
  unaryClosure : UnaryClosedUnion.UnaryValues α
  sameComponent :
    ∀ x y, componentIndex x = componentIndex y →
      unaryClosure.value x y
  backEdge :
    ∀ x y, graphEdge x y →
      componentIndex y < componentIndex x →
      unaryClosure.value x y

def Closed (P : Presentation α) (S : α → Prop) : Prop :=
  UnaryClosedUnion.Closed P.unaryClosure S

theorem no_cross_exclusive
    (P : Presentation α)
    {A B : α → Prop}
    (hA : P.Closed A) (hB : P.Closed B)
    {x y : α}
    (hAx : A x) (hnBx : ¬ B x)
    (hBy : B y) (hnAy : ¬ A y)
    (hxy : P.graphEdge x y) : False := by
  rcases lt_trichotomy (P.componentIndex x) (P.componentIndex y) with
    hlt | heq | hgt
  · have hval : P.unaryClosure.value y x :=
      P.backEdge y x (P.symmetric x y hxy) hlt
    exact hnBx (hB y x hBy hval)
  · have hval : P.unaryClosure.value x y :=
      P.sameComponent x y heq
    exact hnAy (hA x y hAx hval)
  · have hval : P.unaryClosure.value x y :=
      P.backEdge x y hxy hgt
    exact hnAy (hA x y hAx hval)

theorem disjoint_closed_no_edge
    (P : Presentation α)
    {A B : α → Prop}
    (hA : P.Closed A) (hB : P.Closed B)
    (hdisj : ∀ x, A x → ¬ B x)
    {x y : α} (hx : A x) (hy : B y) :
    ¬ P.graphEdge x y := by
  intro hxy
  exact P.no_cross_exclusive hA hB hx (hdisj x hx) hy
    (fun hAy => hdisj y hAy hy) hxy

/-- Every graph edge in the union of two closed substructures
belongs wholly to one factor. Thus their union is the free
graph amalgam over the intersection. -/
theorem union_edges_in_one_side
    (P : Presentation α)
    {A B : α → Prop}
    (hA : P.Closed A) (hB : P.Closed B)
    {x y : α}
    (hx : A x ∨ B x) (hy : A y ∨ B y)
    (hxy : P.graphEdge x y) :
    (A x ∧ A y) ∨ (B x ∧ B y) := by
  rcases hx with hxA | hxB
  · rcases hy with hyA | hyB
    · exact Or.inl ⟨hxA,hyA⟩
    · by_cases hxB : B x
      · exact Or.inr ⟨hxB,hyB⟩
      · by_cases hyA : A y
        · exact Or.inl ⟨hxA,hyA⟩
        · exact False.elim
            (P.no_cross_exclusive hA hB hxA hxB hyB hyA hxy)
  · rcases hy with hyA | hyB
    · by_cases hxA : A x
      · exact Or.inl ⟨hxA,hyA⟩
      · by_cases hyB : B y
        · exact Or.inr ⟨hxB,hyB⟩
        · exact False.elim
            (P.no_cross_exclusive hA hB hyA hyB hxB hxA
              (P.symmetric x y hxy))
    · exact Or.inr ⟨hxB,hyB⟩

theorem union_closed (P : Presentation α)
    {A B : α → Prop}
    (hA : P.Closed A) (hB : P.Closed B) :
    P.Closed (UnaryClosedUnion.Union A B) :=
  UnaryClosedUnion.union_closed P.unaryClosure hA hB

end AllThoseBigRamsey.C0BackedgeClosed
