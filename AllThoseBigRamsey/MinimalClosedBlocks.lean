import Std

/-!
# Minimal closed extensions over one base

In any strong class where finite closed substructures are closed under
intersection, two distinct minimal closed extensions of one closed
base have intersection exactly that base. This applies to the
strong-closure and strict d-closure conventions of the Big Hrushovski
manuscript once their intersection/minimality results are supplied.

Only the abstract predicate-order argument is formalized here.
-/
namespace AllThoseBigRamsey.MinimalClosedBlocks

universe u
variable {α : Type u}

abbrev Pred (α : Type u) := α → Prop

def Subset (S T : Pred α) : Prop := ∀ x, S x → T x

def Inter (S T : Pred α) : Pred α := fun x => S x ∧ T x

/-- Closed extension C of B with no proper intermediate closed D. -/
structure MinimalOver (Closed : Pred α → Prop)
    (B C : Pred α) : Prop where
  base_subset : Subset B C
  proper : ¬ Subset C B
  closed : Closed C
  minimal : ∀ (D : Pred α), Closed D →
    Subset B D → Subset D C → D = B ∨ D = C

theorem distinct_minimal_intersection
    (Closed : Pred α → Prop)
    (hInter : ∀ C D, Closed C → Closed D → Closed (Inter C D))
    {B C D : Pred α}
    (hC : MinimalOver Closed B C)
    (hD : MinimalOver Closed B D)
    (hne : C ≠ D) :
    Inter C D = B := by
  have hInt : Closed (Inter C D) :=
    hInter C D hC.closed hD.closed
  have hBInt : Subset B (Inter C D) := by
    intro x hx
    exact ⟨hC.base_subset x hx, hD.base_subset x hx⟩
  have hIntC : Subset (Inter C D) C := by
    intro x hx
    exact hx.1
  rcases hC.minimal (Inter C D) hInt hBInt hIntC with hbase | hfull
  · exact hbase
  · have hCD : Subset C D := by
      intro x hx
      have hpair : Inter C D x := by
        rw [hfull]
        exact hx
      exact hpair.2
    rcases hD.minimal C hC.closed hC.base_subset hCD with hCB | hCDsame
    · apply False.elim
      apply hC.proper
      intro x hx
      rw [hCB] at hx
      exact hx
    · exact False.elim (hne hCDsame)

theorem distinct_minimal_overlap_only_base
    (Closed : Pred α → Prop)
    (hInter : ∀ C D, Closed C → Closed D → Closed (Inter C D))
    {B C D : Pred α}
    (hC : MinimalOver Closed B C)
    (hD : MinimalOver Closed B D)
    (hne : C ≠ D)
    {x : α} (hx : C x) (hy : D x) :
    B x := by
  have heq : Inter C D = B :=
    distinct_minimal_intersection Closed hInter hC hD hne
  have hi : Inter C D x := ⟨hx,hy⟩
  rw [heq] at hi
  exact hi

end AllThoseBigRamsey.MinimalClosedBlocks
