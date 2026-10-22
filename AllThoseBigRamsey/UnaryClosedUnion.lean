import AllThoseBigRamsey.MinimalClosedBlocks

/-!
# Union and intersection of unary-closed substructures

A family of set-valued unary operations is encoded by a binary
input-output relation. A closed set contains every output of an
operation applied to one of its vertices.

Unions and intersections of these closed sets are closed. This
is the precise property used to convert minimal closed extensions
into vertices of a relational free-amalgamation class.

No assertion about multi-input closure operations is made.
-/
namespace AllThoseBigRamsey.UnaryClosedUnion

universe u
variable {α : Type u}

/-- A unary closure system, including set-valued outputs.
A finite collection of unary symbols can be absorbed in value. -/
structure UnaryValues (α : Type u) where
  value : α → α → Prop

def Closed (f : UnaryValues α) (S : α → Prop) : Prop :=
  ∀ x y, S x → f.value x y → S y

def Union (S T : α → Prop) : α → Prop :=
  fun x => S x ∨ T x

def Inter (S T : α → Prop) : α → Prop :=
  fun x => S x ∧ T x

theorem union_closed (f : UnaryValues α)
    {S T : α → Prop} (hS : Closed f S) (hT : Closed f T) :
    Closed f (Union S T) := by
  intro x y hx hxy
  rcases hx with hx | hx
  · exact Or.inl (hS x y hx hxy)
  · exact Or.inr (hT x y hx hxy)

theorem inter_closed (f : UnaryValues α)
    {S T : α → Prop} (hS : Closed f S) (hT : Closed f T) :
    Closed f (Inter S T) := by
  intro x y hx hxy
  exact ⟨hS x y hx.1 hxy, hT x y hx.2 hxy⟩

/-- Every finite union of closed sets is closed. -/
def BigUnion (Ss : List (α → Prop)) : α → Prop :=
  fun x => ∃ S, S ∈ Ss ∧ S x

theorem bigUnion_closed (f : UnaryValues α)
    (Ss : List (α → Prop)) (h : ∀ S, S ∈ Ss → Closed f S) :
    Closed f (BigUnion Ss) := by
  intro x y hx hxy
  rcases hx with ⟨S, hS, hxS⟩
  exact ⟨S, hS, h S hS x y hxS hxy⟩

/-- For unary closure, different minimal closed extensions of B
cannot share any vertex outside B. -/
theorem minimal_blocks_intersect_in_base
    (f : UnaryValues α)
    {B C D : α → Prop}
    (hC : MinimalClosedBlocks.MinimalOver (Closed f) B C)
    (hD : MinimalClosedBlocks.MinimalOver (Closed f) B D)
    (hne : C ≠ D) :
    (fun x => C x ∧ D x) = B := by
  apply MinimalClosedBlocks.distinct_minimal_intersection
    (Closed f)
  · intro S T hS hT
    exact inter_closed f hS hT
  · exact hC
  · exact hD
  · exact hne

theorem minimal_blocks_no_shared_new_vertex
    (f : UnaryValues α)
    {B C D : α → Prop}
    (hC : MinimalClosedBlocks.MinimalOver (Closed f) B C)
    (hD : MinimalClosedBlocks.MinimalOver (Closed f) B D)
    (hne : C ≠ D) {x : α}
    (hx : C x) (hy : D x) :
    B x := by
  have hi := minimal_blocks_intersect_in_base f hC hD hne
  have hpair : (fun x => C x ∧ D x) x := ⟨hx, hy⟩
  rw [hi] at hpair
  exact hpair

end AllThoseBigRamsey.UnaryClosedUnion
