import AllThoseBigRamsey.FullTypes

/-! Actual relational embeddings cannot place an irreducible forbidden structure
across a free union. No bound on the forbidden structure's size is assumed. -/
namespace AllThoseBigRamsey

/-- Irreducibility uses every distinct pair, and allows arbitrary relation arities. -/
def Irreducible {L : Language} {α : Type} (A : RelStructure L α) : Prop :=
  ∀ x y, x ≠ y → ∃ R, ∃ t : Fin (L.arity R) → α,
    ∃ i j, A.rel R t ∧ t i = x ∧ t j = y

namespace Embedding

/-- Restrict the target of an actual embedding to an induced substructure. -/
def intoInduced {L : Language} {α β : Type}
    {A : RelStructure L α} {B : RelStructure L β}
    (e : Embedding A B) (P : β → Prop) (h : ∀ x, P (e.toFun x)) :
    Embedding A (B.pullback (fun x : {b // P b} => x.val)) where
  toFun := fun x => ⟨e.toFun x, h x⟩
  injective := fun heq => e.injective (congrArg Subtype.val heq)
  map_rel := e.map_rel
end Embedding

namespace Irreducible
variable {L : Language} {α β : Type}
variable {F : RelStructure L α} {D : RelStructure L β}

/-- If every relation tuple lies in one side of a cover, an irreducible
embedded structure lies wholly in one side. Singleton and empty cases are included. -/
theorem range_in_one_side (irr : Irreducible F) (e : Embedding F D)
    (U V : β → Prop) (cover : ∀ x, U x ∨ V x)
    (tuples : ∀ R t, D.rel R t → (∀ i, U (t i)) ∨ (∀ i, V (t i))) :
    (∀ x, U (e.toFun x)) ∨ (∀ x, V (e.toFun x)) := by
  classical
  by_cases hu : ∀ x, U (e.toFun x)
  · exact Or.inl hu
  · right
    obtain ⟨x, hx⟩ := Classical.not_forall.mp hu
    intro y
    by_cases hy : V (e.toFun y)
    · exact hy
    · have hxy : x ≠ y := by
        intro heq
        subst y
        exact hx ((cover (e.toFun x)).resolve_right hy)
      obtain ⟨R, t, i, j, ht, hi, hj⟩ := irr x y hxy
      have htD := (e.map_rel R t).mp ht
      rcases tuples R (fun d => e.toFun (t d)) htD with hU | hV
      · have h := hU i
        rw [hi] at h
        exact False.elim (hx h)
      · have h := hV j
        rw [hj] at h
        exact False.elim (hy h)
end Irreducible

/-- Forbidding an induced embedding, not a homomorphism. -/
def Avoids {L : Language} {α β : Type}
    (F : RelStructure L α) (D : RelStructure L β) : Prop :=
  ∀ _ : Embedding F D, False

/-- The relational obstruction step for free amalgamation and the full-type
insertion construction. Applying this to every member handles infinite families. -/
theorem avoids_of_free_cover {L : Language} {α β : Type}
    {F : RelStructure L α} {D : RelStructure L β} (irr : Irreducible F)
    (U V : β → Prop) (cover : ∀ x, U x ∨ V x)
    (tuples : ∀ R t, D.rel R t → (∀ i, U (t i)) ∨ (∀ i, V (t i)))
    (left : Avoids F (D.pullback (fun x : {b // U b} => x.val)))
    (right : Avoids F (D.pullback (fun x : {b // V b} => x.val))) :
    Avoids F D := by
  intro e
  rcases irr.range_in_one_side e U V cover tuples with hU | hV
  · exact left (e.intoInduced U hU)
  · exact right (e.intoInduced V hV)
end AllThoseBigRamsey
