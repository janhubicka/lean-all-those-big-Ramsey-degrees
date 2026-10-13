import AllThoseBigRamsey.FullTypes

/-!
# Neutral completion of support-closed partial structures

For a partial relational diagram, let E mark the pairs of vertices whose
relations have already been decided.  Neutral completion deletes all positive
tuples whose distinct vertices are not pairwise E-marked.

The key observation is that an irreducible forbidden structure cannot be
created by this operation: every pair of vertices of a forbidden copy occurs
in a positive relation tuple, so the copy must lie entirely in the region
where every atomic relation is unchanged.

Unlike a maximum-vertex-only determination rule, pairwise support closure
remains valid for arbitrary relation arities and repeated coordinates.
-/
namespace AllThoseBigRamsey.SupportClosed

variable {L : Language} {α β : Type}

/-- Every pair of distinct vertices occurring in a tuple is marked. -/
def PairMarked (E : α → α → Prop) {k : Nat} (q : Fin k → α) : Prop :=
  ∀ i j, q i ≠ q j → E (q i) (q j)

/-- Delete all positive tuples containing a pair not marked by E.
No relation is added, including on diagonal and repeated-entry tuples. -/
def neutralise (D : RelStructure L α) (E : α → α → Prop) :
    RelStructure L α where
  rel := fun R q => D.rel R q ∧ PairMarked E q

theorem neutralise_rel_iff_of_marked
    (D : RelStructure L α) (E : α → α → Prop)
    (R : L.Symbol) (q : Fin (L.arity R) → α)
    (hq : PairMarked E q) :
    (neutralise D E).rel R q ↔ D.rel R q := by
  simp [neutralise, hq]

theorem neutralise_no_new_positive
    (D : RelStructure L α) (E : α → α → Prop)
    (R : L.Symbol) (q : Fin (L.arity R) → α)
    (h : (neutralise D E).rel R q) : D.rel R q :=
  h.1

/-- An irreducible structure has a positive relational witness for each
ordered pair of distinct vertices.  The language need not be binary. -/
def Irreducible (F : RelStructure L β) : Prop :=
  ∀ x y : β, x ≠ y →
    ∃ R : L.Symbol, ∃ q : Fin (L.arity R) → β,
      ∃ i j : Fin (L.arity R),
        F.rel R q ∧ q i = x ∧ q j = y

theorem pair_marked_of_irreducible_embedding
    (D : RelStructure L α) (E : α → α → Prop)
    {F : RelStructure L β}
    (hF : Irreducible F)
    (e : Embedding F (neutralise D E))
    {x y : β} (hxy : x ≠ y) :
    E (e.toFun x) (e.toFun y) := by
  obtain ⟨R, q, i, j, hR, hi, hj⟩ := hF x y hxy
  have hs : PairMarked E (fun a => e.toFun (q a)) :=
    ((e.map_rel R q).mp hR).2
  have hne : e.toFun (q i) ≠ e.toFun (q j) := by
    intro h
    apply hxy
    have heq : q i = q j := e.injective h
    calc
      x = q i := hi.symm
      _ = q j := heq
      _ = y := hj
  have hm := hs i j hne
  simpa only [hi, hj] using hm

/-- An embedding of an irreducible structure into the neutral completion
already embeds it into the original structure.  Both directions of atomic
truth are proved; this is about induced embeddings, not homomorphisms. -/
def lift_embedding
    (D : RelStructure L α) (E : α → α → Prop)
    {F : RelStructure L β}
    (hF : Irreducible F)
    (e : Embedding F (neutralise D E)) :
    Embedding F D where
  toFun := e.toFun
  injective := e.injective
  map_rel := by
    intro R q
    constructor
    · intro h
      exact ((e.map_rel R q).mp h).1
    · intro h
      apply (e.map_rel R q).mpr
      constructor
      · exact h
      · intro i j hne
        apply pair_marked_of_irreducible_embedding D E hF e
        intro heq
        apply hne
        exact congrArg e.toFun heq

theorem neutralise_omits_irreducible
    (D : RelStructure L α) (E : α → α → Prop)
    {F : RelStructure L β}
    (hF : Irreducible F)
    (hD : ¬ Nonempty (Embedding F D)) :
    ¬ Nonempty (Embedding F (neutralise D E)) := by
  intro h
  rcases h with ⟨e⟩
  exact hD ⟨lift_embedding D E hF e⟩

/-- Two completions agreeing on all E-supported atomic facts have
identical neutralisations.  This is the source of canonical
same-socle compatibility. -/
theorem neutralise_unique
    (D₁ D₂ : RelStructure L α) (E : α → α → Prop)
    (h : ∀ (R : L.Symbol) (q : Fin (L.arity R) → α),
      PairMarked E q → (D₁.rel R q ↔ D₂.rel R q))
    (R : L.Symbol) (q : Fin (L.arity R) → α) :
    (neutralise D₁ E).rel R q ↔ (neutralise D₂ E).rel R q := by
  by_cases hmark : PairMarked E q
  · simpa [neutralise, hmark] using h R q hmark
  · simp [neutralise, hmark]

/-- Neutralisation commutes with restriction along an injective vertex map
when the auxiliary mark is restricted along the same map. -/
theorem neutralise_restrict
    (D : RelStructure L α) (E : α → α → Prop)
    (f : β → α) (hf : Function.Injective f)
    (R : L.Symbol) (q : Fin (L.arity R) → β) :
    ((neutralise D E).pullback f).rel R q ↔
      (neutralise (D.pullback f) (fun x y => E (f x) (f y))).rel R q := by
  have hm :
      PairMarked E (fun i => f (q i)) ↔
        PairMarked (fun x y => E (f x) (f y)) q := by
    constructor
    · intro h i j hij
      exact h i j (fun hEq => hij (hf hEq))
    · intro h i j hij
      exact h i j (fun hEq => hij (congrArg f hEq))
  exact and_congr Iff.rfl hm

/-- If every positive tuple is E-supported, neutralisation changes nothing. -/
theorem neutralise_fixed
    (D : RelStructure L α) (E : α → α → Prop)
    (h : ∀ R q, D.rel R q → PairMarked E q)
    (R : L.Symbol) (q : Fin (L.arity R) → α) :
    (neutralise D E).rel R q ↔ D.rel R q := by
  constructor
  · exact And.left
  · intro hD
    exact ⟨hD, h R q hD⟩

end AllThoseBigRamsey.SupportClosed
