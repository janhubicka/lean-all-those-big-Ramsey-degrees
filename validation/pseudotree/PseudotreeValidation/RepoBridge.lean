import AllThoseBigRamsey.Relational
import PseudotreeValidation.Indivisibility

/-!
# The functional model in the repository's big Ramsey definition

The outer repository uses relational structures. We retain both the order
relation and the graph of meet, and prove that its embeddings are exactly
the functional-language embeddings used in the manuscript validation. The
finite-set and finite-list palette conventions are also proved equivalent.
-/

namespace AllThoseBigRamsey.Pseudotree.RepoBridge

open scoped FirstOrder

inductive Symbol
  | le | meetGraph

def signature : AllThoseBigRamsey.Language where
  Symbol := Symbol
  arity
    | .le => 2
    | .meetGraph => 3
  arity_pos := by intro R; cases R <;> decide

def model (M : Type) [SemilatticeInf M] : RelStructure signature M where
  rel := by
    intro R
    cases R with
    | le => exact fun q : Fin 2 → M => q 0 ≤ q 1
    | meetGraph => exact fun q : Fin 3 → M => q 0 ⊓ q 1 = q 2

variable {M N K : Type} [SemilatticeInf M] [SemilatticeInf N] [SemilatticeInf K]

def ofFunctional (e : M ↪[language] N) : Embedding (model M) (model N) where
  toFun := e
  injective := fun h => e.injective h
  map_rel := by
    intro R q
    cases R with
    | le => exact (embeddingOrderEmbedding e).le_iff_le.symm
    | meetGraph =>
      change Fin 3 → M at q
      change q 0 ⊓ q 1 = q 2 ↔ e (q 0) ⊓ e (q 1) = e (q 2)
      rw [← embedding_map_inf e]
      exact e.injective.eq_iff.symm

def toFunctional (e : Embedding (model M) (model N)) : M ↪[language] N :=
  embeddingOfInfMap e.toFun (fun _ _ h => e.injective h) (by
    intro a b
    let q : Fin 3 → M := fun i => if i = 0 then a else if i = 1 then b else a ⊓ b
    have h := (e.map_rel Symbol.meetGraph q).mp (by simp [model, q])
    have heq : e.toFun a ⊓ e.toFun b = e.toFun (a ⊓ b) := by simpa [model, q] using h
    exact heq.symm)

omit [SemilatticeInf M] [SemilatticeInf N] in
theorem embedding_ext {A : RelStructure signature M} {B : RelStructure signature N}
    (e f : Embedding A B) (h : ∀ x, e.toFun x = f.toFun x) : e = f := by
  cases e with
  | mk ef ei er =>
    cases f with
    | mk ff fi fr =>
      have heq : ef = ff := funext h
      cases heq
      rfl

@[simp] theorem to_of (e : M ↪[language] N) : toFunctional (ofFunctional e) = e := by
  apply FirstOrder.Language.Embedding.ext
  intro x
  rfl

@[simp] theorem of_to (e : Embedding (model M) (model N)) :
    ofFunctional (toFunctional e) = e := embedding_ext _ _ (fun _ => rfl)

@[simp] theorem ofFunctional_comp (f : N ↪[language] K) (e : M ↪[language] N) :
    ofFunctional (f.comp e) = Embedding.comp (ofFunctional f) (ofFunctional e) :=
  embedding_ext _ _ (fun _ => rfl)

@[simp] theorem toFunctional_comp
    (f : Embedding (model N) (model K)) (e : Embedding (model M) (model N)) :
    toFunctional (Embedding.comp f e) = (toFunctional f).comp (toFunctional e) := by
  apply FirstOrder.Language.Embedding.ext
  intro x
  rfl

/-- The existing repository predicate and the functional-language predicate
have exactly the same finite bounds, including the palette cardinality. -/
theorem bound_iff (A : Type) [SemilatticeInf A] (d : ℕ) :
    BigRamseyBound (model A) (model TernaryModel) d ↔
      Incomparables.FunctionalBigRamseyBound A d := by
  classical
  constructor
  · intro h r hr colour
    obtain ⟨f, palette, hcard, hcover⟩ := h r hr (fun e => colour (toFunctional e))
    refine ⟨toFunctional f, palette.toFinset,
      (List.toFinset_card_le _).trans hcard, ?_⟩
    intro e
    apply List.mem_toFinset.mpr
    simpa only [toFunctional_comp, to_of] using hcover (ofFunctional e)
  · intro h r hr colour
    obtain ⟨f, palette, hcard, hcover⟩ := h r hr (fun e => colour (ofFunctional e))
    refine ⟨ofFunctional f, palette.toList, ?_, ?_⟩
    · simpa only [Finset.length_toList] using hcard
    · intro e
      apply Finset.mem_toList.mpr
      simpa only [ofFunctional_comp, of_to] using hcover (toFunctional e)

/-- The already proved incomparable theorem is an infinite degree in the
repository's own definition, for the signature retaining meet's graph. -/
theorem incomparable_degree_infinite (A : Type) [SemilatticeInf A] [Finite A]
    (hA : Nonempty (A ↪[language] TernaryModel))
    {x y : A} (hxy : ¬x ≤ y) (hyx : ¬y ≤ x) :
    IsBigRamseyDegree (model A) (model TernaryModel) none := by
  intro d hd
  exact Incomparables.no_finite_bound hA hxy hyx d ((bound_iff A d).mp hd)

/-- End-to-end exact singleton degree, in the existing repository API. -/
theorem singleton_degree :
    IsBigRamseyDegree (model (Fin 1)) (model TernaryModel) (some 1) := by
  constructor
  · exact (bound_iff (Fin 1) 1).mpr singleton_chain_bound
  · intro d hd
    exact singleton_chain_minimal ((bound_iff (Fin 1) d).mp hd)

end AllThoseBigRamsey.Pseudotree.RepoBridge
