import AllThoseBigRamsey.Relational

/-!
# Algebraic closure in a pure matching

Every vertex has a unique mate. Closed sets are unions of complete
two-vertex components. Their embeddings and closed hulls are described
here without a claim about general Hrushovski predimension closures.
-/
namespace AllThoseBigRamsey.ClosedMatching

abbrev Vertex (n : Nat) := Fin n × Bool

def mate {n : Nat} (v : Vertex n) : Vertex n := (v.1, !v.2)

@[simp] theorem mate_mate {n : Nat} (v : Vertex n) :
    mate (mate v) = v := by
  cases v with
  | mk i b => cases b <;> rfl

theorem mate_ne_self {n : Nat} (v : Vertex n) : mate v ≠ v := by
  cases v with
  | mk i b => cases b <;> simp [mate]

/-- The symmetric graph relation: the second endpoint is the first's mate. -/
def Edge {n : Nat} (u v : Vertex n) : Prop := v = mate u

theorem edge_iff_mate {n : Nat} (u v : Vertex n) :
    Edge u v ↔ v = mate u := Iff.rfl

/-- Sets are represented by predicates; no Mathlib Set API is required. -/
def Closed {n : Nat} (S : Vertex n → Prop) : Prop :=
  ∀ v, S v → S (mate v)

def closure {n : Nat} (S : Vertex n → Prop) : Vertex n → Prop :=
  fun v => S v ∨ S (mate v)

theorem closure_closed {n : Nat} (S : Vertex n → Prop) :
    Closed (closure S) := by
  intro v hv
  rcases hv with hv | hv
  · right
    simpa only [mate_mate] using hv
  · exact Or.inl hv

theorem closure_least {n : Nat} {S T : Vertex n → Prop}
    (hS : ∀ v, S v → T v) (hT : Closed T) :
    ∀ v, closure S v → T v := by
  intro v hv
  rcases hv with hv | hv
  · exact hS v hv
  · have h := hT (mate v) (hS (mate v) hv)
    simpa only [mate_mate] using h

theorem closure_eq_of_closed {n : Nat} {S : Vertex n → Prop}
    (hS : Closed S) : closure S = S := by
  funext v
  apply propext
  constructor
  · exact closure_least (fun _ h => h) hS v
  · exact Or.inl

theorem singleton_not_closed {n : Nat} (v : Vertex n) :
    ¬ Closed (fun x => x = v) := by
  intro h
  have hv : mate v = v := h v rfl
  exact mate_ne_self v hv

structure BlockEmbedding (m n : Nat) where
  block : Fin m → Fin n
  block_injective : Function.Injective block

namespace BlockEmbedding
variable {m n : Nat}

def vertexMap (f : BlockEmbedding m n) (v : Vertex m) : Vertex n :=
  (f.block v.1, v.2)

theorem vertexMap_injective (f : BlockEmbedding m n) :
    Function.Injective f.vertexMap := by
  intro u v h
  cases u with
  | mk i b =>
    cases v with
    | mk j c =>
      have hi : f.block i = f.block j := congrArg Prod.fst h
      have hb : b = c := congrArg Prod.snd h
      have hij := f.block_injective hi
      subst j
      subst c
      rfl

theorem map_mate (f : BlockEmbedding m n) (v : Vertex m) :
    f.vertexMap (mate v) = mate (f.vertexMap v) := rfl

theorem edge_iff (f : BlockEmbedding m n) (u v : Vertex m) :
    Edge (f.vertexMap u) (f.vertexMap v) ↔ Edge u v := by
  change f.vertexMap v = mate (f.vertexMap u) ↔ v = mate u
  rw [← f.map_mate u]
  constructor
  · exact f.vertexMap_injective
  · intro h
    exact congrArg f.vertexMap h

/-- Image in predicate notation. -/
def image {α β : Type} (f : α → β) (S : α → Prop) (v : β) : Prop :=
  ∃ u, S u ∧ f u = v

theorem image_closed (f : BlockEmbedding m n)
    {S : Vertex m → Prop} (hS : Closed S) :
    Closed (image f.vertexMap S) := by
  rintro v ⟨u, hu, rfl⟩
  exact ⟨mate u, hS u hu, f.map_mate u⟩

theorem closure_natural (f : BlockEmbedding m n)
    (S : Vertex m → Prop) (v : Vertex n) :
    image f.vertexMap (closure S) v ↔
      closure (image f.vertexMap S) v := by
  constructor
  · rintro ⟨u, hu, huv⟩
    rcases hu with hu | hu
    · exact Or.inl ⟨u, hu, huv⟩
    · right
      refine ⟨mate u, hu, ?_⟩
      calc
        f.vertexMap (mate u) = mate (f.vertexMap u) := f.map_mate u
        _ = mate v := congrArg mate huv
  · intro h
    rcases h with ⟨u, hu, huv⟩ | ⟨u, hu, huv⟩
    · exact ⟨u, Or.inl hu, huv⟩
    · refine ⟨mate u, Or.inr hu, ?_⟩
      calc
        f.vertexMap (mate u) = mate (f.vertexMap u) := f.map_mate u
        _ = mate (mate v) := congrArg mate huv
        _ = v := mate_mate v

end BlockEmbedding

inductive Symbol
  | edge

def language : Language where
  Symbol := Symbol
  arity := fun _ => 2
  arity_pos := by intro R; cases R; decide

def graph (n : Nat) : RelStructure language (Vertex n) where
  rel := by
    intro R q
    cases R
    exact Edge (q 0) (q 1)

def BlockEmbedding.toGraphEmbedding {m n : Nat} (f : BlockEmbedding m n) :
    Embedding (graph m) (graph n) where
  toFun := f.vertexMap
  injective := by
    intro x y h
    exact f.vertexMap_injective h
  map_rel := by
    intro R q
    cases R
    exact (f.edge_iff (q 0) (q 1)).symm

def appendBlock (m : Nat) : BlockEmbedding m (m+1) where
  block := Fin.castSucc
  block_injective := by
    intro i j h
    exact Fin.ext (congrArg Fin.val h)

def lastBlock (m : Nat) (b : Bool) : Vertex (m+1) := (Fin.last m, b)

theorem append_disjoint (m : Nat) (v : Vertex m) (b : Bool) :
    ¬ Edge ((appendBlock m).vertexMap v) (lastBlock m b) := by
  intro h
  have hh : (Fin.last m) = Fin.castSucc v.1 := congrArg Prod.fst h
  have hv := congrArg Fin.val hh
  simp at hv
  omega

end AllThoseBigRamsey.ClosedMatching
