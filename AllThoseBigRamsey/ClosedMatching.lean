import AllThoseBigRamsey.Relational
import Std.Tactic.Omega

/-!
# Matching closure and closed-block embeddings

The countable disjoint matching has a definable involution assigning the
unique mate of each vertex. A closed finite substructure contains both
endpoints of each of its components. Minimal nonempty closed extensions
are whole edge blocks, not single vertices.

This module checks the concrete closed category and naturality of its
closure. It does not assert a general closure-relative TRAP theorem for
Hrushovski predimension classes.
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

def Edge {n : Nat} (u v : Vertex n) : Prop :=
  u.1 = v.1 ∧ u.2 ≠ v.2

theorem edge_to_mate {n : Nat} (v : Vertex n) : Edge v (mate v) := by
  cases v with
  | mk i b => cases b <;> simp [Edge, mate]

theorem edge_iff_mate {n : Nat} (u v : Vertex n) :
    Edge u v ↔ v = mate u := by
  cases u with
  | mk i b =>
    cases v with
    | mk j c =>
      cases b <;> cases c <;> simp [Edge, mate, Prod.mk.injEq]

def Closed {n : Nat} (S : Set (Vertex n)) : Prop :=
  ∀ v, v ∈ S → mate v ∈ S

def closure {n : Nat} (S : Set (Vertex n)) : Set (Vertex n) :=
  fun v => v ∈ S ∨ mate v ∈ S

theorem closure_closed {n : Nat} (S : Set (Vertex n)) :
    Closed (closure S) := by
  intro v hv
  rcases hv with hv | hv
  · right
    simpa only [mate_mate] using hv
  · left
    exact hv

theorem closure_least {n : Nat} {S T : Set (Vertex n)}
    (hS : S ⊆ T) (hT : Closed T) : closure S ⊆ T := by
  intro v hv
  rcases hv with hv | hv
  · exact hS hv
  · have hh := hT (mate v) (hS hv)
    simpa using hh

theorem closure_eq_of_closed {n : Nat} {S : Set (Vertex n)}
    (hS : Closed S) : closure S = S := by
  apply Set.ext
  intro v
  constructor
  · exact closure_least (Set.Subset.rfl) hS
  · exact Or.inl

theorem singleton_not_closed {n : Nat} (v : Vertex n) :
    ¬ Closed ({v} : Set (Vertex n)) := by
  intro h
  have hv : mate v ∈ ({v} : Set (Vertex n)) := h v (by simp)
  have heq : mate v = v := by simpa using hv
  exact mate_ne_self v heq

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
  change (f.block u.1 = f.block v.1 ∧ u.2 ≠ v.2) ↔
    (u.1 = v.1 ∧ u.2 ≠ v.2)
  constructor
  · rintro ⟨he, hb⟩
    exact ⟨f.block_injective he, hb⟩
  · rintro ⟨he, hb⟩
    exact ⟨congrArg f.block he, hb⟩

theorem image_closed (f : BlockEmbedding m n)
    {S : Set (Vertex m)} (hS : Closed S) :
    Closed (f.vertexMap '' S) := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨mate u, hS u hu, f.map_mate u⟩

theorem closure_natural (f : BlockEmbedding m n)
    (S : Set (Vertex m)) :
    f.vertexMap '' (closure S) = closure (f.vertexMap '' S) := by
  apply Set.ext
  intro v
  constructor
  · rintro ⟨u, (hu | hu), rfl⟩
    · exact Or.inl ⟨u, hu, rfl⟩
    · exact Or.inr ⟨mate u, hu, f.map_mate u⟩
  · intro h
    rcases h with ⟨u, hu, rfl⟩ | ⟨u, hu, heq⟩
    · exact ⟨u, Or.inl hu, rfl⟩
    · refine ⟨mate u, Or.inr hu, ?_⟩
      calc
        f.vertexMap (mate u) = mate (f.vertexMap u) := f.map_mate u
        _ = mate (mate v) := congrArg mate heq
        _ = v := mate_mate v

end BlockEmbedding

inductive Symbol
  | edge

def language : Language where
  Symbol := Symbol
  arity := fun _ => 2
  arity_pos := by intro R; cases R; decide

def graph (n : Nat) : RelStructure language (Vertex n) where
  rel := fun _ q => Edge (q 0) (q 1)

def BlockEmbedding.toGraphEmbedding {m n : Nat} (f : BlockEmbedding m n) :
    Embedding (graph m) (graph n) where
  toFun := f.vertexMap
  injective := f.vertexMap_injective
  map_rel := by
    intro R q
    exact (f.edge_iff (q 0) (q 1)).symm

def appendBlock (m : Nat) : BlockEmbedding m (m + 1) where
  block := Fin.castSucc
  block_injective := Fin.castSucc_injective m

def lastBlock (m : Nat) (b : Bool) : Vertex (m + 1) := (Fin.last m, b)

theorem append_disjoint (m : Nat) (v : Vertex m) (b : Bool) :
    ¬ Edge ((appendBlock m).vertexMap v) (lastBlock m b) := by
  intro h
  have hh := congrArg Fin.val h.1
  simp [BlockEmbedding.vertexMap, appendBlock, lastBlock] at hh
  omega

end AllThoseBigRamsey.ClosedMatching
