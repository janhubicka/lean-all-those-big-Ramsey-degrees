import Std

/-! Relational structures and embeddings. Tuples may have repeated entries. -/
namespace AllThoseBigRamsey

structure Language where
  Symbol : Type
  arity : Symbol → Nat
  arity_pos : ∀ R, 0 < arity R

structure RelStructure (L : Language) (α : Type) where
  rel : (R : L.Symbol) → (Fin (L.arity R) → α) → Prop

structure Embedding {L : Language} {α β : Type}
    (A : RelStructure L α) (B : RelStructure L β) where
  toFun : α → β
  injective : ∀ {x y}, toFun x = toFun y → x = y
  map_rel : ∀ R q, A.rel R q ↔ B.rel R (fun i => toFun (q i))

namespace Embedding
variable {L : Language} {α β γ : Type}
variable {A : RelStructure L α} {B : RelStructure L β} {C : RelStructure L γ}

def id (A : RelStructure L α) : Embedding A A where
  toFun := fun x => x
  injective := fun h => h
  map_rel := fun _ _ => Iff.rfl

def comp (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  toFun := fun x => g.toFun (f.toFun x)
  injective := fun h => f.injective (g.injective h)
  map_rel := fun R q => (f.map_rel R q).trans (g.map_rel R (fun i => f.toFun (q i)))

@[simp] theorem comp_apply (g : Embedding B C) (f : Embedding A B) (x : α) :
    (comp g f).toFun x = g.toFun (f.toFun x) := rfl
end Embedding

/-- An enumeration has an initial segment of `Nat` as its range. -/
structure Enumeration (α : Type) where
  index : α → Nat
  injective : ∀ {x y}, index x = index y → x = y
  initial : ∀ x n, n < index x → ∃ y, index y = n

structure EnumeratedStructure (L : Language) where
  Carrier : Type
  structure : RelStructure L Carrier
  enumeration : Enumeration Carrier

namespace EnumeratedStructure
variable {L : Language}
abbrev index (A : EnumeratedStructure L) := A.enumeration.index

def ofFin {n : Nat} (A : RelStructure L (Fin n)) : EnumeratedStructure L where
  Carrier := Fin n
  structure := A
  enumeration := {
    index := Fin.val
    injective := Fin.ext
    initial := fun x m h => ⟨⟨m, Nat.lt_trans h x.isLt⟩, rfl⟩ }
end EnumeratedStructure

structure OrderedEmbedding {L : Language} (A B : EnumeratedStructure L)
    extends Embedding A.structure B.structure where
  increasing : ∀ {x y}, A.index x < A.index y → B.index (toFun x) < B.index (toFun y)

namespace OrderedEmbedding
variable {L : Language} {A B C : EnumeratedStructure L}

def id (A : EnumeratedStructure L) : OrderedEmbedding A A where
  toEmbedding := Embedding.id A.structure
  increasing := fun h => h

def comp (g : OrderedEmbedding B C) (f : OrderedEmbedding A B) : OrderedEmbedding A C where
  toEmbedding := Embedding.comp g.toEmbedding f.toEmbedding
  increasing := fun h => g.increasing (f.increasing h)

theorem increasing_le (f : OrderedEmbedding A B) {x y : A.Carrier}
    (h : A.index x ≤ A.index y) : B.index (f.toFun x) ≤ B.index (f.toFun y) := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · exact Nat.le_of_lt (f.increasing hlt)
  · have hxy : x = y := A.enumeration.injective heq
    subst y
    exact Nat.le_refl _
end OrderedEmbedding

/-- The finite-degree upper-bound predicate uses colours of embeddings. -/
def BigRamseyBound {L : Language} {α κ : Type}
    (A : RelStructure L α) (K : RelStructure L κ) (t : Nat) : Prop :=
  ∀ r : Nat, 0 < r → ∀ χ : Embedding A K → Fin r,
    ∃ f : Embedding K K, ∃ palette : List (Fin r),
      palette.length ≤ t ∧ ∀ g : Embedding A K, χ (Embedding.comp f g) ∈ palette

/-- `none` denotes infinity; `some t` denotes the least finite bound. -/
def IsBigRamseyDegree {L : Language} {α κ : Type}
    (A : RelStructure L α) (K : RelStructure L κ) (d : Option Nat) : Prop :=
  match d with
  | none => ∀ t, ¬ BigRamseyBound A K t
  | some t => BigRamseyBound A K t ∧ ∀ s, BigRamseyBound A K s → t ≤ s

/-- All finite structures in the age have finite embedding degrees. -/
def HasFiniteBigRamseyDegrees {L : Language} {κ : Type} (K : RelStructure L κ) : Prop :=
  ∀ n (A : RelStructure L (Fin n)), Nonempty (Embedding A K) → ∃ t, BigRamseyBound A K t

end AllThoseBigRamsey
