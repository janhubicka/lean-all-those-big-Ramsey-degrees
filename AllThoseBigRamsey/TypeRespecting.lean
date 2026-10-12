import AllThoseBigRamsey.FullTypes

/-! Type-respecting embeddings of finite or countably infinite enumerated structures. -/
namespace AllThoseBigRamsey
variable {L : Language}

abbrev Prefix (A : EnumeratedStructure L) (v : A.Carrier) :=
  { x : A.Carrier // A.index x < A.index v }

def TailTuple (A : EnumeratedStructure L) (v : A.Carrier)
    {k : Nat} (s : Fin k → A.Carrier) : Prop :=
  (∀ i, A.index v ≤ A.index (s i)) ∧
  (∀ i j, i.val < j.val → A.index (s i) < A.index (s j))

def SameType (A : EnumeratedStructure L) (v : A.Carrier)
    {k : Nat} (s t : Fin k → A.Carrier) : Prop :=
  SameFullType A.relStructure (fun x : Prefix A v => x.val) s t

/-- All tuple sizes at most `n` are included; no padding assumption is made. -/
def NTypeRespecting {A B : EnumeratedStructure L} (n : Nat)
    (f : OrderedEmbedding A B) : Prop :=
  ∀ v k, k ≤ n → ∀ s t : Fin k → A.Carrier,
    TailTuple A v s → TailTuple A v t → SameType A v s t →
      SameType B (f.toFun v) (fun i => f.toFun (s i)) (fun i => f.toFun (t i))

namespace OrderedEmbedding
variable {A B : EnumeratedStructure L}
theorem map_tail (f : OrderedEmbedding A B) {v : A.Carrier}
    {k : Nat} {s : Fin k → A.Carrier} (hs : TailTuple A v s) :
    TailTuple B (f.toFun v) (fun i => f.toFun (s i)) := by
  exact ⟨fun i => f.increasing_le (hs.1 i), fun i j h => f.increasing (hs.2 i j h)⟩
end OrderedEmbedding

namespace NTypeRespecting
variable {A B C : EnumeratedStructure L} {n m : Nat}

theorem id (A : EnumeratedStructure L) (n : Nat) :
    NTypeRespecting n (OrderedEmbedding.id A) := by
  intro v k hk s t hs ht hst
  exact hst

theorem comp {f : OrderedEmbedding A B} {g : OrderedEmbedding B C}
    (hf : NTypeRespecting n f) (hg : NTypeRespecting n g) :
    NTypeRespecting n (OrderedEmbedding.comp g f) := by
  intro v k hk s t hs ht hst
  exact hg (f.toFun v) k hk
    (fun i => f.toFun (s i)) (fun i => f.toFun (t i))
    (f.map_tail hs) (f.map_tail ht) (hf v k hk s t hs ht hst)

theorem mono {f : OrderedEmbedding A B} (hf : NTypeRespecting n f) (hmn : m ≤ n) :
    NTypeRespecting m f := by
  intro v k hk s t hs ht hst
  exact hf v k (Nat.le_trans hk hmn) s t hs ht hst
end NTypeRespecting

/-- A maximum positive arity, with value one for the empty language. -/
structure MaximumArity (L : Language) where
  value : Nat
  positive : 0 < value
  bound : ∀ R, L.arity R ≤ value
  sharp : value = 1 ∨ ∃ R, L.arity R = value

/-- The unqualified convention uses the actual maximum relation arity minus one. -/
def TypeRespecting {A B : EnumeratedStructure L} (r : MaximumArity L)
    (f : OrderedEmbedding A B) : Prop := NTypeRespecting (r.value - 1) f

end AllThoseBigRamsey
