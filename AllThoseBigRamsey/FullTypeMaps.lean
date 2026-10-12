import AllThoseBigRamsey.TypeRespecting
import AllThoseBigRamsey.BinaryFullTypes

/-! Concrete coherent maps on full types, retaining the ordered base embedding.
These are structural maps; the separate continuation predicate is not implicit. -/
namespace AllThoseBigRamsey

structure FullTypeMap {L : Language} (n : Nat) (A B : EnumeratedStructure L) where
  base : OrderedEmbedding A B
  onType : (k : Nat) → k ≤ n → FullType A.relStructure k → FullType B.relStructure k
  extension : ∀ k hk p R t,
    p.diagram.rel R t ↔
      (onType k hk p).diagram.rel R (fun i => Sum.map base.toFun (fun j => j) (t i))
  coherent : ∀ j k (hj : j ≤ n) (hk : k ≤ n)
    (p : FullType A.relStructure k) (ρ : Fin j → Fin k),
    (∀ u v, u.val < v.val → (ρ u).val < (ρ v).val) →
    onType j hj (p.restrict ρ) = (onType k hk p).restrict ρ

namespace FullTypeMap
variable {L : Language} {n : Nat} {A B C : EnumeratedStructure L}

def id (A : EnumeratedStructure L) (n : Nat) : FullTypeMap n A A where
  base := OrderedEmbedding.id A
  onType := fun _ _ p => p
  extension := by
    intro k hk p R t
    have h : (fun i => Sum.map (fun x : A.Carrier => x) (fun j : Fin k => j) (t i)) = t := by
      funext i
      cases t i <;> rfl
    simpa only [h] using (Iff.rfl : p.diagram.rel R t ↔ p.diagram.rel R t)
  coherent := fun _ _ _ _ _ _ _ => rfl

def comp (G : FullTypeMap n B C) (F : FullTypeMap n A B) : FullTypeMap n A C where
  base := OrderedEmbedding.comp G.base F.base
  onType := fun k hk p => G.onType k hk (F.onType k hk p)
  extension := by
    intro k hk p R t
    have hf := F.extension k hk p R t
    have hg := G.extension k hk (F.onType k hk p) R
      (fun i => Sum.map F.base.toFun (fun j => j) (t i))
    have hnames :
        (fun i => Sum.map G.base.toFun (fun j : Fin k => j)
          (Sum.map F.base.toFun (fun j => j) (t i))) =
        (fun i => Sum.map (fun x => G.base.toFun (F.base.toFun x)) (fun j => j) (t i)) := by
      funext i
      cases t i <;> rfl
    exact hf.trans (by simpa only [hnames] using hg)
  coherent := by
    intro j k hj hk p ρ hρ
    rw [F.coherent j k hj hk p ρ hρ]
    exact G.coherent j k hj hk (F.onType k hk p) ρ hρ

/-- Input types can be recovered from their images, even outside the class. -/
theorem onType_injective (F : FullTypeMap n A B) {k : Nat} (hk : k ≤ n)
    {p q : FullType A.relStructure k} (h : F.onType k hk p = F.onType k hk q) : p = q := by
  apply FullType.ext_diagram
  intro R t
  have hp := F.extension k hk p R t
  have hq := F.extension k hk q R t
  rw [h] at hp
  exact hp.trans hq.symm

/-- Every coherent map fixes the entire diagram internal to the future tuple. -/
theorem future_preserved (F : FullTypeMap n A B) {k : Nat} (hk : k ≤ n)
    (p : FullType A.relStructure k) :
    (F.onType k hk p).futureDiagram = p.futureDiagram := by
  apply RelStructure.ext_rel
  intro R t
  exact (F.extension k hk p R (fun i => Sum.inr (t i))).symm

/-- For a binary language, no independent higher-type component is possible.
The future diagram is preserved by `extension`, not inferred from singletons. -/
theorem binary_determined_by_one (binary : ∀ R, L.arity R ≤ 2)
    (F G : FullTypeMap n A B) (h1 : 1 ≤ n)
    (one : ∀ p, F.onType 1 h1 p = G.onType 1 h1 p)
    {k : Nat} (hk : k ≤ n) (p : FullType A.relStructure k) :
    F.onType k hk p = G.onType k hk p := by
  apply FullType.binary_ext binary
  · intro j
    have hj : ∀ u v : Fin 1, u.val < v.val →
        j.val < j.val := by
      intro u v huv
      have hu := u.isLt
      have hv := v.isLt
      omega
    calc
      (F.onType k hk p).restrict (fun _ : Fin 1 => j) =
          F.onType 1 h1 (p.restrict (fun _ : Fin 1 => j)) :=
        (F.coherent 1 k h1 hk p _ hj).symm
      _ = G.onType 1 h1 (p.restrict (fun _ : Fin 1 => j)) := one _
      _ = (G.onType k hk p).restrict (fun _ : Fin 1 => j) :=
        G.coherent 1 k h1 hk p _ hj
  · exact (F.future_preserved hk p).trans (G.future_preserved hk p).symm
end FullTypeMap
end AllThoseBigRamsey
