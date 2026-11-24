import PseudotreeValidation.LowerTurn
import PseudotreeValidation.DiarySoundness

/-! Finite frontier data for the constructive lower-bound realization. -/

namespace AllThoseBigRamsey.Pseudotree.LowerRealization

open LowerGeometry
open scoped FirstOrder

abbrev Level (D : PaperDiary n) (j : Nat) :=
  {u : DiaryWord // u ∈ D.nodes ∧ u.length = j}

instance (D : PaperDiary n) (j : Nat) : Finite (Level D j) :=
  Finite.of_injective (fun u : Level D j => (⟨u.val, u.property.1⟩ : D.nodes))
    (fun _ _ h => Subtype.ext (congrArg (fun v : D.nodes => v.val) h))

noncomputable instance (D : PaperDiary n) (j : Nat) : Fintype (Level D j) := Fintype.ofFinite _

def childNode (u : Level D j) (a : Fin 3) (ha : child u.val a ∈ D.nodes) :
    Level D (j + 1) := ⟨child u.val a, ha, by simp [child, u.property.2]⟩

/-- Every active branch carries a genuine single-ray rational suborder of the
specified self-copy, in a distinct lexicographically ordered prefix cylinder. -/
structure Layer (D : PaperDiary n)
    (f : TernaryModel ↪[language] TernaryModel) (j : Nat) where
  bound : Nat
  copies : Level D j → RayCopy
  prefixes : Level D j → List TernaryLetter
  prefix_length : ∀ u, (prefixes u).length = bound
  common_prefix : ∀ u q, prefixes u <+: fromBlocks (copies u q)
  root_short : ∀ u, (rayRoot (copies u).stem).length < bound
  inside : ∀ u, Set.range (copies u).embedding ⊆ Set.range f
  ordered : ∀ u v, u.val < v.val → Sparse.lexLess (prefixes u) (prefixes v) = true

/-- A genuine one-level transition. The old level is realized at `level`,
then each new candidate cylinder starts after the prescribed first letter.
Only these local equations are needed by the finite-map assembly. -/
structure Step {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} (P : Layer D f j) where
  next : Layer D f (j + 1)
  level : Nat
  lower : P.bound ≤ level
  upper : level < next.bound
  roots : Level D j → List TernaryLetter
  root_length : ∀ u, (roots u).length = level
  root_binary : ∀ u, ∃ b : List TernaryLetter,
    .one ∉ b ∧ roots u = P.prefixes u ++ b
  coding : ∀ u, u.val ∈ D.codes → toBlocks (roots u) ∈ Set.range f
  edge : ∀ u a (ha : child u.val a ∈ D.nodes),
    ∃ b : List TernaryLetter,
      next.prefixes (childNode u a ha) = roots u ++ RayMapModel.toLetter a :: b ∧
      (a ≠ 1 → .one ∉ b)

/-- The root candidate layer is obtained inside an actual source interval and
then refined past its ray root. -/
theorem initial (D : PaperDiary n) (f : TernaryModel ↪[language] TernaryModel) :
    Nonempty (Layer D f 0) := by
  let y : TernaryModel := .point ⟨[]⟩
  obtain ⟨w, hyw⟩ := exists_gt y
  obtain ⟨Q, hQ⟩ := interval_rayCopy (embeddingOrderEmbedding f) hyw
  obtain ⟨R, hstem, hsub, p, hplen, hp⟩ := Q.common_prefix
    ((rayRoot Q.stem).length + 1) (by omega)
  refine ⟨{
    bound := (rayRoot Q.stem).length + 1
    copies := fun _ => R
    prefixes := fun _ => p
    prefix_length := fun _ => hplen
    common_prefix := fun _ => hp
    root_short := fun _ => by rw [hstem]; omega
    inside := ?_
    ordered := ?_
  }⟩
  · intro u x hx
    obtain ⟨q, hq⟩ := hsub hx
    obtain ⟨z, _, _, hz⟩ := hQ q
    exact ⟨z, (hz.symm.trans hq)⟩
  · intro u v huv
    have hu : u.val = [] := List.length_eq_zero_iff.mp u.property.2
    have hv : v.val = [] := List.length_eq_zero_iff.mp v.property.2
    rw [hu, hv] at huv
    exact False.elim ((lt_irrefl _) huv)

end AllThoseBigRamsey.Pseudotree.LowerRealization
