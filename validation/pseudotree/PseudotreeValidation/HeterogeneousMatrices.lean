import PseudotreeValidation.DenseMatrices

/-!
# Dense matrices for genuinely different ambient trees

Binary rays are not strong subtrees of a ternary ambient tree. To apply
the common-ambient library API honestly, put the original factors in the
proved common-root wedge and then transport the matrix back. This module
uses the library's existing wedge construction, rather than introducing
another tree representation or assuming equal branching.
-/

namespace AllThoseBigRamsey.Pseudotree

open Milliken Milliken.GeneralTree

/-- Finite-colour dense-level-matrix HL for a positive finite family of
independent pruned, locally finite rooted trees, with precisely the
finite-demand and fixed-colour quantifiers used in the note. -/
theorem heterogeneousFiniteDemandDenseMatrices
    (d : ℕ) (hd : 0 < d) (T : Fin d → AmbientTree) (n : ℕ)
    (colour : (∀ i, T i) → Fin (n + 1)) :
    ∃ base : (∀ i, T i), ∃ a : Fin (n + 1),
      ∀ F : (i : Fin d) → Finset (T i),
        (∀ i, ∀ x ∈ F i, base i ≤ x) →
        ∀ m : ℕ, ∃ l : ℕ, m ≤ l ∧
          ∃ X : (i : Fin d) → Set (T i),
            (∀ i, ∀ x ∈ X i, (T i).level x = l) ∧
            (∀ i, ∀ x ∈ F i, ∃ y ∈ X i, x ≤ y) ∧
            ∀ x : (∀ i, T i), (∀ i, x i ∈ X i) → colour x = a := by
  classical
  let U : AmbientTree := WedgeNode.ambientTree T hd
  let : DecidableEq (WedgeNode T) := Classical.decEq _
  let P : Fin d → StrongSubtree U := WedgeNode.componentStrong T hd
  have hinj (i : Fin d) : Function.Injective (WedgeNode.embed T i) := by
    intro x y hxy
    exact le_antisymm
      ((WedgeNode.embed_le_embed_iff T i x y).mp hxy.le)
      ((WedgeNode.embed_le_embed_iff T i y x).mp hxy.symm.le)
  let decode (i : Fin d) : U → T i := Function.invFun (WedgeNode.embed T i)
  have hdecode (i : Fin d) (x : T i) : decode i (WedgeNode.embed T i x) = x :=
    Function.leftInverse_invFun (hinj i) x
  let colour' : (Fin d → U) → Fin (n + 1) := fun x => colour (fun i => decode i (x i))
  obtain ⟨k, base, a, hall⟩ := finiteDemandDenseMatrices U d hd P n colour'
  let base' : (i : Fin d) → T i := fun i => decode i (base.1 i)
  have hbase (i : Fin d) : WedgeNode.embed T i (base' i) = base.1 i := by
    obtain ⟨x, hx⟩ := WedgeNode.exists_embed_of_mem_componentStrong
      T hd i (base.1 i) (base.2 i).1
    dsimp [base']
    rw [← hx, hdecode]
  refine ⟨base', a, ?_⟩
  intro F hF m
  let F' : Fin d → Finset U := fun i => (F i).image (WedgeNode.embed T i)
  have hF' : ∀ i, ∀ x ∈ F' i, x ∈ (P i).carrier ∧ base.1 i ≤ x := by
    intro i x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    constructor
    · exact WedgeNode.embed_mem_componentStrong T hd i y
    · rw [← hbase i]
      exact (WedgeNode.embed_le_embed_iff T i (base' i) y).mpr (hF i y hy)
  obtain ⟨l, hml, M, hOn, hDom, hMono⟩ := hall F' hF' m
  let X : (i : Fin d) → Set (T i) := fun i => {x | WedgeNode.embed T i x ∈ M.coord i}
  refine ⟨l, hml, X, ?_, ?_, ?_⟩
  · intro i x hx
    have hz := hOn i (WedgeNode.embed T i x) hx
    obtain ⟨y, hy, heq⟩ :=
      (WedgeNode.mem_componentStrong_sourceLevel_iff T hd i l
        (WedgeNode.embed T i x)).mp hz
    simpa only [hinj i heq] using hy
  · intro i x hx
    have hx' : WedgeNode.embed T i x ∈ F' i := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hxz⟩ := hDom i (WedgeNode.embed T i x) hx'
    obtain ⟨y, hy⟩ := WedgeNode.exists_embed_of_mem_componentStrong
      T hd i z (M.coord_sub i hz)
    rw [← hy] at hz hxz
    exact ⟨y, hz, (WedgeNode.embed_le_embed_iff T i x y).mp hxz⟩
  · intro x hx
    have h := hMono (fun i => WedgeNode.embed T i (x i)) hx
    change colour (fun i => decode i (WedgeNode.embed T i (x i))) = a at h
    simpa only [hdecode] using h

end AllThoseBigRamsey.Pseudotree
