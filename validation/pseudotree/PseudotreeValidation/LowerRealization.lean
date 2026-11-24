import PseudotreeValidation.LowerTransition
import PseudotreeValidation.LowerAssembly

/-!
# Every diary is realized in every sparse self-copy

The finite iteration consumes the geometrically proved transitions. The
result is an actual total ray-preserving strong map, with every designated
coding node inside the specified functional self-copy. There is no assumed
local realization, extension, homogeneity, or desired colouring premise.

Combined with uniqueness of normalized diaries for equal coding images, this
is the unavoidability input for the exact lower bound.
-/

namespace AllThoseBigRamsey.Pseudotree.LowerRealization

open RayEmbeddings
open scoped FirstOrder

/-- Every raw paper diary has a ray-preserving realization whose coding nodes
belong to any prescribed self-copy contained in the literal sparse set. -/
theorem sparse_realization (D : PaperDiary n)
    (f : TernaryModel ↪[language] TernaryModel)
    (hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x)) :
    ∃ g : RayStrongMap, ∀ w ∈ D.codes, DiaryChains.model (g.map w) ∈ Set.range f := by
  obtain ⟨height, T⟩ := D.axioms
  exact finite_realization_of_steps D f T (fun _ hj P => exists_step T hj hsparse P)

/-- The same unconditional realization result on actual embeddings of the
standard finite chain, retaining its precise coding-image interpretation. -/
theorem sparse_chain_realization (D : PaperDiary n)
    (f : TernaryModel ↪[language] TernaryModel)
    (hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x)) :
    ∃ g : RayStrongMap,
      Set.range ((RayMapModel.embedding g).comp D.chainEmbedding) ⊆ Set.range f := by
  obtain ⟨height, T⟩ := D.axioms
  exact chain_realization_of_steps D f T (fun _ hj P => exists_step T hj hsparse P)

/-- In particular, every actual self-embedding of the identified sparse model
contains a ray-preserving realization of every diary. -/
theorem sparse_self_copy_realization (D : PaperDiary n)
    (h : SparseModel ↪[language] SparseModel) :
    ∃ g : RayStrongMap, ∀ w ∈ D.codes,
      DiaryChains.model (g.map w) ∈ Set.range (SparseModel.inclusion.comp h) := by
  let f : TernaryModel ↪[language] TernaryModel :=
    (SparseModel.inclusion.comp h).comp SparseModel.equiv.toEmbedding
  have hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x) := by
    rintro x ⟨t, rfl⟩
    exact (h (SparseModel.equiv t)).property
  obtain ⟨g, hg⟩ := sparse_realization D f hsparse
  refine ⟨g, ?_⟩
  intro w hw
  obtain ⟨t, ht⟩ := hg w hw
  exact ⟨SparseModel.equiv t, ht⟩

end AllThoseBigRamsey.Pseudotree.LowerRealization
