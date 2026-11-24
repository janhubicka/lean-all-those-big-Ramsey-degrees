import PseudotreeValidation.RepoBridge
import PseudotreeValidation.LowerRealization

/-! Final palette and degree deductions from the geometric diary theorems.

The two normalization inputs are explicit in this assembly module. The
unconditional paper endpoint must instantiate them with the proved sparse
extraction and recovery theorems; no normalization axiom is introduced here.
-/

namespace AllThoseBigRamsey.Pseudotree.DegreeAssembly

open scoped FirstOrder
open RayEmbeddings

/-- A functional embedding with image inside another embedding factors
through it. Mathlib's actual domain/range isomorphism supplies the factor. -/
theorem factor_embedding {A M N : Type} [language.Structure A]
    [language.Structure M] [language.Structure N]
    (f : M ↪[language] N) (e : A ↪[language] N) (hrange : Set.range e ⊆ Set.range f) :
    ∃ g : A ↪[language] M, f.comp g = e := by
  let h : A ↪[language] f.toHom.range := e.codRestrict f.toHom.range
    (fun a => hrange ⟨a, rfl⟩)
  let g : A ↪[language] M := f.equivRange.symm.toEmbedding.comp h
  refine ⟨g, ?_⟩
  apply FirstOrder.Language.Embedding.ext
  intro a
  change f (f.equivRange.symm (h a)) = e a
  calc
    f (f.equivRange.symm (h a)) =
        (f.equivRange (f.equivRange.symm (h a))).val := rfl
    _ = (h a).val := congrArg Subtype.val (f.equivRange.apply_symm_apply (h a))
    _ = e a := rfl

variable {n : Nat}

/-- Sparse representation is the only additional input needed after the
independently proved simultaneous finite-tree canonization theorem. -/
theorem chain_bound_of_representations
    (represent : ∀ e : Fin n ↪[language] TernaryModel,
      ∃ D : PaperDiary n, ∃ d : RayMilliken.Embedding D.shape,
        D.embeddedChain d = SparseModel.selfEmbedding.comp e) :
    Incomparables.FunctionalBigRamseyBound (Fin n) (diaryCount true n 1) := by
  classical
  intro r hr colour
  cases r with
  | zero => omega
  | succ colours =>
    obtain ⟨g, c, hc⟩ := DiaryCanonization.simultaneous colour
    let palette := (Finset.univ : Finset (PaperDiary n)).image c
    refine ⟨(RayMapModel.embedding g).comp SparseModel.selfEmbedding, palette, ?_, ?_⟩
    · calc
        palette.card ≤ (Finset.univ : Finset (PaperDiary n)).card := Finset.card_image_le
        _ = diaryCount true n 1 := by rw [Finset.card_univ, paperDiary_card]
    · intro e
      obtain ⟨D, d, hd⟩ := represent e
      have h := hc D d
      rw [hd] at h
      change colour ((RayMapModel.embedding g).comp (SparseModel.selfEmbedding.comp e)) ∈ palette
      rw [h]
      exact Finset.mem_image.mpr ⟨D, Finset.mem_univ _, rfl⟩

/-- Existence and uniqueness of normalized representations, together with
the independently proved realization theorem, give the exact chain degree
in the repository's original API. -/
theorem exact_degree_of_representations (hn : 0 < n)
    (represent : ∀ e : Fin n ↪[language] TernaryModel,
      ∃ D : PaperDiary n, ∃ d : RayMilliken.Embedding D.shape,
        D.embeddedChain d = SparseModel.selfEmbedding.comp e)
    (unique : ∀ (D E : PaperDiary n)
      (d : RayMilliken.Embedding D.shape) (e : RayMilliken.Embedding E.shape),
      D.embeddedChain d = E.embeddedChain e → D = E) :
    IsBigRamseyDegree (RepoBridge.model (Fin n)) (RepoBridge.model TernaryModel)
      (some (diaryCount true n 1)) := by
  classical
  constructor
  · exact (RepoBridge.bound_iff (Fin n) _).mpr (chain_bound_of_representations represent)
  · intro bound hbound
    have functionalBound := (RepoBridge.bound_iff (Fin n) bound).mp hbound
    let typeOf (e : Fin n ↪[language] TernaryModel) : PaperDiary n := (represent e).choose
    have type_rep (e : Fin n ↪[language] TernaryModel) :
        ∃ d : RayMilliken.Embedding (typeOf e).shape,
          (typeOf e).embeddedChain d = SparseModel.selfEmbedding.comp e :=
      (represent e).choose_spec
    have unavoidable (f : TernaryModel ↪[language] TernaryModel) (D : PaperDiary n) :
        ∃ e : Fin n ↪[language] TernaryModel, typeOf (f.comp e) = D := by
      let F := SparseModel.selfEmbedding.comp f
      have hsparse : ∀ x ∈ Set.range F, Sparse.InSparse (fromBlocks x) := by
        rintro x ⟨t, rfl⟩
        have hmem : SparseModel.selfEmbedding (f t) ∈ Set.range SparseModel.selfEmbedding :=
          ⟨f t, rfl⟩
        rw [SparseModel.selfEmbedding_range] at hmem
        exact hmem
      obtain ⟨g, hg⟩ := LowerRealization.sparse_chain_realization D F hsparse
      obtain ⟨e, he⟩ := factor_embedding F ((RayMapModel.embedding g).comp D.chainEmbedding) hg
      obtain ⟨d, hd⟩ := type_rep (f.comp e)
      refine ⟨e, unique (typeOf (f.comp e)) D d (RayMilliken.Embedding.ofTotal D.shape g) ?_⟩
      rw [PaperDiary.embeddedChain_ofTotal, hd]
      exact he
    have hnonempty : Nonempty (PaperDiary n) := by
      cases n with
      | zero => omega
      | succ k => exact ⟨(longestDiary k).toPaper⟩
    let r := Fintype.card (PaperDiary n)
    have hr : 0 < r := Fintype.card_pos_iff.mpr hnonempty
    let encode := Fintype.equivFin (PaperDiary n)
    let colour : (Fin n ↪[language] TernaryModel) → Fin r := fun e => encode (typeOf e)
    obtain ⟨f, palette, hcard, hcover⟩ := functionalBound r hr colour
    have hfull : (Finset.univ : Finset (Fin r)) ⊆ palette := by
      intro i _hi
      obtain ⟨e, he⟩ := unavoidable f (encode.symm i)
      have h := hcover e
      simpa only [colour, he, Equiv.apply_symm_apply] using h
    have hcount : r ≤ palette.card := by
      simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hfull
    rw [← paperDiary_card n]
    exact hcount.trans hcard

end AllThoseBigRamsey.Pseudotree.DegreeAssembly
