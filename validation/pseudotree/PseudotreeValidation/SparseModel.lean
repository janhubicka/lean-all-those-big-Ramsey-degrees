import AllThoseBigRamsey.Pseudotree.SparseOrder
import PseudotreeValidation.GenericFiniteExtensions

/-!
# The generated sparse set is an actual copy of the binary pseudotree

The carrier is exactly the range of the manuscript's explicit `Sparse.code`
sequence, transported through the proved literal-word/block equivalence.
Its order, meet, density and two inhabited cones are verified from the actual
FIFO construction. The generic finite-extension theorem and mathlib's
back-and-forth then identify this carrier with the concrete Fraïssé limit.
-/

namespace AllThoseBigRamsey.Pseudotree

open FirstOrder
open scoped FirstOrder

@[simp] theorem fromBlocks_inf (s t : TernaryModel) :
    fromBlocks (s ⊓ t) = wordMeet (fromBlocks s) (fromBlocks t) := by
  apply wordEquiv.injective
  change toBlocks (fromBlocks (s ⊓ t)) =
    toBlocks (wordMeet (fromBlocks s) (fromBlocks t))
  simp

/-- The actual generated sparse set, in the standard model coordinates. -/
abbrev SparseModel := {s : TernaryModel // Sparse.InSparse (fromBlocks s)}

namespace SparseModel

instance : SemilatticeInf SparseModel where
  inf s t := ⟨s.val ⊓ t.val, by
    rw [fromBlocks_inf]
    exact Sparse.sparse_meet_closed s.property t.property⟩
  inf_le_left s t := by
    change s.val ⊓ t.val ≤ s.val
    exact inf_le_left
  inf_le_right s t := by
    change s.val ⊓ t.val ≤ t.val
    exact inf_le_right
  le_inf s t u hst hsu := by
    change s.val ≤ t.val ⊓ u.val
    exact le_inf hst hsu

@[simp] theorem val_inf (s t : SparseModel) : (s ⊓ t).val = s.val ⊓ t.val := rfl

/-- Literal words for the actual sparse nodes. -/
def word (s : SparseModel) : Sparse.Word := fromBlocks s.val

/-- The word belongs to the actual generated range, not an abstract sparse set. -/
theorem word_mem (s : SparseModel) : Sparse.InSparse (word s) := s.property

/-- Include any word proved to be generated. -/
def ofWord (w : Sparse.Word) (hw : Sparse.InSparse w) : SparseModel :=
  ⟨toBlocks w, by simpa using hw⟩

@[simp] theorem word_ofWord (w : Sparse.Word) (hw : Sparse.InSparse w) :
    word (ofWord w hw) = w := fromBlocks_toBlocks w

@[simp] theorem ofWord_word (s : SparseModel) : ofWord (word s) (word_mem s) = s := by
  apply Subtype.ext
  exact toBlocks_fromBlocks s.val

@[simp] theorem word_inf (s t : SparseModel) : word (s ⊓ t) = wordMeet (word s) (word t) :=
  fromBlocks_inf s.val t.val

@[simp] theorem word_le_iff (s t : SparseModel) : wordBelow (word s) (word t) ↔ s ≤ t := by
  change wordBelow (fromBlocks s.val) (fromBlocks t.val) ↔ s.val ≤ t.val
  simpa only [word, toBlocks_fromBlocks] using
    wordBelow_iff_toBlocks_le (fromBlocks s.val) (fromBlocks t.val)

/-- The coding sequence is a surjection onto the carrier. -/
def code (n : Nat) : SparseModel :=
  ofWord (Sparse.code n) ((Sparse.inSparse_iff_code _).mpr ⟨n, rfl⟩)

theorem code_surjective : Function.Surjective code := by
  intro s
  obtain ⟨n, hn⟩ := (Sparse.inSparse_iff_code (word s)).mp (word_mem s)
  refine ⟨n, ?_⟩
  apply Subtype.ext
  change toBlocks (Sparse.code n) = s.val
  rw [← hn]
  exact toBlocks_fromBlocks s.val

instance : Nonempty SparseModel := ⟨code 0⟩

instance : NoMinOrder SparseModel where
  exists_lt s := by
    obtain ⟨u, hu, hus, hsu⟩ := (Sparse.sparse_no_endpoints (word_mem s)).1
    let v := ofWord u hu
    have hvs : v ≤ s := (word_le_iff v s).mp (by simpa [v] using hus)
    have hsv : ¬s ≤ v := by
      intro h
      exact hsu (by simpa [v] using (word_le_iff s v).mpr h)
    exact ⟨v, lt_iff_le_not_ge.mpr ⟨hvs, hsv⟩⟩

instance : NoMaxOrder SparseModel where
  exists_gt s := by
    obtain ⟨u, hu, hsu, hus⟩ := (Sparse.sparse_no_endpoints (word_mem s)).2
    let v := ofWord u hu
    have hsv : s ≤ v := (word_le_iff s v).mp (by simpa [v] using hsu)
    have hvs : ¬v ≤ s := by
      intro h
      exact hus (by simpa [v] using (word_le_iff v s).mpr h)
    exact ⟨v, lt_iff_le_not_ge.mpr ⟨hsv, hvs⟩⟩

instance : DenselyOrdered SparseModel where
  dense s t hst := by
    have hst' : wordBelow (word s) (word t) := (word_le_iff s t).mpr hst.le
    have hts' : ¬wordBelow (word t) (word s) := by
      intro h
      exact (not_le_of_gt hst) ((word_le_iff t s).mp h)
    obtain ⟨u, hu, hsu, hus, hut, htu⟩ :=
      Sparse.sparse_dense (word_mem s) (word_mem t) hst' hts'
    let v := ofWord u hu
    refine ⟨v, lt_iff_le_not_ge.mpr ⟨?_, ?_⟩, lt_iff_le_not_ge.mpr ⟨?_, ?_⟩⟩
    · exact (word_le_iff s v).mp (by simpa [v] using hsu)
    · intro h
      exact hus (by simpa [v] using (word_le_iff v s).mpr h)
    · exact (word_le_iff v t).mp (by simpa [v] using hut)
    · intro h
      exact htu (by simpa [v] using (word_le_iff t v).mpr h)

/-- The order inherited from the model has linearly ordered predecessor sets. -/
theorem predecessors_comparable {x y z : SparseModel} (hx : x ≤ z) (hy : y ≤ z) :
    x ≤ y ∨ y ≤ x := RayTree.le_or_ge_of_le_common hx hy

/-- At most two upper cones is inherited from the actual ambient model. -/
theorem binaryBranching : BinaryBranching SparseModel := by
  intro s x y z hx hy hz
  exact RayTree.binaryBranching s.val x.val y.val z.val hx hy hz

/-- The first and second FIFO children inhabit both upper cones. -/
theorem fork (s : SparseModel) : ∃ x y : SparseModel, s < x ∧ s < y ∧ x ⊓ y = s := by
  obtain ⟨u, v, hu, hv, hsu, hus, hsv, hvs, huv⟩ := Sparse.sparse_fork (word_mem s)
  let x := ofWord u hu
  let y := ofWord v hv
  refine ⟨x, y, lt_iff_le_not_ge.mpr ⟨?_, ?_⟩,
    lt_iff_le_not_ge.mpr ⟨?_, ?_⟩, ?_⟩
  · exact (word_le_iff s x).mp (by simpa [x] using hsu)
  · intro h
    exact hus (by simpa [x] using (word_le_iff x s).mpr h)
  · exact (word_le_iff s y).mp (by simpa [y] using hsv)
  · intro h
    exact hvs (by simpa [y] using (word_le_iff y s).mpr h)
  · apply Subtype.ext
    change toBlocks u ⊓ toBlocks v = s.val
    rw [← toBlocks_wordMeet, huv]
    exact toBlocks_fromBlocks s.val

/-- Any occupied cone has a sparse point in the other cone. -/
theorem exists_opposite_cone (s r : SparseModel) (hr : s < r) :
    ∃ v, s < v ∧ v ⊓ r = s := by
  obtain ⟨x, y, hx, hy, hxy⟩ := fork s
  by_cases hxr : s < r ⊓ x
  · refine ⟨y, hy, ?_⟩
    exact inf_eq_of_opposite_cone predecessors_comparable hy.le hr.le
      (by simpa only [inf_comm] using hxy) hxr
  · refine ⟨x, hx, ?_⟩
    have hle : s ≤ r ⊓ x := le_inf hr.le hx.le
    have heq : r ⊓ x = s := by
      rcases lt_or_eq_of_le hle with hlt | heq
      · exact False.elim (hxr hlt)
      · exact heq.symm
    simpa only [inf_comm] using heq

/-- Inclusion of the actual sparse carrier preserves the function and relation
symbols of the manuscript's language. -/
def inclusion : SparseModel ↪[language] TernaryModel :=
  embeddingOfInfMap Subtype.val Subtype.val_injective (fun _ _ => rfl)

/-- This finite-extension theorem has only the source age hypotheses. Every
target property was proved from the literal sparse construction. -/
theorem extend_finite {M : Type u} [SemilatticeInf M] [language.Structure M]
    [MeetsInterpreted M] [Finite M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbinary : BinaryBranching M)
    (S : language.Substructure M) (f : S ↪[language] SparseModel) :
    ∃ g : M ↪[language] SparseModel, ∀ a : S, g a = f a :=
  DenseMeetTree.extend_finite predecessors_comparable exists_opposite_cone htree hbinary S f

/-- The actual sparse construction is ultrahomogeneous. -/
theorem isUltrahomogeneous : language.IsUltrahomogeneous SparseModel :=
  DenseMeetTree.isUltrahomogeneous predecessors_comparable exists_opposite_cone binaryBranching

/-- The actual sparse construction has exactly the manuscript's finite age. -/
theorem age_eq_finiteBinaryClass : language.age SparseModel = finiteBinaryClass :=
  DenseMeetTree.age_eq_finiteBinaryClass predecessors_comparable exists_opposite_cone binaryBranching

/-- The sparse-copy assertion in the paper, proved as a native Fraïssé limit. -/
theorem isFraisseLimit : language.IsFraisseLimit finiteBinaryClass SparseModel :=
  DenseMeetTree.isFraisseLimit predecessors_comparable exists_opposite_cone binaryBranching

/-- The literal generated sparse set is isomorphic to the full concrete model. -/
theorem nonempty_equiv : Nonempty (TernaryModel ≃[language] SparseModel) :=
  ternaryModel_unique isFraisseLimit

/-- Choose the isomorphism supplied by back-and-forth. -/
noncomputable def equiv : TernaryModel ≃[language] SparseModel :=
  Classical.choice nonempty_equiv

/-- An actual functional self-embedding whose range is exactly the generated
sparse set. -/
noncomputable def selfEmbedding : TernaryModel ↪[language] TernaryModel :=
  inclusion.comp equiv.toEmbedding

/-- The sparse-copy theorem specifies the precise range of the constructed
self-embedding; it does not merely assert existence of some sparse copy. -/
theorem selfEmbedding_range :
    Set.range selfEmbedding = {s | Sparse.InSparse (fromBlocks s)} := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact (equiv t).property
  · intro hs
    obtain ⟨t, ht⟩ := equiv.surjective (⟨s, hs⟩ : SparseModel)
    exact ⟨t, congrArg Subtype.val ht⟩

end SparseModel
end AllThoseBigRamsey.Pseudotree
