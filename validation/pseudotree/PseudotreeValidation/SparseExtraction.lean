import PseudotreeValidation.SparseNormalization
import PseudotreeValidation.DiaryCanonization
import PseudotreeValidation.Indivisibility
import PseudotreeValidation.SparseModel

/-! Diary extraction for actual functional embeddings of finite chains. -/

namespace AllThoseBigRamsey.Pseudotree.SparseExtraction

open RayEmbeddings RayMapModel
open scoped FirstOrder

def word (x : TernaryModel) : DiaryWord := (fromBlocks x).map toFin

@[simp] theorem model_word (x : TernaryModel) : DiaryChains.model (word x) = x := by
  simp [DiaryChains.model, word, List.map_map, Function.comp_def]

@[simp] theorem word_model (w : DiaryWord) : word (DiaryChains.model w) = w := by
  simp [DiaryChains.model, word, List.map_map, Function.comp_def]

theorem word_injective : Function.Injective word := by
  intro x y heq
  simpa only [model_word] using congrArg DiaryChains.model heq

noncomputable def chainWords {n : Nat} (e : Fin n ↪[language] TernaryModel) : Finset DiaryWord := by
  classical
  exact Finset.univ.image (fun i => word (e i))

theorem chainWords_card {n : Nat} (e : Fin n ↪[language] TernaryModel) :
    (chainWords e).card = n := by
  classical
  have hi : Function.Injective (fun i => word (e i)) := by
    intro i j h
    exact e.injective (word_injective h)
  rw [chainWords, Finset.card_image_of_injective _ hi]
  simp

theorem mem_chainWords {n : Nat} (e : Fin n ↪[language] TernaryModel) (w : DiaryWord) :
    w ∈ chainWords e ↔ ∃ i, word (e i) = w := by
  classical
  simp [chainWords]

/-- Every actual finite chain in the generated sparse copy has a literal
normalized diary and a ray-preserving finite embedding, with exact equality
of functional chain embeddings (not merely an abstract isomorphism). -/
theorem representation {n : Nat} (hn : 0 < n) (e : Fin n ↪[language] TernaryModel)
    (hsparse : ∀ x ∈ Set.range e, Sparse.InSparse (fromBlocks x)) :
    ∃ D : PaperDiary n, ∃ d : RayMilliken.Embedding D.shape, D.embeddedChain d = e := by
  classical
  let C := chainWords e
  let last : Fin n := ⟨n-1, by omega⟩
  let v := word (e last)
  have hv : v ∈ C := (mem_chainWords e v).mpr ⟨last, rfl⟩
  have hC : ∀ w ∈ C, SparseNormalization.Point w := by
    intro w hw
    obtain ⟨i, rfl⟩ := (mem_chainWords e w).mp hw
    have h := hsparse (e i) ⟨i, rfl⟩
    simpa [SparseNormalization.Point, word, List.map_map, Function.comp_def] using h
  have hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v := by
    intro w hw
    obtain ⟨i, rfl⟩ := (mem_chainWords e w).mp hw
    change DiaryChains.model (word (e i)) ≤ DiaryChains.model (word (e last))
    rw [model_word, model_word]
    exact (embeddingOrderEmbedding e).monotone (by change i.val ≤ n-1; omega)
  have hex : ∃ D : PaperDiary C.card, ∃ g : RayStrongMap, D.codes.image g.map = C :=
    ⟨SparseNormalization.normalize hC hv hmax, SparseNormalization.extraction hC hv hmax⟩
  have hcard : C.card = n := chainWords_card e
  rw [hcard] at hex
  obtain ⟨D, g, himage⟩ := hex
  let d := RayMilliken.Embedding.ofTotal D.shape g
  refine ⟨D, d, chain_embedding_eq_of_range_eq _ _ ?_⟩
  rw [D.embeddedChain_range d]
  ext x
  constructor
  · rintro ⟨w, hw, hx⟩
    have hword : g.map w ∈ C := by
      rw [← himage]
      exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
    obtain ⟨i, hi⟩ := (mem_chainWords e (g.map w)).mp hword
    refine ⟨i, ?_⟩
    have hmodel : DiaryChains.model (g.map w) = x := hx
    rw [← hi, model_word] at hmodel
    exact hmodel
  · rintro ⟨i, rfl⟩
    have hword : word (e i) ∈ C := (mem_chainWords e _).mpr ⟨i, rfl⟩
    rw [← himage] at hword
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hword
    refine ⟨w, hw, ?_⟩
    change DiaryChains.model (g.map w) = e i
    rw [heq, model_word]

/-- Exact input needed by simultaneous diary canonization: every chain in
one fixed actual sparse self-copy has a diary representation. -/
theorem sparse_copy_representation {n : Nat} (hn : 0 < n)
    (e : Fin n ↪[language] TernaryModel) :
    ∃ D : PaperDiary n, ∃ d : RayMilliken.Embedding D.shape,
      D.embeddedChain d = SparseModel.selfEmbedding.comp e := by
  apply representation hn (SparseModel.selfEmbedding.comp e)
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  exact (show Sparse.InSparse (fromBlocks (SparseModel.selfEmbedding (e i))) from
    (show SparseModel.selfEmbedding (e i) ∈ {x | Sparse.InSparse (fromBlocks x)} from
      SparseModel.selfEmbedding_range ▸ Set.mem_range_self (e i)))

end AllThoseBigRamsey.Pseudotree.SparseExtraction
