import PseudotreeValidation.RayMilliken
import PseudotreeValidation.DiaryChains
import PseudotreeValidation.RayMapEmbedding

/-! Simultaneous canonization of all literal n-diaries, with colourings of
actual embeddings of the standard n-element chain in the functional model.
The finite diary class is independently defined and its finiteness is proved.
-/

namespace AllThoseBigRamsey.Pseudotree

open RayEmbeddings
open scoped FirstOrder

namespace RayMilliken

theorem restricted_milliken_list {ι : Type} (shape : ι → Shape) {colours : ℕ}
    (ds : List ι) (colour : ∀ d, Embedding (shape d) → Fin (colours + 1)) :
    ∃ g : RayStrongMap, ∀ d ∈ ds, ∃ c : Fin (colours + 1),
      ∀ e : Embedding (shape d), colour d (Embedding.comp g e) = c := by
  induction ds generalizing colour with
  | nil => exact ⟨RayStrongMap.identity, by simp⟩
  | cons d ds ih =>
    obtain ⟨c, g, hg⟩ := restricted_milliken (shape d) (colour d)
    obtain ⟨h, hh⟩ := ih (fun d => induced (colour d) g)
    refine ⟨g.comp h, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨c, fun e => by simpa only [← Embedding.comp_comp] using hg (Embedding.comp h e)⟩
    · obtain ⟨c', hc'⟩ := hh a ha
      exact ⟨c', fun e => by simpa only [induced, Embedding.comp_comp] using hc' e⟩

/-- A finite family of finite prefix trees can be canonized at once. -/
theorem restricted_milliken_family {ι : Type} [Fintype ι]
    (shape : ι → Shape) {colours : ℕ}
    (colour : ∀ d, Embedding (shape d) → Fin (colours + 1)) :
    ∃ g : RayStrongMap, ∃ palette : ι → Fin (colours + 1),
      ∀ d (e : Embedding (shape d)), colour d (Embedding.comp g e) = palette d := by
  classical
  obtain ⟨g, hg⟩ := restricted_milliken_list shape Finset.univ.toList colour
  have hc : ∀ d, ∃ c : Fin (colours + 1),
      ∀ e : Embedding (shape d), colour d (Embedding.comp g e) = c :=
    fun d => hg d (by simp)
  choose palette hp using hc
  exact ⟨g, palette, hp⟩

end RayMilliken

namespace PaperDiary

/-- Raw diary axioms imply the exact finite-tree hypothesis of restricted
Milliken. The node set is unchanged. -/
noncomputable def shape (D : PaperDiary n) : RayMilliken.Shape where
  nodes := D.nodes
  root_mem := by
    obtain ⟨height, T⟩ := D.axioms
    obtain ⟨kind, w, P⟩ := T.level 0 T.height_pos
    have hw : w = [] := List.length_eq_zero_iff.mp P.critical_length
    exact hw ▸ P.critical_mem
  prefix_closed := by
    intro s t hst
    obtain ⟨height, T⟩ := D.axioms
    have h := T.prefix_closed (s ++ t) hst s.length (by simp)
    simpa only [List.take_append_length] using h
  one_per_level := by
    intro s hs t ht hlen hs1 ht1
    obtain ⟨p, rfl⟩ := hs1
    obtain ⟨q, rfl⟩ := ht1
    obtain ⟨d, hnodes, _⟩ := D.represented
    have hp : p = q := d.toTree_one_per_level ((hnodes _).mpr hs) ((hnodes _).mpr ht)
      (by simpa only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] using hlen)
    rw [hp]

@[simp] theorem shape_nodes (D : PaperDiary n) : D.shape.nodes = D.nodes := rfl

theorem code_node (D : PaperDiary n) {w : DiaryWord} (hw : w ∈ D.codes) : w ∈ D.shape.nodes := by
  obtain ⟨_, T⟩ := D.axioms
  exact T.code_subset hw

theorem chainEmbedding_word (D : PaperDiary n) (i : Fin n) :
    ∃ w : DiaryWord, w ∈ D.codes ∧ DiaryChains.model w = D.chainEmbedding i := by
  have h := (D.codeOrderIso i).property
  change _ ∈ D.codes.image DiaryChains.model at h
  exact Finset.mem_image.mp h

@[simp] theorem ray_embedding_model (f : RayStrongMap) (w : DiaryWord) :
    RayMapModel.embedding f (DiaryChains.model w) = DiaryChains.model (f.map w) := by
  rw [DiaryChains.model, RayMapModel.embedding_apply_word]
  simp [RayMapModel.act, List.map_map, Function.comp_def, DiaryChains.model]

/-- The standard chain represented by a finite ray embedding of the diary.
This definition is independent of which total realization is chosen. -/
noncomputable def embeddedChain (D : PaperDiary n) (e : RayMilliken.Embedding D.shape) :
    Fin n ↪[language] TernaryModel :=
  (RayMapModel.embedding e.realizer).comp D.chainEmbedding

theorem embeddedChain_apply_word (D : PaperDiary n) (e : RayMilliken.Embedding D.shape)
    (i : Fin n) (w : DiaryWord) (hw : w ∈ D.codes)
    (hi : D.chainEmbedding i = DiaryChains.model w) :
    D.embeddedChain e i = DiaryChains.model (e ⟨w, D.code_node hw⟩) := by
  change RayMapModel.embedding e.realizer (D.chainEmbedding i) = _
  rw [hi, ray_embedding_model, e.realizer_agrees ⟨w, D.code_node hw⟩]

theorem embeddedChain_comp (D : PaperDiary n) (e : RayMilliken.Embedding D.shape)
    (g : RayStrongMap) :
    D.embeddedChain (RayMilliken.Embedding.comp g e) =
      (RayMapModel.embedding g).comp (D.embeddedChain e) := by
  ext i
  obtain ⟨w, hw, hi⟩ := D.chainEmbedding_word i
  rw [D.embeddedChain_apply_word _ i w hw hi.symm]
  change _ = RayMapModel.embedding g (D.embeddedChain e i)
  rw [D.embeddedChain_apply_word _ i w hw hi.symm, ray_embedding_model]
  rfl

theorem embeddedChain_ofTotal (D : PaperDiary n) (f : RayStrongMap) :
    D.embeddedChain (RayMilliken.Embedding.ofTotal D.shape f) =
      (RayMapModel.embedding f).comp D.chainEmbedding := by
  ext i
  obtain ⟨w, hw, hi⟩ := D.chainEmbedding_word i
  rw [D.embeddedChain_apply_word _ i w hw hi.symm]
  change _ = RayMapModel.embedding f (D.chainEmbedding i)
  rw [hi.symm, ray_embedding_model]
  rfl

/-- The range is exactly the images of the literal coding nodes under the
finite map, not a proxy set or a conditional chain assertion. -/
theorem embeddedChain_range (D : PaperDiary n) (e : RayMilliken.Embedding D.shape) :
    Set.range (D.embeddedChain e) =
      {x | ∃ w : DiaryWord, ∃ hw : w ∈ D.codes,
        DiaryChains.model (e ⟨w, D.code_node hw⟩) = x} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨w, hw, hi⟩ := D.chainEmbedding_word i
    exact ⟨w, hw, (D.embeddedChain_apply_word e i w hw hi.symm).symm⟩
  · rintro ⟨w, hw, rfl⟩
    have hmodel : DiaryChains.model w ∈ D.modelCodes := Finset.mem_image.mpr ⟨w, hw, rfl⟩
    have hr : DiaryChains.model w ∈ Set.range D.chainEmbedding := by
      rw [D.chainEmbedding_range]
      exact hmodel
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, D.embeddedChain_apply_word e i w hw hi⟩

end PaperDiary

namespace DiaryCanonization

/-- Simultaneous canonization for colourings of actual functional-language
chain embeddings. There is one colour per independently specified diary,
and all its finite ray realizations receive that colour after one common
self-embedding. -/
theorem simultaneous {n colours : ℕ}
    (colour : (Fin n ↪[language] TernaryModel) → Fin (colours + 1)) :
    ∃ g : RayStrongMap, ∃ palette : PaperDiary n → Fin (colours + 1),
      ∀ (D : PaperDiary n) (e : RayMilliken.Embedding D.shape),
        colour ((RayMapModel.embedding g).comp (D.embeddedChain e)) = palette D := by
  obtain ⟨g, palette, hg⟩ := RayMilliken.restricted_milliken_family
    (fun D : PaperDiary n => D.shape) (fun D e => colour (D.embeddedChain e))
  refine ⟨g, palette, ?_⟩
  intro D e
  simpa only [PaperDiary.embeddedChain_comp] using hg D e

/-- The equivalent total-map formulation, useful when finite realizations
have already been completed by the checked completion theorem. -/
theorem simultaneous_total {n colours : ℕ}
    (colour : (Fin n ↪[language] TernaryModel) → Fin (colours + 1)) :
    ∃ g : RayStrongMap, ∃ palette : PaperDiary n → Fin (colours + 1),
      ∀ (D : PaperDiary n) (f : RayStrongMap),
        colour ((RayMapModel.embedding g).comp
          ((RayMapModel.embedding f).comp D.chainEmbedding)) = palette D := by
  obtain ⟨g, palette, hg⟩ := simultaneous colour
  refine ⟨g, palette, ?_⟩
  intro D f
  simpa only [PaperDiary.embeddedChain_ofTotal] using
    hg D (RayMilliken.Embedding.ofTotal D.shape f)

end DiaryCanonization
end AllThoseBigRamsey.Pseudotree
