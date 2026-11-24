import PseudotreeValidation.DiaryRecoveryNaturality
import PseudotreeValidation.DiaryCanonization
import PseudotreeValidation.SparseChainGeometry

/-! Actual maxima of coding chains, independently of sparse extraction. -/

namespace AllThoseBigRamsey.Pseudotree

open RayEmbeddings
open scoped FirstOrder

namespace DiaryRecovery

/-- The distinguished word is the maximum in the actual pseudotree order. -/
def IsMaximum (C : Finset Word) (v : Word) : Prop :=
  v ∈ C ∧ ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v

theorem maximum_unique {C : Finset Word} {u v : Word}
    (hu : IsMaximum C u) (hv : IsMaximum C v) : u = v :=
  DiaryChains.model_injective (le_antisymm (hv.2 u hu.1) (hu.2 v hv.1))

theorem maximum_image (f : RayStrongMap) {C : Finset Word} {v : Word}
    (hv : IsMaximum C v) : IsMaximum (C.image f.map) (f.map v) := by
  classical
  refine ⟨Finset.mem_image.mpr ⟨v, hv.1, rfl⟩, ?_⟩
  intro w hw
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
  rw [← PaperDiary.ray_embedding_model, ← PaperDiary.ray_embedding_model]
  exact (embeddingOrderEmbedding (RayMapModel.embedding f)).monotone (hv.2 x hx)

/-- Every 1 on a word below `v` lies on the branch of `v`, in the diary
alphabet. This is a universal order fact, not a sparsity assumption. -/
theorem one_prefix_of_le {w v p t : Word}
    (hbelow : DiaryChains.model w ≤ DiaryChains.model v) (heq : w = p ++ 1 :: t) :
    (p ++ [1]).IsPrefix v := by
  have hb : wordBelow (w.map RayMapModel.toLetter) (v.map RayMapModel.toLetter) :=
    (wordBelow_iff_toBlocks_le _ _).mpr hbelow
  have hform : w.map RayMapModel.toLetter = p.map RayMapModel.toLetter ++
      TernaryLetter.one :: t.map RayMapModel.toLetter := by
    simp only [heq, List.map_append, List.map_cons]
    rfl
  rw [hform] at hb
  have hp := Sparse.wordBelow_one_prefix _ _ _ hb
  have hmap := hp.map RayMapModel.toFin
  have hOne : RayMapModel.toFin TernaryLetter.one = (1 : Fin 3) := rfl
  simpa [List.map_append, List.map_map, Function.comp_def, hOne] using hmap

theorem spine_of_maximum {C : Finset Word} {v : Word} (hv : IsMaximum C v) :
    DiaryNormalization.Spine C v := by
  intro w hw k hOne
  have hk : k < w.length := (List.getElem?_eq_some_iff.mp hOne).1
  have heq : w = w.take k ++ 1 :: w.drop (k+1) := by
    have hget : w[k] = 1 := by simpa only [List.getElem?_eq_getElem hk, Option.some.injEq] using hOne
    simpa only [List.drop_eq_getElem_cons hk, hget] using (List.take_append_drop k w).symm
  have hp := one_prefix_of_le (hv.2 w hw) heq
  have hlen : (w.take k ++ [1]).length = k+1 := by simp [Nat.min_eq_left hk.le]
  rw [List.take_add_one, hOne]
  simpa only [hlen, Option.toList_some] using List.prefix_iff_eq_take.mp hp

end DiaryRecovery

namespace PaperDiary

theorem nodes_iff_prefix_code (D : PaperDiary n) (w : DiaryWord) :
    w ∈ D.nodes ↔ ∃ c ∈ D.codes, w.IsPrefix c := by
  obtain ⟨d, hn, hc⟩ := D.represented
  rw [← hn w, d.toTree_nodes_iff_prefix_code]
  constructor
  · rintro ⟨c, hcode, tail, htail⟩
    exact ⟨c, (hc c).mp hcode, ⟨tail, htail.symm⟩⟩
  · rintro ⟨c, hcode, tail, htail⟩
    exact ⟨c, (hc c).mpr hcode, tail, htail.symm⟩

theorem codes_nonempty (D : PaperDiary n) : D.codes.Nonempty := by
  obtain ⟨c, hc, _⟩ := (D.nodes_iff_prefix_code []).mp D.shape.root_mem
  exact ⟨c, hc⟩

theorem size_pos (D : PaperDiary n) : 0 < n := by
  rw [← D.size]
  exact Finset.card_pos.mpr D.codes_nonempty

/-- Raw diary nodes are the prefix closure of their coding nodes, hence
coding-set equality determines the whole independently defined diary. -/
theorem codes_ext {D E : PaperDiary n} (h : D.codes = E.codes) : D = E := by
  apply PaperDiary.ext _ h
  ext w
  rw [D.nodes_iff_prefix_code, E.nodes_iff_prefix_code, h]

theorem exists_maximum (D : PaperDiary n) : ∃ v, DiaryRecovery.IsMaximum D.codes v := by
  let last : Fin n := ⟨n-1, by have := D.size_pos; omega⟩
  obtain ⟨v, hv, hlast⟩ := D.chainEmbedding_word last
  refine ⟨v, hv, ?_⟩
  intro w hw
  have hmodel : DiaryChains.model w ∈ D.modelCodes := Finset.mem_image.mpr ⟨w, hw, rfl⟩
  have hrange : DiaryChains.model w ∈ Set.range D.chainEmbedding := by
    rw [D.chainEmbedding_range]
    exact hmodel
  obtain ⟨i, hi⟩ := hrange
  rw [hlast, ← hi]
  apply (embeddingOrderEmbedding D.chainEmbedding).monotone
  change i.val ≤ n-1
  omega

noncomputable def maximum (D : PaperDiary n) : DiaryWord := D.exists_maximum.choose

theorem maximum_spec (D : PaperDiary n) : DiaryRecovery.IsMaximum D.codes D.maximum :=
  D.exists_maximum.choose_spec

/-- Membership in the literal coding image is exactly membership in the
actual chain image, after the verified word/model identification. -/
theorem mem_codingImage_iff (D : PaperDiary n) (e : RayMilliken.Embedding D.shape) (w : Word) :
    w ∈ D.codes.image e.realizer.map ↔ DiaryChains.model w ∈ Set.range (D.embeddedChain e) := by
  classical
  rw [D.embeddedChain_range]
  constructor
  · intro hw
    obtain ⟨x, hx, hxw⟩ := Finset.mem_image.mp hw
    refine ⟨x, hx, ?_⟩
    rw [← e.realizer_agrees ⟨x, D.code_node hx⟩, hxw]
  · rintro ⟨x, hx, heq⟩
    apply Finset.mem_image.mpr
    refine ⟨x, hx, ?_⟩
    rw [e.realizer_agrees ⟨x, D.code_node hx⟩]
    exact DiaryChains.model_injective heq

theorem codingImage_eq_of_embeddedChain_eq (D E : PaperDiary n)
    (d : RayMilliken.Embedding D.shape) (e : RayMilliken.Embedding E.shape)
    (h : D.embeddedChain d = E.embeddedChain e) :
    D.codes.image d.realizer.map = E.codes.image e.realizer.map := by
  ext w
  rw [D.mem_codingImage_iff d w, E.mem_codingImage_iff e w, h]

end PaperDiary

namespace DiaryRecovery

theorem maximum_image_eq (D E : PaperDiary n) (f g : RayStrongMap)
    (h : D.codes.image f.map = E.codes.image g.map) :
    f.map D.maximum = g.map E.maximum := by
  have hD := maximum_image f D.maximum_spec
  have hE := maximum_image g E.maximum_spec
  rw [h] at hD
  exact maximum_unique hD hE

end DiaryRecovery
end AllThoseBigRamsey.Pseudotree
