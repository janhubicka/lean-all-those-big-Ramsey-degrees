import PseudotreeValidation.DiaryRecoverySource

/-!
# Recovery and uniqueness of diary types

Normalization is natural under every actual ray-preserving map and is the
identity on every independently specified raw diary. Therefore a literal
coding image determines its diary uniquely. The final theorem is stated on
actual embeddings of the standard finite chain in the functional language.
-/

namespace AllThoseBigRamsey.Pseudotree.DiaryRecovery

open RayEmbeddings DiaryNormalization

/-- The explicit normalization recovers every raw diary from every total
ray-preserving realization of its coding set. -/
theorem image_recovery (D : PaperDiary n) (f : RayStrongMap) (v : Word)
    (hv : IsMaximum D.codes v) :
    codes (D.codes.image f.map) (f.map v) = D.codes := by
  rw [codes_image, codes_source D v hv]

theorem image_nodes_recovery (D : PaperDiary n) (f : RayStrongMap) (v : Word)
    (hv : IsMaximum D.codes v) :
    nodes (D.codes.image f.map) (f.map v) = D.nodes := by
  rw [nodes_image, nodes_source D v hv]

/-- Equal literal coding images have equal independently defined diaries.
The two realizing maps and their level sequences may differ arbitrarily. -/
theorem coding_image_unique (D E : PaperDiary n) (f g : RayStrongMap)
    (h : D.codes.image f.map = E.codes.image g.map) : D = E := by
  apply PaperDiary.codes_ext
  have hmax := maximum_image_eq D E f g h
  calc
    D.codes = codes (D.codes.image f.map) (f.map D.maximum) :=
      (image_recovery D f D.maximum D.maximum_spec).symm
    _ = codes (E.codes.image g.map) (g.map E.maximum) := by rw [h, hmax]
    _ = E.codes := image_recovery E g E.maximum E.maximum_spec

/-- Exact uniqueness on the finite-map domain used by canonization and
sparse extraction. There is no normalization or representation hypothesis. -/
theorem embeddedChain_unique (D E : PaperDiary n)
    (d : RayMilliken.Embedding D.shape) (e : RayMilliken.Embedding E.shape)
    (h : D.embeddedChain d = E.embeddedChain e) : D = E :=
  coding_image_unique D E d.realizer e.realizer (D.codingImage_eq_of_embeddedChain_eq E d e h)

end AllThoseBigRamsey.Pseudotree.DiaryRecovery
