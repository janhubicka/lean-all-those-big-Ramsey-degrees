import AllThoseBigRamsey.Pseudotree.RayMapModel
import PseudotreeValidation.WordModelMathlib
import PseudotreeValidation.FiniteExtensions

/-!
# Strong ray maps as embeddings in the functional language

The Std proof checks literal order reflection and meet preservation. This
module transports that result through the proved word/block equivalence
and packages it as an actual embedding of the language `{≤, ∧}`.
-/

namespace AllThoseBigRamsey.Pseudotree.RayMapModel

open scoped FirstOrder
open RayEmbeddings

def modelMap (f : RayStrongMap) (x : TernaryModel) : TernaryModel :=
  toBlocks (act f (fromBlocks x))

theorem modelMap_injective (f : RayStrongMap) : Function.Injective (modelMap f) := by
  intro x y h
  have hwords := wordEquiv.injective h
  have hsource := act_injective f hwords
  have hblocks := congrArg toBlocks hsource
  simpa only [toBlocks_fromBlocks] using hblocks

private theorem fromBlocks_inf (x y : TernaryModel) :
    fromBlocks (x ⊓ y) = wordMeet (fromBlocks x) (fromBlocks y) := by
  apply wordEquiv.injective
  change toBlocks (fromBlocks (x ⊓ y)) =
    toBlocks (wordMeet (fromBlocks x) (fromBlocks y))
  simp

theorem modelMap_inf (f : RayStrongMap) (x y : TernaryModel) :
    modelMap f (x ⊓ y) = modelMap f x ⊓ modelMap f y := by
  simp only [modelMap, fromBlocks_inf, ← act_wordMeet, toBlocks_wordMeet]

/-- Every ray-preserving strong map induces a genuine self-embedding of
the concrete pseudotree in the language containing both order and meet. -/
def embedding (f : RayStrongMap) : TernaryModel ↪[language] TernaryModel :=
  embeddingOfInfMap (modelMap f) (modelMap_injective f) (modelMap_inf f)

@[simp] theorem embedding_apply_word (f : RayStrongMap) (s : List TernaryLetter) :
    embedding f (toBlocks s) = toBlocks (act f s) := by
  change modelMap f (toBlocks s) = _
  simp only [modelMap, fromBlocks_toBlocks]

end AllThoseBigRamsey.Pseudotree.RayMapModel
