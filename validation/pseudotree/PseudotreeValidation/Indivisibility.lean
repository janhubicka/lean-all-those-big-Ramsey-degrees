import PseudotreeValidation.MixedProduct
import PseudotreeValidation.RayMapEmbedding
import PseudotreeValidation.Incomparables
import Mathlib.Order.WellFounded

/-! The singleton chain degree and rigidity of finite chain copies. -/

namespace AllThoseBigRamsey.Pseudotree

open scoped FirstOrder
open RayEmbeddings

theorem word_indivisible {n : ℕ} (colour : Word → Fin (n + 1)) :
    ∃ c : Fin (n + 1), ∃ f : RayStrongMap, ∀ s : Word, colour (f.map s) = c := by
  let lifted : Mixed.Tuple 0 → Fin (n + 1) := fun x => colour (x 0)
  obtain ⟨c, F, hF⟩ := Mixed.mixed_product lifted
  refine ⟨c, F.maps 0, ?_⟩
  intro s
  have hx : Mixed.AdmissibleAt 0 s.length (fun _ => s) := by
    refine ⟨fun _ => rfl, ?_⟩
    intro i hi
    exact False.elim (hi (Fin.ext (by omega)))
  exact hF s.length (fun _ => s) hx

/-- Every finite colouring of the actual model has a monochromatic
functional-language self-copy. This is the singleton chain case. -/
theorem ternaryModel_indivisible {n : ℕ} (colour : TernaryModel → Fin (n + 1)) :
    ∃ c : Fin (n + 1), ∃ f : TernaryModel ↪[language] TernaryModel,
      ∀ x : TernaryModel, colour (f x) = c := by
  let lifted : Word → Fin (n + 1) := fun s => colour (toBlocks (s.map RayMapModel.toLetter))
  obtain ⟨c, f, hf⟩ := word_indivisible lifted
  refine ⟨c, RayMapModel.embedding f, ?_⟩
  intro x
  have h := hf ((fromBlocks x).map RayMapModel.toFin)
  change colour (toBlocks (RayMapModel.act f (fromBlocks x))) = c at h
  change colour (RayMapModel.modelMap f x) = c
  exact h

/-- Finite chains are rigid: functional embeddings with the same image
coincide. Thus embedding colourings and copy colourings have the same domain
up to the unique increasing enumeration. -/
theorem chain_embedding_eq_of_range_eq {n : ℕ}
    (e g : Fin n ↪[language] TernaryModel) (hrange : Set.range e = Set.range g) : e = g := by
  have he := (embeddingOrderEmbedding e).strictMono
  have hg := (embeddingOrderEmbedding g).strictMono
  have hfun : (fun i => e i) = (fun i => g i) :=
    (he.range_inj_of_wellFoundedLT hg).mp hrange
  apply FirstOrder.Language.Embedding.ext
  exact congrFun hfun

def pointEmbedding (x : TernaryModel) : Fin 1 ↪[language] TernaryModel :=
  embeddingOfInfMap (fun _ => x)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ _ => (inf_idem x).symm)

theorem pointEmbedding_comp (f : TernaryModel ↪[language] TernaryModel)
    (e : Fin 1 ↪[language] TernaryModel) : f.comp e = pointEmbedding (f (e 0)) := by
  apply FirstOrder.Language.Embedding.ext
  intro i
  change f (e i) = f (e 0)
  rw [Subsingleton.elim i 0]

theorem singleton_chain_bound : Incomparables.FunctionalBigRamseyBound (Fin 1) 1 := by
  intro r hr colour
  cases r with
  | zero => omega
  | succ n =>
    obtain ⟨c, f, hf⟩ := ternaryModel_indivisible (fun x => colour (pointEmbedding x))
    refine ⟨f, {c}, by simp, ?_⟩
    intro e
    rw [pointEmbedding_comp f e, hf]
    simp

theorem singleton_chain_minimal {d : ℕ}
    (h : Incomparables.FunctionalBigRamseyBound (Fin 1) d) : 1 ≤ d := by
  obtain ⟨f, palette, hcard, hcover⟩ := h 1 (by omega) (fun _ => (0 : Fin 1))
  have hmem := hcover (pointEmbedding (toBlocks []))
  have hpos : 0 < palette.card := Finset.card_pos.mpr ⟨0, hmem⟩
  omega

end AllThoseBigRamsey.Pseudotree
