import PseudotreeValidation.Profiles
import PseudotreeValidation.WordModelMathlib

/-!
# The profile construction on every functional copy of the ternary model

The hypotheses used by `Profiles.System.repeated_endExtension` are established
here on the ranges of actual embeddings in the paper's functional language.
Thus the binary-model application does not assume an unproved profile property
or treat order embeddings as automatically preserving meet.
-/
namespace AllThoseBigRamsey.Pseudotree

open FirstOrder
open scoped FirstOrder

/-- An embedding in the language {≤,∧} is an order embedding. -/
def functionalOrderEmbedding {M N : Type*} [SemilatticeInf M] [SemilatticeInf N]
    (f : M ↪[language] N) : M ↪o N where
  toFun := f
  inj' := f.injective
  map_rel_iff' := by
    intro x y
    let v : Fin 2 → M := fun i => if i = 0 then x else y
    have h := f.map_rel OrderRelation.le v
    change (f (v 0) ≤ f (v 1) ↔ v 0 ≤ v 1) at h
    simpa [v] using h

/-- Meet preservation follows from the function-symbol clause of the embedding. -/
theorem functionalEmbedding_inf {M N : Type*} [SemilatticeInf M] [SemilatticeInf N]
    (f : M ↪[language] N) (x y : M) : f (x ⊓ y) = f x ⊓ f y := by
  let v : Fin 2 → M := fun i => if i = 0 then x else y
  have h := f.map_fun MeetFunction.meet v
  change f (v 0 ⊓ v 1) = f (v 0) ⊓ f (v 1) at h
  simpa [v] using h

namespace Profiles

/-- A branch different from a specified upper direction exists in the concrete model. -/
theorem ternary_branch {x a : TernaryModel} (hxa : x < a) :
    ∃ z, x < z ∧ z ⊓ a = x := by
  obtain ⟨v, w, hxv, hxw, _, hcones⟩ := ternaryModel_two_cones x
  have hnot := (hcones a hxa).2
  by_cases hav : x < a ⊓ v
  · refine ⟨w, hxw, ?_⟩
    have haw : ¬x < a ⊓ w := fun h => hnot ⟨hav, h⟩
    have he : x = a ⊓ w := (lt_or_eq_of_le (le_inf hxa.le hxw.le)).resolve_left haw
    simpa [inf_comm] using he.symm
  · refine ⟨v, hxv, ?_⟩
    have he : x = a ⊓ v := (lt_or_eq_of_le (le_inf hxa.le hxv.le)).resolve_left hav
    simpa [inf_comm] using he.symm

/-- The actual countable ternary model admits a surjective enumeration. -/
theorem exists_ternary_enumeration :
    ∃ e : ℕ → TernaryModel, Function.Surjective e := by
  let : Nonempty TernaryModel := ⟨RayTree.point ⟨[]⟩⟩
  exact exists_surjective_nat TernaryModel

/-- Fix one enumeration; every profile below uses this same ambient enumeration. -/
noncomputable def ternarySystem : System TernaryModel where
  enumerate := exists_ternary_enumeration.choose
  onto := exists_ternary_enumeration.choose_spec
  predecessors := RayTree.le_or_ge_of_le_common

/-- Every functional self-copy has the geometric properties needed in the
no-isolation proof. No ultrahomogeneity assumption is needed for this step. -/
theorem ternary_copy_rich (f : TernaryModel ↪[language] TernaryModel) :
    ternarySystem.RichSubset (Set.range f) := by
  let : Nonempty TernaryModel := ⟨RayTree.point ⟨[]⟩⟩
  exact ternarySystem.richSubset_range ternary_branch (functionalOrderEmbedding f)
    (functionalEmbedding_inf f)

/-- There is a repeated profile in every actual functional copy. -/
theorem ternary_copy_repeated_nonempty (f : TernaryModel ↪[language] TernaryModel) :
    ∃ s, ternarySystem.Repeated (Set.range f) s :=
  ternarySystem.repeated_nonempty (ternary_copy_rich f)

/-- Repeated profiles in every functional copy have proper end-extensions
whose new elements are all beyond any prescribed cutoff. -/
theorem ternary_copy_endExtension (f : TernaryModel ↪[language] TernaryModel)
    {s : Finset ℕ} (hs : ternarySystem.Repeated (Set.range f) s) (N : ℕ) :
    ∃ t, ternarySystem.Repeated (Set.range f) t ∧ s ⊂ t ∧
      ∀ i ∈ t, i ∉ s → N < i :=
  ternarySystem.repeated_endExtension (ternary_copy_rich f) hs N

end Profiles
end AllThoseBigRamsey.Pseudotree
