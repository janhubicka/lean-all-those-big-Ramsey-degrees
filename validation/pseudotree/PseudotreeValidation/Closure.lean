import PseudotreeValidation.ModelMathlib

/-!
# Finite meet closure in a pseudotree

Mathlib's general `fg_iff_finite` requires a relational language. The manuscript
has a binary meet function. Here predecessor comparability shows that the
closure of a set is exactly its pairwise-meet image, supplying the missing
finite-generation bridge in the actual functional language.
-/

namespace AllThoseBigRamsey.Pseudotree

open FirstOrder
open scoped FirstOrder

variable {M : Type u} [SemilatticeInf M]

/-- Threefold meets in a meet-tree reduce to a meet of two inputs. -/
theorem inf_inf_eq_pair
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (a b c : M) : (a ⊓ b) ⊓ c = a ⊓ b ∨ (a ⊓ b) ⊓ c = a ⊓ c := by
  have heq : (a ⊓ b) ⊓ c = (a ⊓ b) ⊓ (a ⊓ c) := by ac_rfl
  rw [heq]
  rcases htree (inf_le_left : a ⊓ b ≤ a) (inf_le_left : a ⊓ c ≤ a) with h | h
  · exact Or.inl (inf_eq_left.mpr h)
  · exact Or.inr (inf_eq_right.mpr h)

/-- Pairwise meets are already closed under meet in a meet-tree. -/
theorem image2_inf_closed
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x) (S : Set M) :
    ∀ x ∈ Set.image2 (· ⊓ ·) S S, ∀ y ∈ Set.image2 (· ⊓ ·) S S,
      x ⊓ y ∈ Set.image2 (· ⊓ ·) S S := by
  rintro _ ⟨a, ha, b, hb, rfl⟩ _ ⟨c, hc, d, hd, rfl⟩
  have heq : (a ⊓ b) ⊓ (c ⊓ d) = ((a ⊓ b) ⊓ c) ⊓ d := (inf_assoc _ _ _).symm
  rw [heq]
  rcases inf_inf_eq_pair htree a b c with h | h
  · rw [h]
    rcases inf_inf_eq_pair htree a b d with h' | h'
    · exact ⟨a, ha, b, hb, h'.symm⟩
    · exact ⟨a, ha, d, hd, h'.symm⟩
  · rw [h]
    rcases inf_inf_eq_pair htree a c d with h' | h'
    · exact ⟨a, ha, c, hc, h'.symm⟩
    · exact ⟨a, ha, d, hd, h'.symm⟩

/-- Functional closure is exactly the pairwise-meet image, including for the
empty set (there are no constants in the language). -/
theorem closure_eq_pairwise_meets
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x) (S : Set M) :
    (FirstOrder.Language.Substructure.closure language S : Set M) =
      Set.image2 (· ⊓ ·) S S := by
  let P := substructureOfMeetClosed (Set.image2 (· ⊓ ·) S S) (image2_inf_closed htree S)
  have hSP : S ⊆ P := by
    intro x hx
    exact ⟨x, hx, x, hx, inf_idem x⟩
  apply Set.Subset.antisymm
  · exact FirstOrder.Language.Substructure.closure_le.mpr hSP
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact substructure_inf_mem _ (FirstOrder.Language.Substructure.subset_closure ha)
      (FirstOrder.Language.Substructure.subset_closure hb)

/-- A finite set generates a finite meet-closed substructure. -/
theorem finite_meet_closure
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    {S : Set M} (hS : S.Finite) :
    (FirstOrder.Language.Substructure.closure language S : Set M).Finite := by
  rw [closure_eq_pairwise_meets htree S]
  exact hS.image2 (· ⊓ ·) hS

/-- In a meet-tree, finitely generated and finite agree even in the functional
language `{≤, ∧}`. -/
theorem fg_iff_finite_meet_tree
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x) :
    FirstOrder.Language.Structure.FG language M ↔ Finite M := by
  constructor
  · intro h
    obtain ⟨S, hS, htop⟩ := FirstOrder.Language.Structure.fg_iff.mp h
    have hf := finite_meet_closure htree hS
    rw [htop] at hf
    exact Set.finite_univ_iff.mp hf
  · intro h
    let _ : Finite M := h
    exact FirstOrder.Language.Structure.FG.of_finite

/-- The generic closure result specializes to the explicit block model. -/
theorem RayTree.fg_iff_finite {α : Type u} [LinearOrder α] :
    FirstOrder.Language.Structure.FG language (RayTree α) ↔ Finite (RayTree α) :=
  fg_iff_finite_meet_tree RayTree.le_or_ge_of_le_common

end AllThoseBigRamsey.Pseudotree
