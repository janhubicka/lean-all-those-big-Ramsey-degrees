import AllThoseBigRamsey.Pseudotree.Words
import PseudotreeValidation.Cones
import PseudotreeValidation.Closure
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Rat.Encodable

/-!
# The concrete binary ray and ternary-word model

`BinaryRay` is only a type wrapper, preventing collision with the usual order
on lists. Its order is exactly the manuscript's `2 < end-of-word < 0` order.
The density and no-endpoint proofs come from the checked word algorithms;
mathlib's Cantor theorem then identifies it with the rationals. Literal
ternary words are explicitly equivalent to the block model, preserving order
and the meet function.
-/

namespace AllThoseBigRamsey.Pseudotree

@[ext] structure BinaryRay where
  word : List Bool
  deriving DecidableEq, Repr

namespace BinaryRay

instance : Inhabited BinaryRay := ⟨⟨[]⟩⟩

instance : Countable BinaryRay :=
  Function.Injective.countable (f := word) (fun _ _ h => BinaryRay.ext h)

instance : LinearOrder BinaryRay where
  le s t := binaryLE s.word t.word = true
  le_refl s := binaryLE_refl s.word
  le_trans _ _ _ := binaryLE_trans
  le_antisymm _ _ hst hts := BinaryRay.ext (binaryLE_antisymm hst hts)
  le_total s t := binaryLE_total s.word t.word
  toDecidableLE := fun s t => inferInstanceAs (Decidable (binaryLE s.word t.word = true))
  toDecidableEq := inferInstance

instance : NoMinOrder BinaryRay where
  exists_lt s := by
    obtain ⟨t, hts, hne⟩ := (binary_no_endpoints s.word).1
    refine ⟨⟨t⟩, lt_of_le_of_ne hts ?_⟩
    exact fun h => hne (congrArg word h)

instance : NoMaxOrder BinaryRay where
  exists_gt s := by
    obtain ⟨t, hst, hne⟩ := (binary_no_endpoints s.word).2
    refine ⟨⟨t⟩, lt_of_le_of_ne hst ?_⟩
    exact fun h => hne (congrArg word h).symm

instance : DenselyOrdered BinaryRay where
  dense s t hst := by
    have hne : s.word ≠ t.word := fun h => hst.ne (BinaryRay.ext h)
    obtain ⟨u, hsu, hsne, hut, hune⟩ := binary_dense hst.le hne
    exact ⟨⟨u⟩, lt_of_le_of_ne hsu (fun h => hsne (congrArg word h)),
      lt_of_le_of_ne hut (fun h => hune (congrArg word h))⟩

/-- The binary-word order really is the rational order. -/
theorem nonempty_orderIso_rat : Nonempty (BinaryRay ≃o ℚ) :=
  Order.iso_of_countable_dense BinaryRay ℚ

@[simp] theorem mk_binaryMin (s t : List Bool) :
    BinaryRay.mk (binaryMin s t) = min (BinaryRay.mk s) (BinaryRay.mk t) := by
  by_cases h : binaryLE s t = true
  · have hle : BinaryRay.mk s ≤ BinaryRay.mk t := h
    rw [min_eq_left hle]
    simp [binaryMin, h]
  · have hle : BinaryRay.mk t ≤ BinaryRay.mk s := le_of_not_ge h
    rw [min_eq_right hle]
    simp [binaryMin, h]

end BinaryRay

/-- The manuscript's model in coordinate form, with its verified ray order. -/
abbrev TernaryModel := RayTree BinaryRay

/-- Convert a literal ternary word to the standard ordered model. -/
def toBlocks (s : List TernaryLetter) : TernaryModel :=
  RayTree.map BinaryRay.mk (parseWord s)

/-- Convert a standard model node to its literal ternary word. -/
def fromBlocks (s : TernaryModel) : List TernaryLetter :=
  printWord (RayTree.map BinaryRay.word s)

@[simp] theorem fromBlocks_toBlocks (s : List TernaryLetter) :
    fromBlocks (toBlocks s) = s := by
  simp only [fromBlocks, toBlocks, RayTree.map_map]
  change printWord (RayTree.map id (parseWord s)) = s
  simp

@[simp] theorem toBlocks_fromBlocks (s : TernaryModel) :
    toBlocks (fromBlocks s) = s := by
  simp only [toBlocks, fromBlocks, parse_print, RayTree.map_map]
  change RayTree.map id s = s
  exact RayTree.map_id s

/-- No quotient or loss of words is hidden in the block representation. -/
def wordEquiv : List TernaryLetter ≃ TernaryModel where
  toFun := toBlocks
  invFun := fromBlocks
  left_inv := fromBlocks_toBlocks
  right_inv := toBlocks_fromBlocks

theorem wordBelow_iff_toBlocks_le (s t : List TernaryLetter) :
    wordBelow s t ↔ toBlocks s ≤ toBlocks t := by
  symm
  exact RayTree.below_map_iff (f := BinaryRay.mk)
    (fun {a b} h => BinaryRay.mk.inj h) (fun _ _ => Iff.rfl) (parseWord s) (parseWord t)

@[simp] theorem toBlocks_wordMeet (s t : List TernaryLetter) :
    toBlocks (wordMeet s t) = toBlocks s ⊓ toBlocks t := by
  simp only [toBlocks, wordMeet, parse_print]
  exact RayTree.map_meet (f := BinaryRay.mk) (fun {a b} h => BinaryRay.mk.inj h)
    BinaryRay.mk_binaryMin (parseWord s) (parseWord t)

/-- The concrete ternary model has exactly the two stated cones at every node. -/
theorem ternaryModel_two_cones (s : TernaryModel) :
    ∃ x y, s < x ∧ s < y ∧ x ⊓ y = s ∧
      ∀ z, s < z →
        (s < z ⊓ x ∨ s < z ⊓ y) ∧ ¬(s < z ⊓ x ∧ s < z ⊓ y) :=
  RayTree.two_cones s

/-- Finite sets in the concrete word model have finite functional meet closure. -/
theorem ternaryModel_finite_closure {S : Set TernaryModel} (hS : S.Finite) :
    (FirstOrder.Language.Substructure.closure language S : Set TernaryModel).Finite :=
  finite_meet_closure RayTree.le_or_ge_of_le_common hS

end AllThoseBigRamsey.Pseudotree
