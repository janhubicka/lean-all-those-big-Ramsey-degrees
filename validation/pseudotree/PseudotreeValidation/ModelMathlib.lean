import AllThoseBigRamsey.Pseudotree.Model
import Mathlib.ModelTheory.Fraisse
import Mathlib.Order.CountableDenseLinearOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Preorder.Chain

/-!
# Mathlib interfaces for the pseudotree block model

Installs standard order instances and the manuscript's functional language
`{≤, ∧}`. Its substructures are genuinely meet-closed. This does not substitute
relational-only substructures for the manuscript's functional substructures.
-/

namespace AllThoseBigRamsey.Pseudotree
namespace RayTree
variable {α : Type u} {β : Type v}

instance [Countable α] : Countable (RayTree α) :=
  Function.Injective.countable (f := coordinates)
    (fun _ _ h => coordinates_injective h)

instance [PartialOrder α] : PartialOrder (RayTree α) where
  le := Below (fun a b : α => a ≤ b)
  le_refl := below_refl (r := fun a b : α => a ≤ b) (fun _ => le_rfl)
  le_trans _ _ _ := below_trans (r := fun a b : α => a ≤ b)
    (fun hab hbc => le_trans hab hbc)
  le_antisymm _ _ := below_antisymm (r := fun a b : α => a ≤ b)
    (fun hab hba => le_antisymm hab hba)

instance [LinearOrder α] : SemilatticeInf (RayTree α) where
  inf := meet min
  inf_le_left := meet_below_left min_le_left
  inf_le_right := meet_below_right min_le_right
  le_inf _ _ _ := below_meet (r := fun a b : α => a ≤ b) (μ := min)
    (fun hca hcb => le_min hca hcb)

/-- The pseudotree axiom in standard order notation. -/
theorem le_or_ge_of_le_common [LinearOrder α] {s t w : RayTree α}
    (hs : s ≤ w) (ht : t ≤ w) : s ≤ t ∨ t ≤ s :=
  predecessors_comparable (r := fun a b : α => a ≤ b) le_total hs ht

theorem predecessors_isChain [LinearOrder α] (w : RayTree α) :
    IsChain (· ≤ ·) (Set.Iic w) := by
  intro s hs t ht _
  exact le_or_ge_of_le_common hs ht

theorem strictBelow_iff_lt [PartialOrder α] (s t : RayTree α) :
    StrictBelow (fun a b : α => a ≤ b) s t ↔ s < t := by
  change (s ≤ t ∧ s ≠ t) ↔ s < t
  exact lt_iff_le_and_ne.symm

instance [PartialOrder α] [NoMinOrder α] : NoMinOrder (RayTree α) where
  exists_lt s := by
    have hα : ∀ a : α, ∃ b, b ≤ a ∧ b ≠ a := by
      intro a
      obtain ⟨b, hb⟩ := NoMinOrder.exists_lt a
      exact ⟨b, hb.le, hb.ne⟩
    obtain ⟨t, ht⟩ := exists_strict_below hα s
    exact ⟨t, (strictBelow_iff_lt t s).1 ht⟩

instance [PartialOrder α] : NoMaxOrder (RayTree α) where
  exists_gt s := by
    obtain ⟨t, ht⟩ := exists_strict_above (r := (· ≤ ·)) (fun _ => le_rfl) s
    exact ⟨t, (strictBelow_iff_lt s t).1 ht⟩

instance [LinearOrder α] [NoMinOrder α] [DenselyOrdered α] :
    DenselyOrdered (RayTree α) where
  dense s t hst := by
    have hmin : ∀ a : α, ∃ b, b ≤ a ∧ b ≠ a := by
      intro a
      obtain ⟨b, hb⟩ := NoMinOrder.exists_lt a
      exact ⟨b, hb.le, hb.ne⟩
    have hdense : ∀ a b : α, a ≤ b → a ≠ b →
        ∃ c, a ≤ c ∧ a ≠ c ∧ c ≤ b ∧ c ≠ b := by
      intro a b hab hne
      obtain ⟨c, hac, hcb⟩ := _root_.exists_between (lt_of_le_of_ne hab hne)
      exact ⟨c, hac.le, hac.ne, hcb.le, hcb.ne⟩
    obtain ⟨z, hsz, hzt⟩ := RayTree.exists_between (fun _ => le_rfl) hmin hdense
      ((strictBelow_iff_lt s t).2 hst)
    exact ⟨z, (strictBelow_iff_lt s z).1 hsz, (strictBelow_iff_lt z t).1 hzt⟩

/-- Coordinate order embeddings preserve the pseudotree order. -/
def orderEmbedding [LinearOrder α] [LinearOrder β] (f : α ↪o β) :
    RayTree α ↪o RayTree β where
  toFun := map f
  inj' := by
    intro s t h
    exact map_injective (f := (f : α → β)) (fun {a b} h => f.injective h) h
  map_rel_iff' := below_map_iff (f := (f : α → β))
    (fun {a b} h => f.injective h) (fun _ _ => f.le_iff_le) _ _

@[simp] theorem map_inf [LinearOrder α] [LinearOrder β]
    (f : α ↪o β) (s t : RayTree α) : map f (s ⊓ t) = map f s ⊓ map f t := by
  exact map_meet (f := (f : α → β)) (fun {a b} h => f.injective h)
    (fun a b => f.monotone.map_min) s t
end RayTree

open FirstOrder
open scoped FirstOrder

/-- The only function symbol is binary meet. -/
inductive MeetFunction : ℕ → Type
  | meet : MeetFunction 2

/-- The only relation symbol is binary order. -/
inductive OrderRelation : ℕ → Type
  | le : OrderRelation 2

/-- The functional language used in the manuscript. -/
def language : Language where
  Functions := MeetFunction
  Relations := OrderRelation

instance semilatticeStructure (M : Type u) [SemilatticeInf M] : language.Structure M where
  funMap := fun f x => match f with
    | .meet => x 0 ⊓ x 1
  RelMap := fun r x => match r with
    | .le => x 0 ≤ x 1

/-- Meet-closed sets give functional substructures. -/
def substructureOfMeetClosed {M : Type u} [SemilatticeInf M] (S : Set M)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ⊓ y ∈ S) : language.Substructure M where
  carrier := S
  fun_mem := by
    intro n f x hx
    cases f
    exact hS (x 0) (hx 0) (x 1) (hx 1)

/-- Conversely, every functional substructure is meet-closed. -/
theorem substructure_inf_mem {M : Type u} [SemilatticeInf M]
    (S : language.Substructure M) {x y : M} (hx : x ∈ S) (hy : y ∈ S) : x ⊓ y ∈ S := by
  let v : Fin 2 → M := fun i => if i = 0 then x else y
  have hv : ∀ i, v i ∈ S := by
    intro i
    by_cases hi : i = 0
    · simpa [v, hi] using hx
    · simpa [v, hi] using hy
  have h := S.fun_mem MeetFunction.meet v hv
  change v 0 ⊓ v 1 ∈ S at h
  simpa [v] using h

/-- Ray order embeddings are embeddings in the functional language. -/
def rayEmbedding {α : Type u} {β : Type v} [LinearOrder α] [LinearOrder β]
    (f : α ↪o β) : RayTree α ↪[language] RayTree β where
  toFun := RayTree.map f
  inj' := by
    intro s t h
    exact RayTree.map_injective (f := (f : α → β)) (fun {a b} h => f.injective h) h
  map_fun' := by
    intro n g x
    cases g
    exact RayTree.map_inf f (x 0) (x 1)
  map_rel' := by
    intro n r x
    cases r
    exact RayTree.below_map_iff (f := (f : α → β))
      (fun {a b} h => f.injective h) (fun _ _ => f.le_iff_le) (x 0) (x 1)

/-- The precise extension theorem for the incomparable-triple step.
Ultrahomogeneity is an explicit hypothesis, not silently assumed proved. -/
theorem extend_finite_pattern {M A B : Type u}
    [language.Structure M] [language.Structure A] [language.Structure B]
    (hM : language.IsUltrahomogeneous M)
    (hA : FirstOrder.Language.Structure.FG language A)
    (f : A ↪[language] M) (g : A ↪[language] B) (hB : Nonempty (B ↪[language] M)) :
    ∃ f' : B ↪[language] M, f = f'.comp g :=
  hM.extend_embedding hA f g (h := hB)
end AllThoseBigRamsey.Pseudotree
