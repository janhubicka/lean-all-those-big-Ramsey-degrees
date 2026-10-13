import Std

/-!
Prefix and socle transport for a coherent completion with a deletion map.
These are structural consequences of the written canonical-insertion lemma,
not a formalisation of full relational type-respecting amalgamation.
-/
namespace AllThoseBigRamsey.CompletionTransport

universe u v w z

structure PrefixSystem (X : Type u) (S : Type v) where
  level : X → Nat
  cut : Nat → X → X
  socle : X → S
  cut_self : ∀ x, cut (level x) x = x
  cut_level : ∀ x l, l ≤ level x → level (cut l x) = l
  cut_cut : ∀ x i j, i ≤ j → j ≤ level x → cut i (cut j x) = cut i x

namespace PrefixSystem
variable {X : Type u} {S : Type v} (P : PrefixSystem X S)

def Below (x y : X) : Prop :=
  P.level x ≤ P.level y ∧ P.cut (P.level x) y = x

def Compatible (x y : X) : Prop :=
  P.level x = P.level y ∧ P.socle x = P.socle y

theorem below_refl (x : X) : P.Below x x :=
  ⟨Nat.le_refl _, P.cut_self x⟩

theorem below_antisymm {x y : X} (h : P.Below x y) (g : P.Below y x) :
    x = y := by
  have hl : P.level x = P.level y := Nat.le_antisymm h.1 g.1
  calc
    x = P.cut (P.level x) y := h.2.symm
    _ = P.cut (P.level y) y := congrArg (fun l => P.cut l y) hl
    _ = y := P.cut_self y

theorem below_trans {x y z : X} (h : P.Below x y) (g : P.Below y z) :
    P.Below x z := by
  refine ⟨Nat.le_trans h.1 g.1, ?_⟩
  calc
    P.cut (P.level x) z = P.cut (P.level x) (P.cut (P.level y) z) :=
      (P.cut_cut z (P.level x) (P.level y) h.1 g.1).symm
    _ = P.cut (P.level x) y := congrArg (P.cut (P.level x)) g.2
    _ = x := h.2

theorem predecessors_comparable {x y z : X}
    (h : P.Below x z) (g : P.Below y z) : P.Below x y ∨ P.Below y x := by
  by_cases hl : P.level x ≤ P.level y
  · left
    refine ⟨hl, ?_⟩
    calc
      P.cut (P.level x) y = P.cut (P.level x) (P.cut (P.level y) z) :=
        congrArg (P.cut (P.level x)) g.2.symm
      _ = P.cut (P.level x) z := P.cut_cut z _ _ hl g.1
      _ = x := h.2
  · right
    have hl' : P.level y ≤ P.level x := by omega
    refine ⟨hl', ?_⟩
    calc
      P.cut (P.level y) x = P.cut (P.level y) (P.cut (P.level x) z) :=
        congrArg (P.cut (P.level y)) h.2.symm
      _ = P.cut (P.level y) z := P.cut_cut z _ _ hl' h.1
      _ = y := g.2
end PrefixSystem

structure CoherentCompletion {X : Type u} {S : Type v}
    {Y : Type w} {T : Type z} (P : PrefixSystem X S) (Q : PrefixSystem Y T) where
  image : X → Y
  levels : Nat → Nat
  strict : ∀ a b, a < b → levels a < levels b
  level_image : ∀ x, Q.level (image x) = levels (P.level x)
  prefix_image : ∀ l x, l ≤ P.level x →
    Q.cut (levels l) (image x) = image (P.cut l x)
  erase : Y → X
  erase_image : ∀ x, erase (image x) = x
  socleImage : S → T
  socle_image : ∀ x, Q.socle (image x) = socleImage (P.socle x)
  eraseSocle : T → S
  erase_socle_image : ∀ s, eraseSocle (socleImage s) = s

namespace CoherentCompletion
variable {X : Type u} {S : Type v} {Y : Type w} {T : Type z}
variable {P : PrefixSystem X S} {Q : PrefixSystem Y T}
variable (C : CoherentCompletion P Q)

theorem image_injective {x y : X} (h : C.image x = C.image y) : x = y := by
  have he := congrArg C.erase h
  simpa only [C.erase_image] using he

theorem levels_le_iff {a b : Nat} : C.levels a ≤ C.levels b ↔ a ≤ b := by
  constructor
  · intro h
    by_cases hab : a ≤ b
    · exact hab
    · have hba : b < a := by omega
      have hc := C.strict b a hba
      omega
  · intro h
    by_cases hab : a = b
    · subst b
      exact Nat.le_refl _
    · have hc := C.strict a b (by omega)
      omega

theorem levels_eq_iff {a b : Nat} : C.levels a = C.levels b ↔ a = b := by
  constructor
  · intro h
    have hab : a ≤ b := C.levels_le_iff.mp (Nat.le_of_eq h)
    have hba : b ≤ a := C.levels_le_iff.mp (Nat.le_of_eq h.symm)
    omega
  · intro h
    exact congrArg C.levels h

theorem below_iff {x y : X} : Q.Below (C.image x) (C.image y) ↔ P.Below x y := by
  constructor
  · intro h
    have hl : C.levels (P.level x) ≤ C.levels (P.level y) := by
      simpa only [C.level_image] using h.1
    have hl' : P.level x ≤ P.level y := C.levels_le_iff.mp hl
    refine ⟨hl', ?_⟩
    apply C.image_injective
    calc
      C.image (P.cut (P.level x) y) =
          Q.cut (C.levels (P.level x)) (C.image y) :=
        (C.prefix_image (P.level x) y hl').symm
      _ = Q.cut (Q.level (C.image x)) (C.image y) := by rw [C.level_image]
      _ = C.image x := h.2
  · intro h
    constructor
    · have hl := C.levels_le_iff.mpr h.1
      simpa only [C.level_image] using hl
    · calc
        Q.cut (Q.level (C.image x)) (C.image y) =
            Q.cut (C.levels (P.level x)) (C.image y) := by rw [C.level_image]
        _ = C.image (P.cut (P.level x) y) := C.prefix_image (P.level x) y h.1
        _ = C.image x := congrArg C.image h.2

theorem compatible_iff {x y : X} :
    Q.Compatible (C.image x) (C.image y) ↔ P.Compatible x y := by
  constructor
  · intro h
    have hl : C.levels (P.level x) = C.levels (P.level y) := by
      simpa only [C.level_image] using h.1
    have hs : C.socleImage (P.socle x) = C.socleImage (P.socle y) := by
      simpa only [C.socle_image] using h.2
    refine ⟨C.levels_eq_iff.mp hl, ?_⟩
    have he := congrArg C.eraseSocle hs
    simpa only [C.erase_socle_image] using he
  · intro h
    constructor
    · have hl := congrArg C.levels h.1
      simpa only [C.level_image] using hl
    · have hs := congrArg C.socleImage h.2
      simpa only [C.socle_image] using hs
end CoherentCompletion

/- The following Boolean triangles describe three distinct points of an
 equivalence relation. `true` means distance one, `false` means distance two. -/
def EquivalenceTriangle (ab ax bx : Bool) : Prop :=
  ((ab = true ∧ ax = true) → bx = true) ∧
  ((ab = true ∧ bx = true) → ax = true) ∧
  ((ax = true ∧ bx = true) → ab = true)

theorem same_type_completable : EquivalenceTriangle true true true := by decide

theorem mixed_type_completable : EquivalenceTriangle false true false := by decide

theorem same_type_forces_base :
    ∀ b : Bool, EquivalenceTriangle b true true ↔ b = true := by decide

theorem mixed_type_forces_base :
    ∀ b : Bool, EquivalenceTriangle b true false ↔ b = false := by decide

theorem no_common_socle_completion :
    ¬ ∃ b : Bool, EquivalenceTriangle b true true ∧
      EquivalenceTriangle b true false := by decide

/-- An antichain with two nodes cannot embed into a chain, even after changing levels. -/
theorem antichain_not_order_reflected_in_chain (f : Bool → Nat)
    (reflects : ∀ x y, f x ≤ f y → x = y) : False := by
  by_cases h : f false ≤ f true
  · have bad := reflects false true h
    cases bad
  · have h' : f true ≤ f false := by omega
    have bad := reflects true false h'
    cases bad

end AllThoseBigRamsey.CompletionTransport
