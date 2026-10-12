import Std

/-!
# Uniform repair of triangle constraints

The three laws below give an arbitrary-base construction, not a bounded-base
search. `Problem` makes every geometric/prescribed-type premise explicit.
The manuscript derives these premises from a full-type amalgamation request.
That class-level interpretation is not yet encoded in this library.
-/
namespace AllThoseBigRamsey.TriangleRepair

universe u v w z

structure Laws {C : Type u} (T : C → C → C → Prop)
    (repair : C → C → C → C) : Prop where
  lands : ∀ c a h, T c a (repair c a h)
  fixes : ∀ c a h, T c a h → repair c a h = h
  pairs : ∀ c a a' h h' t, T a a' t → T h h' t →
    T (repair c a h) (repair c a' h') t

structure Problem (C : Type u) (Q : Type v) (B : Type w) (P : Type z) where
  triangle : C → C → C → Prop
  cyclic : ∀ a b c, triangle a b c → triangle b c a
  edge : B → B → C
  base : B → C
  profile : Q → B → C
  pair : Q → Q → C → Prop
  protected : P → Q
  prescribed : P → C
  initial : Q → C
  baseTriangle : ∀ b b', b ≠ b' → triangle (base b) (edge b b') (base b')
  profileTriangle : ∀ q b b', b ≠ b' →
    triangle (profile q b) (edge b b') (profile q b')
  profilePair : ∀ q q' t, pair q q' t → ∀ b,
    triangle (profile q b) (profile q' b) t
  protectedFits : ∀ p b, triangle (base b) (profile (protected p) b) (prescribed p)
  initialPair : ∀ q q' t, pair q q' t → triangle (initial q) (initial q') t
  initialFixed : ∀ p, initial (protected p) = prescribed p

namespace Problem
variable {C : Type u} {Q : Type v} {B : Type w} {P : Type z}
variable (D : Problem C Q B P) (repair : C → C → C → C)

def Fits (H : Q → C) (b : B) : Prop :=
  ∀ q, D.triangle (D.base b) (D.profile q b) (H q)

def Pairs (H : Q → C) : Prop :=
  ∀ q q' t, D.pair q q' t → D.triangle (H q) (H q') t

def Fixed (H : Q → C) : Prop :=
  ∀ p, H (D.protected p) = D.prescribed p

def step (b : B) (H : Q → C) : Q → C :=
  fun q => repair (D.base b) (D.profile q b) (H q)

variable (laws : Laws D.triangle repair)

theorem step_fits (b : B) (H : Q → C) : D.Fits (D.step repair b H) b := by
  intro q
  exact laws.lands _ _ _

theorem step_pairs (b : B) (H : Q → C) (h : D.Pairs H) :
    D.Pairs (D.step repair b H) := by
  intro q q' t ht
  exact laws.pairs _ _ _ _ _ _ (D.profilePair q q' t ht b) (h q q' t ht)

theorem step_fixed (b : B) (H : Q → C) (h : D.Fixed H) :
    D.Fixed (D.step repair b H) := by
  intro p
  change repair (D.base b) (D.profile (D.protected p) b) (H (D.protected p)) = _
  rw [h p]
  exact laws.fixes _ _ _ (D.protectedFits p b)

theorem step_preserves_fits (b b' : B) (H : Q → C) (h : D.Fits H b') :
    D.Fits (D.step repair b H) b' := by
  by_cases he : b = b'
  · subst b'
    exact D.step_fits repair laws b H
  · intro q
    have hf := laws.fixes (D.base b) (D.edge b b') (D.base b')
      (D.baseTriangle b b' he)
    have hp := laws.pairs (D.base b) (D.profile q b) (D.edge b b')
      (H q) (D.base b') (D.profile q b')
      (D.profileTriangle q b b' he)
      (D.cyclic _ _ _ (D.cyclic _ _ _ (h q)))
    rw [hf] at hp
    exact D.cyclic _ _ _ hp

/-- Process a finite list of anchors; no bound on its length is imposed. -/
def run : List B → (Q → C) → (Q → C)
  | [], H => H
  | b :: bs, H => D.run repair bs (D.step repair b H)

theorem run_pairs (bs : List B) (H : Q → C) (h : D.Pairs H) :
    D.Pairs (D.run repair bs H) := by
  induction bs generalizing H with
  | nil => exact h
  | cons b bs ih =>
    exact ih (D.step repair b H) (D.step_pairs repair laws b H h)

theorem run_fixed (bs : List B) (H : Q → C) (h : D.Fixed H) :
    D.Fixed (D.run repair bs H) := by
  induction bs generalizing H with
  | nil => exact h
  | cons b bs ih =>
    exact ih (D.step repair b H) (D.step_fixed repair laws b H h)

theorem run_preserves_fits (bs : List B) (H : Q → C) (b : B) (h : D.Fits H b) :
    D.Fits (D.run repair bs H) b := by
  induction bs generalizing H with
  | nil => exact h
  | cons a bs ih =>
    exact ih (D.step repair a H) (D.step_preserves_fits repair laws a b H h)

theorem run_fits_mem (bs : List B) (H : Q → C) (b : B) (hb : b ∈ bs) :
    D.Fits (D.run repair bs H) b := by
  induction bs generalizing H with
  | nil => simp at hb
  | cons a bs ih =>
    rcases List.mem_cons.mp hb with he | ht
    · subst b
      exact D.run_preserves_fits repair laws bs (D.step repair a H) a
        (D.step_fits repair laws a H)
    · exact ih (D.step repair a H) ht

/-- Uniform constraint solution for an arbitrary finite list of base vertices. -/
theorem extension (bs : List B) :
    D.Pairs (D.run repair bs D.initial) ∧
    D.Fixed (D.run repair bs D.initial) ∧
    ∀ b, b ∈ bs → D.Fits (D.run repair bs D.initial) b := by
  exact ⟨D.run_pairs repair laws bs D.initial D.initialPair,
    D.run_fixed repair laws bs D.initial D.initialFixed,
    fun b hb => D.run_fits_mem repair laws bs D.initial b hb⟩

end Problem
end AllThoseBigRamsey.TriangleRepair
