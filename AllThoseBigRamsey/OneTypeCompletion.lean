import AllThoseBigRamsey.FullTypes

/-!
# Completing a partial prescription on full one-types

This file uses the actual `FullType` relational diagrams. It constructs a
neutral amalgam over a common base and totalises any partial prescription.
There is no class-membership assertion. In a binary language, the written
manuscript proof turns this into an unrestricted type-respecting insertion.
Higher-arity coherent families require the exact-support construction in the
manuscript; choosing the whole type at once does not suffice there.
-/
namespace AllThoseBigRamsey.OneTypeCompletion

variable {L : Language} {α : Type} {A : RelStructure L α}

/-- Include the old base and old future vertex, skipping the inserted vertex. -/
def old : Sum α (Fin 1) → Sum (Sum α (Fin 1)) (Fin 1)
  | .inl a => .inl (.inl a)
  | .inr i => .inr i

/-- This projection is used only on tuples with no future vertex. -/
def toBase : Sum (Sum α (Fin 1)) (Fin 1) → Sum α (Fin 1)
  | .inl b => b
  | .inr _ => .inr 0

/-- This projection is used only on tuples with no inserted vertex. -/
def toOld : Sum (Sum α (Fin 1)) (Fin 1) → Sum α (Fin 1)
  | .inl (.inl a) => .inl a
  | .inl (.inr _) => .inr 0
  | .inr i => .inr i

def HitsInserted {d : Nat} (q : Fin d → Sum (Sum α (Fin 1)) (Fin 1)) : Prop :=
  ∃ i j, q i = Sum.inl (Sum.inr j)

def HitsFuture {d : Nat} (q : Fin d → Sum (Sum α (Fin 1)) (Fin 1)) : Prop :=
  ∃ i j, q i = Sum.inr j

theorem no_inserted_old {d : Nat} (q : Fin d → Sum α (Fin 1)) :
    ¬ HitsInserted (fun i => old (q i)) := by
  rintro ⟨i, j, h⟩
  cases hq : q i <;> simp [old, hq] at h

theorem no_future_base {d : Nat} (q : Fin d → Sum α (Fin 1)) :
    ¬ HitsFuture (fun i => Sum.inl (q i)) := by
  rintro ⟨i, j, h⟩
  cases h

@[simp] theorem toOld_old (x : Sum α (Fin 1)) : toOld (old x) = x := by
  cases x <;> rfl

/-- Copy each side and set every genuinely mixed inserted/future tuple false. -/
noncomputable def neutralRel (B p : FullType A 1)
    (R : L.Symbol) (q : Fin (L.arity R) → Sum (Sum α (Fin 1)) (Fin 1)) : Prop := by
  classical
  exact if HitsInserted q then
    if HitsFuture q then False else B.diagram.rel R (fun i => toBase (q i))
  else p.diagram.rel R (fun i => toOld (q i))

theorem neutral_base (B p : FullType A 1) (R : L.Symbol)
    (q : Fin (L.arity R) → Sum α (Fin 1)) :
    neutralRel B p R (fun i => Sum.inl (q i)) ↔ B.diagram.rel R q := by
  classical
  by_cases hz : HitsInserted (fun i => Sum.inl (q i))
  · simp only [neutralRel, if_pos hz, if_neg (no_future_base q), toBase]
  · simp only [neutralRel, if_neg hz]
    have hb (i : Fin (L.arity R)) : ∃ a, q i = Sum.inl a := by
      cases hq : q i with
      | inl a => exact ⟨a, rfl⟩
      | inr j =>
          exact False.elim (hz ⟨i, j, congrArg Sum.inl hq⟩)
    let a := fun i => Classical.choose (hb i)
    have ha : q = fun i => Sum.inl (a i) :=
      funext (fun i => Classical.choose_spec (hb i))
    rw [ha]
    change p.diagram.rel R (fun i => Sum.inl (a i)) ↔
      B.diagram.rel R (fun i => Sum.inl (a i))
    exact (p.over_base R a).trans (B.over_base R a).symm

noncomputable def neutral (B p : FullType A 1) : FullType B.diagram 1 where
  diagram := ⟨neutralRel B p⟩
  over_base := neutral_base B p

/-- Preservation and reflection of every old relation, including non-relations. -/
def Extends (B p : FullType A 1) (q : FullType B.diagram 1) : Prop :=
  ∀ R a, q.diagram.rel R (fun i => old (a i)) ↔ p.diagram.rel R a

theorem neutral_extends (B p : FullType A 1) : Extends B p (neutral B p) := by
  intro R a
  simp only [neutral, neutralRel, if_neg (no_inserted_old a), toOld_old]

/-- Complete a prescription on any set of full one-types, not only valid types. -/
noncomputable def complete (B : FullType A 1) (S : FullType A 1 → Prop)
    (θ : (p : FullType A 1) → S p → FullType B.diagram 1)
    (p : FullType A 1) : FullType B.diagram 1 := by
  classical
  exact if hp : S p then θ p hp else neutral B p

theorem complete_prescribed (B : FullType A 1) (S : FullType A 1 → Prop)
    (θ : (p : FullType A 1) → S p → FullType B.diagram 1)
    (p : FullType A 1) (hp : S p) : complete B S θ p = θ p hp := by
  simp only [complete, dif_pos hp]

theorem complete_extends (B : FullType A 1) (S : FullType A 1 → Prop)
    (θ : (p : FullType A 1) → S p → FullType B.diagram 1)
    (hθ : ∀ p hp, Extends B p (θ p hp)) (p : FullType A 1) :
    Extends B p (complete B S θ p) := by
  classical
  by_cases hp : S p
  · rw [complete_prescribed B S θ p hp]
    exact hθ p hp
  · simp only [complete, dif_neg hp]
    exact neutral_extends B p

end AllThoseBigRamsey.OneTypeCompletion
