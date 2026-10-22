import AllThoseBigRamsey.OneTypeCompletion

/-!
# Realizable-or-candidate repair of full syntactic singleton types

For a class with unique closed free amalgams, the inserted one-type is
forced to be the neutral/free type on every type realizable in a closed
continuation. On nonrealizable syntactic types, use the old unrestricted
candidate map. This preserves the commuting square on ALL syntactic
one-types if realizability is reflected by the source-to-base type map.

The relative realization/reflection property and the fact that neutral
completion stays in the chosen strong class are mathematical lemmas in
the manuscript; they remain explicit mathematical hypotheses, not declarations here.

This code validates the exact unrestricted/full syntactic extension
and the one-type composition argument in the existing relational API.
For an extension by a whole finite closed block, the manuscript uses
the corresponding exact-support rule on mixed relational atoms.
-/
namespace AllThoseBigRamsey.RigidClosedHybrid

open OneTypeCompletion

variable {L : Language} {α : Type} {A : RelStructure L α}

/-- On realizable types use the forced neutral/free amalgam.
On invalid syntactic types keep the original unrestricted map. -/
noncomputable def choose
    (B : FullType A 1)
    (Realizable : FullType A 1 → Prop)
    (G0 : FullType A 1 → FullType B.diagram 1)
    (p : FullType A 1) : FullType B.diagram 1 := by
  classical
  exact if Realizable p then OneTypeCompletion.neutral B p else G0 p

theorem choose_eq_neutral_of_realizable
    (B : FullType A 1)
    (Realizable : FullType A 1 → Prop)
    (G0 : FullType A 1 → FullType B.diagram 1)
    (p : FullType A 1) (hp : Realizable p) :
    choose B Realizable G0 p = OneTypeCompletion.neutral B p := by
  simp [choose, hp]

theorem choose_eq_candidate_of_invalid
    (B : FullType A 1)
    (Realizable : FullType A 1 → Prop)
    (G0 : FullType A 1 → FullType B.diagram 1)
    (p : FullType A 1) (hp : ¬ Realizable p) :
    choose B Realizable G0 p = G0 p := by
  simp [choose, hp]

/-- The hybrid map preserves the old atoms when the unrestricted candidate
preserves and reflects the old type's entire diagram. -/
theorem choose_extends_old
    (B : FullType A 1)
    (Realizable : FullType A 1 → Prop)
    (G0 : FullType A 1 → FullType B.diagram 1)
    (hG0 : ∀ p, OneTypeCompletion.Extends B p (G0 p))
    (p : FullType A 1) :
    OneTypeCompletion.Extends B p (choose B Realizable G0 p) := by
  classical
  by_cases hv : Realizable p
  · rw [choose_eq_neutral_of_realizable B Realizable G0 p hv]
    exact OneTypeCompletion.neutral_extends B p
  · rw [choose_eq_candidate_of_invalid B Realizable G0 p hv]
    exact hG0 p

/-- This is the precise all-syntactic-types square argument.
The first type map F is composed with the hybrid map; the enlarged
map F' is prescribed. The invalid case follows from the original
candidate; the valid case follows from unique free closed amalgamation.
-/
theorem choose_commutes
    {Source : Type}
    (B : FullType A 1)
    (Realizable : FullType A 1 → Prop)
    (SourceRealizable : Source → Prop)
    (F : Source → FullType A 1)
    (F' : Source → FullType B.diagram 1)
    (G0 : FullType A 1 → FullType B.diagram 1)
    (hReflect : ∀ p, Realizable (F p) ↔ SourceRealizable p)
    (hValid : ∀ p, SourceRealizable p →
        OneTypeCompletion.neutral B (F p) = F' p)
    (hCandidate : ∀ p, G0 (F p) = F' p) :
    (fun p => choose B Realizable G0 (F p)) = F' := by
  funext p
  by_cases hp : SourceRealizable p
  · rw [choose_eq_neutral_of_realizable B Realizable G0 (F p)
          ((hReflect p).mpr hp)]
    exact hValid p hp
  · rw [choose_eq_candidate_of_invalid B Realizable G0 (F p)
          (fun hv => hp ((hReflect p).mp hv))]
    exact hCandidate p

end AllThoseBigRamsey.RigidClosedHybrid
