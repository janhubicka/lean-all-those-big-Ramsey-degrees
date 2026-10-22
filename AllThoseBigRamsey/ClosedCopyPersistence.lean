import Std

/-!
# Age indivisibility: finite partition extraction

This file verifies the combinatorial step in the closed-copy extension
of Sauer's persistence argument. An age is a predicate on finite
configurations and subsets of a collection of copies. The lemma says:
if one part of every finite partition realizes the whole age, and
the first n parts each omit some configuration from it, then the
remaining part realizes the whole age.

The actual finite closed-hull configurations, minimal parameter
witness colouring and strong-copy cofinality remain manuscript
definitions and proofs, not axioms of an end-to-end Lean theorem.
-/
namespace AllThoseBigRamsey.ClosedCopyPersistence

universe u v

variable {X : Type u} {Configuration : Type v}

/-- The copies of interest whose colour is i. -/
def part (Y : X → Prop) {n : Nat} (colour : X → Fin (n+1))
    (i : Fin (n+1)) : X → Prop :=
  fun x => Y x ∧ colour x = i

/-- Age indivisibility of a family, in terms of realization of all
finite configurations after some colour class has been selected. -/
def AgeIndivisible (Occurs : (X → Prop) → Configuration → Prop)
    (Y : X → Prop) : Prop :=
  ∀ n (colour : X → Fin (n+1)),
    ∃ i : Fin (n+1), ∀ D,
      Occurs Y D ↔ Occurs (part Y colour i) D

/-- Any other part of a finite partition omits a configuration from
the original age, so the last part retains the whole age. -/
theorem last_part_full_age
    (Occurs : (X → Prop) → Configuration → Prop)
    (Y : X → Prop) (hAge : AgeIndivisible Occurs Y)
    (n : Nat) (colour : X → Fin (n+1))
    (hbad : ∀ j : Fin n,
      ∃ D : Configuration, Occurs Y D ∧
        ¬ Occurs (part Y colour j.castSucc) D) :
    ∀ D, Occurs Y D ↔
      Occurs (part Y colour (Fin.last n)) D := by
  obtain ⟨i, hi⟩ := hAge n colour
  by_cases hlast : i = Fin.last n
  · simpa only [hlast] using hi
  · have hne : i.val ≠ n := by
      intro hv
      apply hlast
      apply Fin.ext
      exact hv
    have ilt : i.val < n := by omega
    let j : Fin n := ⟨i.val, ilt⟩
    have hcast : j.castSucc = i := Fin.ext rfl
    obtain ⟨D, hD, hno⟩ := hbad j
    have hp : Occurs (part Y colour i) D := (hi D).mp hD
    have hj : Occurs (part Y colour j.castSucc) D := by
      simpa only [hcast] using hp
    exact False.elim (hno hj)

/-- The colour class predicted by indivisibility can only be
a class not known to omit a pattern. -/
theorem no_full_age_bad_colour
    (Occurs : (X → Prop) → Configuration → Prop)
    (Y : X → Prop) {n : Nat} (colour : X → Fin (n+1))
    (hbad : ∀ j : Fin n,
      ∃ D : Configuration, Occurs Y D ∧
        ¬ Occurs (part Y colour j.castSucc) D)
    (i : Fin (n+1))
    (hi : ∀ D, Occurs Y D ↔ Occurs (part Y colour i) D) :
    i = Fin.last n := by
  by_cases hlast : i = Fin.last n
  · exact hlast
  · have hne : i.val ≠ n := by
      intro hv
      exact hlast (Fin.ext hv)
    have ilt : i.val < n := by omega
    let j : Fin n := ⟨i.val, ilt⟩
    have he : j.castSucc = i := Fin.ext rfl
    obtain ⟨D, hD, hno⟩ := hbad j
    exact False.elim (hno (by simpa only [he] using (hi D).mp hD))

end AllThoseBigRamsey.ClosedCopyPersistence
