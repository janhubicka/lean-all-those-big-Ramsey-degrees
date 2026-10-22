import AllThoseBigRamsey.ClosedCopyPersistence

/-!
# Vertex Ramsey property implies age indivisibility

The manuscript's family of minimal closed extension blocks is encoded
by a derived finite relational free-amalgamation class. The
Evans--Hubicka--Nesetril ordered Ramsey theorem gives the
finite vertex-Ramsey property of that class.

This module verifies the final purely combinatorial deduction:
joint embedding of finitely many finite patterns plus vertex Ramsey
implies that some class in every finite colouring has the full age.
The derivation of the block class and its Ramsey theorem is a
separate written manuscript proof, not asserted in Lean.
-/
namespace AllThoseBigRamsey.MinimalBlockAge

open ClosedCopyPersistence

universe u v
variable {X : Type u} {Pattern : Type v}

/-- Realisation of patterns is monotone under inclusion of families. -/
def MonotoneOccurs (Occurs : (X → Prop) → Pattern → Prop) : Prop :=
  ∀ S T, (∀ x, S x → T x) →
    ∀ F, Occurs S F → Occurs T F

/-- Occurrence of a larger pattern forces occurrence of each
pattern embedded in it. -/
def RestrictionOccurs
    (Occurs : (X → Prop) → Pattern → Prop)
    (Embeds : Pattern → Pattern → Prop) : Prop :=
  ∀ S F G, Embeds F G → Occurs S G → Occurs S F

/-- Any finite collection of patterns occurring in Y has a
common extension that occurs in Y. -/
def JointPatterns
    (Occurs : (X → Prop) → Pattern → Prop)
    (Embeds : Pattern → Pattern → Prop)
    (Y : X → Prop) : Prop :=
  ∀ n (Fs : Fin (n+1) → Pattern),
    (∀ i, Occurs Y (Fs i)) →
    ∃ G, Occurs Y G ∧ ∀ i, Embeds (Fs i) G

/-- For every pattern occurring in Y, a monochromatic copy
exists under any finite colouring of members of Y. -/
def VertexRamsey
    (Occurs : (X → Prop) → Pattern → Prop)
    (Y : X → Prop) : Prop :=
  ∀ n G, Occurs Y G →
    ∀ colour : X → Fin (n+1),
      ∃ i, Occurs (part Y colour i) G

/-- Finite vertex Ramsey and joint embedding imply age indivisibility.
A full-age part is the same part for ALL finite configurations. -/
theorem ageIndivisible_of_vertexRamsey
    (Occurs : (X → Prop) → Pattern → Prop)
    (Embeds : Pattern → Pattern → Prop)
    (Y : X → Prop)
    (hm : MonotoneOccurs Occurs)
    (hr : RestrictionOccurs Occurs Embeds)
    (hj : JointPatterns Occurs Embeds Y)
    (hv : VertexRamsey Occurs Y) :
    AgeIndivisible Occurs Y := by
  classical
  intro n colour
  by_cases hgood :
      ∃ i : Fin (n+1), ∀ G, Occurs Y G →
        Occurs (part Y colour i) G
  · obtain ⟨i, hi⟩ := hgood
    refine ⟨i, ?_⟩
    intro G
    constructor
    · exact hi G
    · exact hm _ _ (fun x hx => hx.1) G
  · have hbad :
        ∀ i : Fin (n+1), ∃ G, Occurs Y G ∧
          ¬ Occurs (part Y colour i) G := by
      intro i
      have hnot :
          ¬ ∀ G, Occurs Y G → Occurs (part Y colour i) G := by
        intro h
        exact hgood ⟨i, h⟩
      obtain ⟨G, hG⟩ := Classical.not_forall.mp hnot
      have hOccurs : Occurs Y G := by
        by_cases h : Occurs Y G
        · exact h
        · exact False.elim (hG (fun h' => False.elim (h h')))
      refine ⟨G, hOccurs, ?_⟩
      intro ht
      exact hG (fun _ => ht)
    let Fs : Fin (n+1) → Pattern :=
      fun i => Classical.choose (hbad i)
    have hFs : ∀ i, Occurs Y (Fs i) := by
      intro i
      exact (Classical.choose_spec (hbad i)).1
    obtain ⟨G, hG, hEmbed⟩ := hj n Fs hFs
    obtain ⟨i, hmono⟩ := hv n G hG colour
    have hp : Occurs (part Y colour i) (Fs i) :=
      hr _ _ _ (hEmbed i) hmono
    exact False.elim ((Classical.choose_spec (hbad i)).2 hp)

/-- Every colour but the last omits a pattern: explicit special case. -/
theorem last_part_full_age_of_vertexRamsey
    (Occurs : (X → Prop) → Pattern → Prop)
    (Embeds : Pattern → Pattern → Prop)
    (Y : X → Prop)
    (hm : MonotoneOccurs Occurs)
    (hr : RestrictionOccurs Occurs Embeds)
    (hj : JointPatterns Occurs Embeds Y)
    (hv : VertexRamsey Occurs Y)
    (n : Nat) (colour : X → Fin (n+1))
    (hbad : ∀ j : Fin n,
      ∃ G, Occurs Y G ∧
        ¬ Occurs (part Y colour j.castSucc) G) :
    ∀ G, Occurs Y G ↔
      Occurs (part Y colour (Fin.last n)) G := by
  exact last_part_full_age Occurs Y
    (ageIndivisible_of_vertexRamsey Occurs Embeds Y hm hr hj hv)
    n colour hbad

end AllThoseBigRamsey.MinimalBlockAge
