import PseudotreeValidation.LowerGeometry

/-!
# The turn step in diary unavoidability

A point on the selected ambient ray has a later point on the same ray.
An opposite-cone point in the *source* self-copy, transported by meet
preservation, therefore enters the literal `1` cone of the selected point.
A whole source interval does so, and contains the required single-ray
rational suborder. No assumption that arbitrary embeddings preserve rays
is made.
-/

namespace AllThoseBigRamsey.Pseudotree

open FirstOrder
open scoped FirstOrder

namespace RayTree

@[simp] theorem coneCode_onRay (stem : List BinaryRay) (a b : BinaryRay) :
    coneCode (onRay stem a) (onRay stem b) = false := by
  induction stem with
  | nil => rfl
  | cons c stem ih => exact ih

/-- The second cone of the block model is precisely the literal `1` cone. -/
theorem cone_true_prefix {s t : TernaryModel} (hst : s < t)
    (hcone : coneCode s t = true) :
    fromBlocks s ++ [.one] <+: fromBlocks t := by
  induction s generalizing t with
  | point a =>
      cases t with
      | point b => simp [coneCode] at hcone
      | above b t =>
          have hab : a = b := by simpa [coneCode] using hcone
          subst b
          refine ⟨fromBlocks t, ?_⟩
          simp [fromBlocks, RayTree.map, printWord]
  | above a s ih =>
      cases t with
      | point b => exact False.elim (not_above_le_point a b s hst.le)
      | above b t =>
          obtain ⟨rfl, hst'⟩ := (above_lt_above a b s t).mp hst
          obtain ⟨tail, htail⟩ := ih hst' hcone
          refine ⟨tail, ?_⟩
          simpa only [fromBlocks, RayTree.map, printWord, List.append_assoc,
            List.cons_append] using
              congrArg (fun w => a.word.map binaryLetter ++ .one :: w) htail

/-- If a same-ray successor and another successor meet exactly at the base,
the other successor lies above the literal `1` child. -/
theorem prefix_one_of_opposite_to_ray {s r t : TernaryModel}
    (hsr : s < r) (hst : s < t)
    (hray : rayStem s = rayStem r) (hmeet : t ⊓ r = s) :
    fromBlocks s ++ [.one] <+: fromBlocks t := by
  have hsame : coneCode s r = false := by
    conv_lhs => rw [← onRay_stem_value s, ← onRay_stem_value r]
    rw [hray, coneCode_onRay]
  have hdiff : coneCode s t ≠ false := by
    intro hfalse
    have hlt : s < t ⊓ r := (lt_inf_iff_coneCode_eq hst hsr).mpr (hfalse.trans hsame.symm)
    rw [hmeet] at hlt
    exact (lt_irrefl s) hlt
  apply cone_true_prefix hst
  cases h : coneCode s t
  · exact False.elim (hdiff h)
  · rfl

end RayTree

namespace LowerGeometry.RayCopy

/-- The turn needed for either diary event `(c)` or `(d)` is available in
every actual functional self-copy containing the current ray copy. -/
theorem opposite_continuation (Q : LowerGeometry.RayCopy)
    (f : TernaryModel ↪[language] TernaryModel)
    (hQ : Set.range Q.embedding ⊆ Set.range f) (q : ℚ) :
    ∃ R : LowerGeometry.RayCopy, Set.range R.embedding ⊆ Set.range f ∧
      ∀ t, Q q < R t ∧ fromBlocks (Q q) ++ [.one] <+: fromBlocks (R t) := by
  let r : ℚ := q + 1
  have hqr : q < r := lt_add_of_pos_right q zero_lt_one
  obtain ⟨a, ha⟩ := hQ ⟨q, rfl⟩
  obtain ⟨b, hb⟩ := hQ ⟨r, rfl⟩
  have hab : a < b := (embedding_lt_iff f a b).mp (by
    rw [ha, hb]
    exact Q.embedding.strictMono hqr)
  obtain ⟨c, hac, hcb⟩ := RayTree.exists_opposite_cone hab
  obtain ⟨R, hR⟩ := LowerGeometry.interval_rayCopy (embeddingOrderEmbedding f) hac
  refine ⟨R, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨z, _, _, hz⟩ := hR t
    exact ⟨z, hz.symm⟩
  · intro t
    obtain ⟨z, haz, hzc, hz⟩ := hR t
    have hlt : Q q < R t := by
      rw [hz, ← ha]
      exact (embedding_lt_iff f a z).mpr haz
    refine ⟨hlt, ?_⟩
    have hzb : z ⊓ b = a := by
      apply le_antisymm
      · calc z ⊓ b ≤ c ⊓ b := inf_le_inf_right b hzc.le
             _ = a := hcb
      · exact le_inf haz.le hab.le
    have hmeet : R t ⊓ Q r = Q q := by
      rw [hz, ← hb, ← ha]
      change f z ⊓ f b = f a
      rw [← embedding_map_inf f z b, hzb]
    exact RayTree.prefix_one_of_opposite_to_ray (Q.embedding.strictMono hqr) hlt
      ((Q.same_ray q).trans (Q.same_ray r).symm) hmeet

end LowerGeometry.RayCopy
end AllThoseBigRamsey.Pseudotree
