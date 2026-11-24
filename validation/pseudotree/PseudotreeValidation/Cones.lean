import PseudotreeValidation.ModelMathlib

/-!
# Exactly two cones in the block model

The code `false` denotes continuation along the current ray; `true` denotes
entry into the attached ray. The theorem `lt_inf_iff_coneCode_eq` identifies
this code with the manuscript's equivalence relation on strict upper nodes.
-/

namespace AllThoseBigRamsey.Pseudotree.RayTree

variable {α : Type u}

@[simp] theorem point_le_point [PartialOrder α] (a b : α) :
    (point a : RayTree α) ≤ point b ↔ a ≤ b := Iff.rfl

@[simp] theorem point_le_above [PartialOrder α] (a b : α) (t : RayTree α) :
    point a ≤ above b t ↔ a ≤ b := Iff.rfl

@[simp] theorem above_le_above [PartialOrder α] (a b : α) (s t : RayTree α) :
    above a s ≤ above b t ↔ a = b ∧ s ≤ t := Iff.rfl

@[simp] theorem not_above_le_point [PartialOrder α] (a b : α) (s : RayTree α) :
    ¬ above a s ≤ point b := id

@[simp] theorem point_lt_point [PartialOrder α] (a b : α) :
    (point a : RayTree α) < point b ↔ a < b := by
  simp only [lt_iff_le_and_ne, point_le_point, ne_eq, point.injEq]

@[simp] theorem point_lt_above [PartialOrder α] (a b : α) (t : RayTree α) :
    point a < above b t ↔ a ≤ b := by
  simp only [lt_iff_le_and_ne, point_le_above, ne_eq, reduceCtorEq, not_false_eq_true,
    and_true]

@[simp] theorem above_lt_above [PartialOrder α] (a b : α) (s t : RayTree α) :
    above a s < above b t ↔ a = b ∧ s < t := by
  constructor
  · intro h
    obtain ⟨hab, hst⟩ := (above_le_above a b s t).1 h.le
    subst b
    exact ⟨rfl, lt_of_le_of_ne hst (fun heq => h.ne (congrArg (above a) heq))⟩
  · rintro ⟨rfl, hst⟩
    exact lt_of_le_of_ne ⟨rfl, hst.le⟩ (fun heq => hst.ne (above.inj heq).2)

@[simp] theorem point_inf_point [LinearOrder α] (a b : α) :
    (point a : RayTree α) ⊓ point b = point (min a b) := rfl

@[simp] theorem point_inf_above [LinearOrder α] (a b : α) (t : RayTree α) :
    point a ⊓ above b t = point (min a b) := rfl

@[simp] theorem above_inf_point [LinearOrder α] (a b : α) (s : RayTree α) :
    above a s ⊓ point b = point (min a b) := rfl

@[simp] theorem above_inf_same [LinearOrder α] (a : α) (s t : RayTree α) :
    above a s ⊓ above a t = above a (s ⊓ t) := by
  change meet min (above a s) (above a t) = _
  simp only [meet, ↓reduceIte]
  rfl

theorem above_inf_different [LinearOrder α] {a b : α} (hab : a ≠ b)
    (s t : RayTree α) : above a s ⊓ above b t = point (min a b) := by
  change meet min (above a s) (above b t) = _
  simp only [meet, hab, ↓reduceIte]

/-- The two cone labels. The value is only used when the second node is strictly
above the first. -/
def coneCode [DecidableEq α] : RayTree α → RayTree α → Bool
  | point _, point _ => false
  | point a, above b _ => decide (a = b)
  | above _ _, point _ => false
  | above _ s, above _ t => coneCode s t

/-- The cone labels are exactly the equivalence classes defined by meet above
its base point. This proves the at-most-two-cones part of the model lemma. -/
theorem lt_inf_iff_coneCode_eq [LinearOrder α] {s x y : RayTree α}
    (hx : s < x) (hy : s < y) :
    s < x ⊓ y ↔ coneCode s x = coneCode s y := by
  induction s generalizing x y with
  | point a =>
    cases x with
    | point b =>
      have hab : a < b := (point_lt_point a b).1 hx
      cases y with
      | point c =>
        have hac : a < c := (point_lt_point a c).1 hy
        simp only [point_inf_point, point_lt_point, coneCode]
        exact iff_true_intro (lt_min hab hac)
      | above c v =>
        have hac : a ≤ c := (point_lt_above a c v).1 hy
        by_cases heq : a = c
        · subst c
          simp [coneCode, min_eq_right hab.le]
        · have hac' : a < c := lt_of_le_of_ne hac heq
          simp only [point_inf_above, point_lt_point, coneCode, heq,
            decide_false]
          exact iff_true_intro (lt_min hab hac')
    | above b u =>
      have hab : a ≤ b := (point_lt_above a b u).1 hx
      cases y with
      | point c =>
        have hac : a < c := (point_lt_point a c).1 hy
        by_cases heq : a = b
        · subst b
          simp [coneCode, min_eq_left hac.le]
        · have hab' : a < b := lt_of_le_of_ne hab heq
          simp only [above_inf_point, point_lt_point, coneCode, heq,
            decide_false]
          exact iff_true_intro (lt_min hab' hac)
      | above c v =>
        have hac : a ≤ c := (point_lt_above a c v).1 hy
        by_cases heqb : a = b
        · subst b
          by_cases heqc : a = c
          · subst c
            simp [coneCode]
          · rw [above_inf_different heqc]
            simp [coneCode, heqc, min_eq_left hac]
        · by_cases heqc : a = c
          · subst c
            rw [above_inf_different (Ne.symm heqb)]
            simp [coneCode, heqb, min_eq_right hab]
          · have hab' : a < b := lt_of_le_of_ne hab heqb
            have hac' : a < c := lt_of_le_of_ne hac heqc
            have hmin : point a < (point (min b c) : RayTree α) :=
              (point_lt_point a (min b c)).2 (lt_min hab' hac')
            have hcommon : (point (min b c) : RayTree α) ≤ above b u ⊓ above c v :=
              le_inf (min_le_left _ _) (min_le_right _ _)
            have hlt := lt_of_lt_of_le hmin hcommon
            simp only [coneCode, heqb, heqc, decide_false]
            exact iff_true_intro hlt
  | above a s ih =>
    cases x with
    | point b => exact False.elim ((not_above_le_point a b s) hx.le)
    | above b u =>
      obtain ⟨rfl, hsu⟩ := (above_lt_above a b s u).1 hx
      cases y with
      | point c => exact False.elim ((not_above_le_point a c s) hy.le)
      | above c v =>
        obtain ⟨rfl, hsv⟩ := (above_lt_above a c s v).1 hy
        simpa only [above_inf_same, above_lt_above, true_and, coneCode] using ih hsu hsv

/-- Both cone labels occur when the ray has no greatest element. -/
theorem coneCode_surjective [LinearOrder α] [NoMaxOrder α] (s : RayTree α) :
    ∀ b : Bool, ∃ t, s < t ∧ coneCode s t = b := by
  induction s with
  | point a =>
    intro b
    cases b with
    | false =>
      obtain ⟨c, hac⟩ := NoMaxOrder.exists_gt a
      exact ⟨point c, (point_lt_point a c).2 hac, rfl⟩
    | true =>
      exact ⟨above a (point a), (point_lt_above a a _).2 le_rfl, by simp [coneCode]⟩
  | above a s ih =>
    intro b
    obtain ⟨t, hst, ht⟩ := ih b
    exact ⟨above a t, (above_lt_above a a s t).2 ⟨rfl, hst⟩, ht⟩

/-- Two representatives of exactly the two cones above every node. -/
theorem two_cones [LinearOrder α] [NoMaxOrder α] (s : RayTree α) :
    ∃ x y, s < x ∧ s < y ∧ x ⊓ y = s ∧
      ∀ z, s < z →
        (s < z ⊓ x ∨ s < z ⊓ y) ∧ ¬(s < z ⊓ x ∧ s < z ⊓ y) := by
  obtain ⟨x, hx, hcx⟩ := coneCode_surjective s false
  obtain ⟨y, hy, hcy⟩ := coneCode_surjective s true
  have hmeet : x ⊓ y = s := by
    have hle : s ≤ x ⊓ y := le_inf hx.le hy.le
    apply le_antisymm _ hle
    by_contra hnot
    have hlt : s < x ⊓ y := lt_iff_le_not_ge.mpr ⟨hle, hnot⟩
    have hcode := (lt_inf_iff_coneCode_eq hx hy).1 hlt
    simp [hcx, hcy] at hcode
  refine ⟨x, y, hx, hy, hmeet, ?_⟩
  intro z hz
  rw [lt_inf_iff_coneCode_eq hz hx, lt_inf_iff_coneCode_eq hz hy, hcx, hcy]
  cases coneCode s z <;> simp

end AllThoseBigRamsey.Pseudotree.RayTree
