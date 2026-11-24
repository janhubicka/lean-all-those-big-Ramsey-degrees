import PseudotreeValidation.LowerLayers
import PseudotreeValidation.SparseLex

/-! Canonical parents and lexicographic order for the realization frontier. -/

namespace AllThoseBigRamsey.Pseudotree.LowerRealization

variable {D : PaperDiary n} {height j : Nat}

def parent (T : PaperTreeAxioms D.nodes D.codes height) (v : Level D (j + 1)) : Level D j :=
  ⟨v.val.take j,
    T.prefix_closed v.val v.property.1 j (by rw [v.property.2]; omega),
    by simp [v.property.2]⟩

def last (v : Level D (j + 1)) : Fin 3 := v.val[j]'(by rw [v.property.2]; omega)

theorem child_parent (T : PaperTreeAxioms D.nodes D.codes height) (v : Level D (j + 1)) :
    child (parent T v).val (last v) = v.val := by
  change v.val.take j ++ [v.val[j]'(by rw [v.property.2]; omega)] = v.val
  rw [List.take_append_getElem]
  exact List.take_of_length_le (by rw [v.property.2])

theorem parent_child_mem (T : PaperTreeAxioms D.nodes D.codes height) (v : Level D (j + 1)) :
    child (parent T v).val (last v) ∈ D.nodes := by
  rw [child_parent]
  exact v.property.1

theorem childNode_parent (T : PaperTreeAxioms D.nodes D.codes height) (v : Level D (j + 1)) :
    childNode (parent T v) (last v) (parent_child_mem T v) = v :=
  Subtype.ext (child_parent T v)

@[simp] theorem parent_childNode (T : PaperTreeAxioms D.nodes D.codes height)
    (u : Level D j) (a : Fin 3) (ha : child u.val a ∈ D.nodes) :
    parent T (childNode u a ha) = u := by
  apply Subtype.ext
  have h := child_parent T (childNode u a ha)
  exact List.append_inj_left' h rfl

@[simp] theorem last_childNode (T : PaperTreeAxioms D.nodes D.codes height)
    (u : Level D j) (a : Fin 3) (ha : child u.val a ∈ D.nodes) :
    last (childNode u a ha) = a := by
  have h := child_parent T (childNode u a ha)
  rw [parent_childNode] at h
  have hsingle := List.append_cancel_left h
  exact List.singleton_inj.mp hsingle

theorem child_lt_same_iff (u : DiaryWord) (a b : Fin 3) :
    child u a < child u b ↔ a < b := by
  induction u with
  | nil => exact List.lex_singleton_iff a b
  | cons c u ih =>
    change List.Lex (· < ·) (c :: child u a) (c :: child u b) ↔ a < b
    rw [List.lex_cons_iff]
    exact ih

/-- Ordered distinct roots keep their order under arbitrary extensions;
children of the same root are ordered by their retained first letters. -/
theorem ordered_children (T : PaperTreeAxioms D.nodes D.codes height)
    (roots : Level D j → List TernaryLetter) (k : Nat)
    (hlen : ∀ u, (roots u).length = k)
    (hord : ∀ u v, u.val < v.val → Sparse.lexLess (roots u) (roots v) = true)
    (q : Level D (j + 1) → List TernaryLetter)
    (hp : ∀ u a (ha : child u.val a ∈ D.nodes),
      (roots u ++ [RayMapModel.toLetter a]).IsPrefix (q (childNode u a ha))) :
    ∀ v w, v.val < w.val → Sparse.lexLess (q v) (q w) = true := by
  intro v w hvw
  have hvp := hp (parent T v) (last v) (parent_child_mem T v)
  have hwp := hp (parent T w) (last w) (parent_child_mem T w)
  rw [childNode_parent] at hvp hwp
  obtain ⟨sv, hsv⟩ := hvp
  obtain ⟨sw, hsw⟩ := hwp
  have hsource : child (parent T v).val (last v) < child (parent T w).val (last w) := by
    rw [child_parent, child_parent]
    exact hvw
  rcases lt_trichotomy (parent T v).val (parent T w).val with hlt | heq | hgt
  · have hr := hord (parent T v) (parent T w) hlt
    have hne : roots (parent T v) ≠ roots (parent T w) := by
      intro he
      rw [he, Sparse.lexLess_self] at hr
      contradiction
    rw [← hsv, ← hsw]
    simp only [List.append_assoc, List.singleton_append]
    rw [Sparse.lexLess_append_of_ne ((hlen _).trans (hlen _).symm) hne]
    exact hr
  · have hparents : parent T v = parent T w := Subtype.ext heq
    rw [hparents] at hsource
    have hletters : last v < last w := (child_lt_same_iff _ _ _).mp hsource
    rw [← hsv, ← hsw, hparents]
    simp only [List.append_assoc, List.singleton_append, Sparse.lexLess_common_prefix,
      Sparse.lexLess, Sparse.rank_toLetter]
    have hval : (last v).val < (last w).val := hletters
    simp [Nat.ne_of_lt hval, hval]
  · have hrev := child_lt_child_of_lt hgt
      ((parent T w).property.2.trans (parent T v).property.2.symm) (last w) (last v)
    exact False.elim (not_lt_of_gt hsource hrev)

end AllThoseBigRamsey.Pseudotree.LowerRealization
