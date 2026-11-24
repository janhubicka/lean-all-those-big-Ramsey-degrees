import AllThoseBigRamsey.Pseudotree.SparseFair
import AllThoseBigRamsey.Pseudotree.SparseMeet
import AllThoseBigRamsey.Pseudotree.RayMapModel

/-!
# Order geometry of the actual sparse queue

A binary tail added beyond an older word cannot change either comparison with
that word. Combined with the exact FIFO child equations, this proves density,
absence of endpoints, and two inhabited upper cones for the generated set.
-/

namespace AllThoseBigRamsey.Pseudotree.Sparse

open RayMapModel

private theorem noOne_iff_point (s : Word) :
    NoOne s ↔ ∃ b, parseWord s = .point b := by
  induction s with
  | nil => simp [parseWord]
  | cons a s ih =>
      cases h : parseWord s with
      | point b =>
          have hs : NoOne s := ih.mpr ⟨b, h⟩
          cases a <;> simp [parseWord, prependBlock, h, hs]
      | above b t =>
          have hs : ¬ NoOne s := by
            intro hbin
            obtain ⟨c, hc⟩ := ih.mp hbin
            rw [h] at hc
            cases hc
          cases a <;> simp [parseWord, prependBlock, h, hs]

private theorem below_cons_same (a : TernaryLetter) (s t : Word) :
    wordBelow (a :: s) (a :: t) ↔ wordBelow s t := by
  cases a <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp [wordBelow, parseWord, prependBlock, hs, ht, RayTree.Below, RayTree.first, binaryLE]

theorem below_common_prefix (p s t : Word) :
    wordBelow (p ++ s) (p ++ t) ↔ wordBelow s t := by
  induction p with
  | nil => rfl
  | cons a p ih => simpa only [List.cons_append, below_cons_same] using ih

private theorem below_nil_cons (a : TernaryLetter) (t : Word) :
    wordBelow [] (a :: t) ↔ a ≠ .two := by
  cases a <;> cases h : parseWord t <;>
    simp [wordBelow, parseWord, prependBlock, h, RayTree.first, binaryLE]

private theorem below_cons_nil (a : TernaryLetter) (s : Word) :
    wordBelow (a :: s) [] ↔ a = .two ∧ NoOne s := by
  rw [noOne_iff_point]
  cases a <;> cases h : parseWord s <;>
    simp [wordBelow, parseWord, prependBlock, h, RayTree.first, binaryLE]

private theorem below_cons_distinct (a b : TernaryLetter) (s t : Word)
    (hab : a ≠ b) : wordBelow (a :: s) (b :: t) ↔ a = .two ∧ NoOne s := by
  rw [noOne_iff_point]
  cases a <;> cases b <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp_all [wordBelow, parseWord, prependBlock, RayTree.first, binaryLE]

private theorem binaryMin_cons (a : Bool) (s t : List Bool) :
    binaryMin (a :: s) (a :: t) = a :: binaryMin s t := by
  simp only [binaryMin, binaryLE, beq_self_eq_true, ↓reduceIte]
  split <;> rfl

private theorem meet_prependBlock (a : Bool) (s t : RayTree (List Bool)) :
    RayTree.meet binaryMin (prependBlock a s) (prependBlock a t) =
      prependBlock a (RayTree.meet binaryMin s t) := by
  cases s <;> cases t <;>
    simp [prependBlock, RayTree.meet, binaryMin_cons]
  split <;> rfl

private theorem meet_cons_same (a : TernaryLetter) (s t : Word) :
    wordMeet (a :: s) (a :: t) = a :: wordMeet s t := by
  cases a
  · simp only [wordMeet, parseWord, meet_prependBlock, printWord_prependBlock]
    rfl
  · simp [wordMeet, parseWord, RayTree.meet, printWord]
  · simp only [wordMeet, parseWord, meet_prependBlock, printWord_prependBlock]
    rfl

theorem meet_common_prefix (p s t : Word) :
    wordMeet (p ++ s) (p ++ t) = p ++ wordMeet s t := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, meet_cons_same, ih]

/-- Appending any binary tail beyond the end of an older word preserves both
comparisons with that older word. -/
theorem shorter_binary_tail (c w b : Word) (hlen : c.length < w.length)
    (hb : .one ∉ b) :
    (wordBelow c (w ++ b) ↔ wordBelow c w) ∧
      (wordBelow (w ++ b) c ↔ wordBelow w c) := by
  have hbb : NoOne b := by
    intro a ha heq
    subst a
    exact hb ha
  induction c generalizing w with
  | nil =>
      cases w with
      | nil => simp at hlen
      | cons a w =>
          simp only [List.cons_append, below_nil_cons, below_cons_nil, noOne_append]
          simp [hbb]
  | cons a c ih =>
      cases w with
      | nil => simp at hlen
      | cons d w =>
          by_cases had : a = d
          · subst d
            simp only [List.cons_append, below_cons_same]
            exact ih w (by simpa using hlen)
          · have hda : d ≠ a := Ne.symm had
            simp only [List.cons_append, below_cons_distinct a d _ _ had,
              below_cons_distinct d a _ _ hda, noOne_append]
            simp [hbb]

/-- Different binary continuations of a word longer than `c` have the same
comparison profile with `c`. -/
theorem shorter_binary_tails (c w p q : Word) (hlen : c.length < w.length)
    (hp : .one ∉ p) (hq : .one ∉ q) :
    (wordBelow c (w ++ p) ↔ wordBelow c (w ++ q)) ∧
      (wordBelow (w ++ p) c ↔ wordBelow (w ++ q) c) := by
  obtain ⟨hp₁, hp₂⟩ := shorter_binary_tail c w p hlen hp
  obtain ⟨hq₁, hq₂⟩ := shorter_binary_tail c w q hlen hq
  exact ⟨hp₁.trans hq₁.symm, hp₂.trans hq₂.symm⟩

private theorem active_head (n : Nat) :
    ∃ u rest, (stage n).active = u :: rest ∧ u.length = 3 * n ∧ code n = u ++ [.zero, .two] := by
  have hn : (stage n).active ≠ [] := by
    intro heq
    have hlen := (stage_lengths n).1
    simp [heq] at hlen
  obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
  refine ⟨u, rest, ha, ?_, ?_⟩
  · exact active_length n u (by simp [ha])
  · simp [code, ha, List.head!, newCode]

/-- The first child stays in the old ray strictly above the selected code. -/
theorem code_upper_child (n : Nat) :
    wordBelow (code n) (code (3 * n + 1)) ∧
      ¬ wordBelow (code (3 * n + 1)) (code n) := by
  obtain ⟨u, rest, ha, _, heq⟩ := active_head n
  obtain ⟨b, hb, hc⟩ := child_binary_code n 0 (by decide) ha
  simp only [Nat.add_zero, newSlots, List.getElem_cons_zero] at hc
  rw [heq, hc]
  simp only [List.append_assoc, List.cons_append, List.nil_append,
    below_common_prefix, below_cons_same]
  rw [below_cons_distinct .two .zero _ _ (by decide),
    below_cons_distinct .zero .two _ _ (by decide)]
  simp [NoOne]

/-- The third child stays in the old ray strictly below the selected code. -/
theorem code_lower_child (n : Nat) :
    wordBelow (code (3 * n + 3)) (code n) ∧
      ¬ wordBelow (code n) (code (3 * n + 3)) := by
  obtain ⟨u, rest, ha, _, heq⟩ := active_head n
  obtain ⟨b, hb, hc⟩ := child_binary_code n 2 (by decide) ha
  have hi : 3 * n + 1 + 2 = 3 * n + 3 := by omega
  rw [hi] at hc
  simp only [newSlots, List.getElem_cons_succ, List.getElem_cons_zero] at hc
  rw [heq, hc]
  simp only [List.append_assoc, List.cons_append, List.nil_append, below_common_prefix]
  rw [below_cons_distinct .two .zero _ _ (by decide),
    below_cons_distinct .zero .two _ _ (by decide)]
  have hbb : NoOne b := by
    intro a ha heq
    subst a
    exact hb ha
  simp [hbb]

/-- The middle child enters the other upper cone of the selected code. -/
theorem code_fork (n : Nat) :
    wordBelow (code n) (code (3 * n + 1)) ∧
    ¬ wordBelow (code (3 * n + 1)) (code n) ∧
    wordBelow (code n) (code (3 * n + 2)) ∧
    ¬ wordBelow (code (3 * n + 2)) (code n) ∧
    wordMeet (code (3 * n + 1)) (code (3 * n + 2)) = code n := by
  obtain ⟨u, rest, ha, _, heq⟩ := active_head n
  obtain ⟨p, hp, hc₀⟩ := child_binary_code n 0 (by decide) ha
  obtain ⟨q, hq, hc₁⟩ := child_binary_code n 1 (by decide) ha
  simp only [Nat.add_zero, newSlots, List.getElem_cons_zero] at hc₀
  have hi : 3 * n + 1 + 1 = 3 * n + 2 := by omega
  rw [hi] at hc₁
  simp only [newSlots, List.getElem_cons_succ, List.getElem_cons_zero] at hc₁
  refine ⟨(code_upper_child n).1, (code_upper_child n).2, ?_, ?_, ?_⟩
  · rw [heq, hc₁]
    have hpref := below_common_prefix (u ++ [.zero, .two]) [] (.one :: q)
    simpa using hpref.mpr ((below_nil_cons .one q).mpr (by decide))
  · rw [heq, hc₁]
    have hpref := below_common_prefix (u ++ [.zero, .two]) (.one :: q) []
    simpa using fun h => (show ¬ wordBelow (.one :: q) [] by
      simp [below_cons_nil]) (hpref.mp h)
  · rw [heq, hc₀, hc₁]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      meet_common_prefix]
    congr 1
    cases h : parseWord p <;>
      simp [wordMeet, parseWord, prependBlock, h, RayTree.meet, binaryMin,
        binaryLE, printWord, binaryLetter]

/-- An upper child has the same comparisons as its parent with every older
coding node. -/
theorem upper_child_profile {k n : Nat} (hkn : k < n) :
    (wordBelow (code k) (code (3 * n + 1)) ↔ wordBelow (code k) (code n)) ∧
    (wordBelow (code (3 * n + 1)) (code k) ↔ wordBelow (code n) (code k)) := by
  obtain ⟨u, rest, ha, hlen, heq⟩ := active_head n
  obtain ⟨b, hb, hc⟩ := child_binary_code n 0 (by decide) ha
  simp only [Nat.add_zero, newSlots, List.getElem_cons_zero] at hc
  rw [heq, hc, List.append_assoc]
  apply shorter_binary_tails
  · rw [code_length, hlen]
    omega
  · simp [hb]
  · simp

/-- A lower child has the same comparisons as its parent with every older
coding node. -/
theorem lower_child_profile {k n : Nat} (hkn : k < n) :
    (wordBelow (code k) (code (3 * n + 3)) ↔ wordBelow (code k) (code n)) ∧
    (wordBelow (code (3 * n + 3)) (code k) ↔ wordBelow (code n) (code k)) := by
  obtain ⟨u, rest, ha, hlen, heq⟩ := active_head n
  obtain ⟨b, hb, hc⟩ := child_binary_code n 2 (by decide) ha
  have hi : 3 * n + 1 + 2 = 3 * n + 3 := by omega
  rw [hi] at hc
  simp only [newSlots, List.getElem_cons_succ, List.getElem_cons_zero] at hc
  rw [heq, hc, List.append_assoc]
  apply shorter_binary_tails
  · rw [code_length, hlen]
    omega
  · simp [hb]
  · simp

/-- Every strict interval between actual coding nodes contains an actual
coding node. The child of the later-coded endpoint provides a witness. -/
theorem code_dense (n m : Nat) (hnm : wordBelow (code n) (code m))
    (hmn : ¬ wordBelow (code m) (code n)) :
    ∃ k, wordBelow (code n) (code k) ∧ ¬ wordBelow (code k) (code n) ∧
      wordBelow (code k) (code m) ∧ ¬ wordBelow (code m) (code k) := by
  rcases Nat.lt_trichotomy n m with h | h | h
  · obtain ⟨h₁, h₂⟩ := lower_child_profile h
    exact ⟨3 * m + 3, h₁.mpr hnm, fun hk => hmn (h₂.mp hk),
      (code_lower_child m).1, (code_lower_child m).2⟩
  · subst m
    exact False.elim (hmn (wordBelow_refl _))
  · obtain ⟨h₁, h₂⟩ := upper_child_profile h
    exact ⟨3 * n + 1, (code_upper_child n).1, (code_upper_child n).2,
      h₂.mpr hnm, fun hk => hmn (h₁.mp hk)⟩

/-- Density of the literal meet-closed sparse set, without an isomorphism
hypothesis or an assumed fair scheduling principle. -/
theorem sparse_dense {s t : Word} (hs : InSparse s) (ht : InSparse t)
    (hst : wordBelow s t) (hts : ¬ wordBelow t s) :
    ∃ u, InSparse u ∧ wordBelow s u ∧ ¬ wordBelow u s ∧
      wordBelow u t ∧ ¬ wordBelow t u := by
  obtain ⟨n, rfl⟩ := (inSparse_iff_code s).mp hs
  obtain ⟨m, rfl⟩ := (inSparse_iff_code t).mp ht
  obtain ⟨k, hk⟩ := code_dense n m hst hts
  exact ⟨code k, (inSparse_iff_code _).mpr ⟨k, rfl⟩, hk⟩

/-- Both strict directions are inhabited at every point of the sparse set. -/
theorem sparse_no_endpoints {s : Word} (hs : InSparse s) :
    (∃ u, InSparse u ∧ wordBelow u s ∧ ¬ wordBelow s u) ∧
    (∃ v, InSparse v ∧ wordBelow s v ∧ ¬ wordBelow v s) := by
  obtain ⟨n, rfl⟩ := (inSparse_iff_code s).mp hs
  exact ⟨⟨code (3 * n + 3), (inSparse_iff_code _).mpr ⟨_, rfl⟩,
      code_lower_child n⟩,
    ⟨code (3 * n + 1), (inSparse_iff_code _).mpr ⟨_, rfl⟩,
      code_upper_child n⟩⟩

/-- At each sparse node, two sparse upper nodes have precisely that meet. -/
theorem sparse_fork {s : Word} (hs : InSparse s) :
    ∃ u v, InSparse u ∧ InSparse v ∧
      wordBelow s u ∧ ¬ wordBelow u s ∧
      wordBelow s v ∧ ¬ wordBelow v s ∧ wordMeet u v = s := by
  obtain ⟨n, rfl⟩ := (inSparse_iff_code s).mp hs
  exact ⟨code (3 * n + 1), code (3 * n + 2),
    (inSparse_iff_code _).mpr ⟨_, rfl⟩, (inSparse_iff_code _).mpr ⟨_, rfl⟩,
    code_fork n⟩

end AllThoseBigRamsey.Pseudotree.Sparse
