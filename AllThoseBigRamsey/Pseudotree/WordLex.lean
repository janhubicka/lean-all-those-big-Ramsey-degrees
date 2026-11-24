import AllThoseBigRamsey.Pseudotree.Sparse

/-!
# Lexicographic orientation of comparable ternary words

The pseudotree order reverses lexicographic order at a first disagreement:
the smaller pseudotree point must take the letter `2`, while the larger one
takes `0` or `1`. The only exception to this reversal is when the smaller
pseudotree point is a prefix of the larger one.

These statements concern all literal ternary words. The imported `lexLess`
is the ordinary lexicographic comparison with `0 < 1 < 2`; no sparse-copy
membership hypothesis is used.
-/

namespace AllThoseBigRamsey.Pseudotree

private theorem wordBelow_cons_same (a : TernaryLetter)
    (s t : List TernaryLetter) :
    wordBelow (a :: s) (a :: t) ↔ wordBelow s t := by
  cases a <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp [wordBelow, parseWord, prependBlock, hs, ht,
      RayTree.Below, RayTree.first, binaryLE]

/-- Comparable words are ordered in the reverse lexicographic direction,
unless the smaller pseudotree word is a prefix of the larger one. -/
theorem wordBelow_prefix_or_lex {x y : List TernaryLetter}
    (h : wordBelow y x) :
    y.IsPrefix x ∨ Sparse.lexLess x y = true := by
  induction y generalizing x with
  | nil => exact Or.inl List.nil_prefix
  | cons b t ih =>
      cases x with
      | nil => exact Or.inr rfl
      | cons a s =>
          by_cases hab : a = b
          · subst a
            have hts : wordBelow t s := (wordBelow_cons_same b t s).mp h
            rcases ih hts with hp | hl
            · obtain ⟨u, hu⟩ := hp
              exact Or.inl ⟨u, by simpa using congrArg (List.cons b) hu⟩
            · exact Or.inr (by simpa [Sparse.lexLess] using hl)
          · right
            cases a <;> cases b <;>
              cases ht : parseWord t <;> cases hs : parseWord s <;>
              simp_all [wordBelow, parseWord, prependBlock, RayTree.Below,
                RayTree.first, binaryLE, Sparse.lexLess, Sparse.rank]

/-- The prefix exception is the only obstruction to lexicographic reversal.
In particular, no sparse-copy hypothesis or separate strictness assumption
is needed. -/
theorem wordBelow_lex_of_not_prefix {x y : List TernaryLetter}
    (h : wordBelow y x) (hprefix : ¬ y.IsPrefix x) :
    Sparse.lexLess x y = true :=
  (wordBelow_prefix_or_lex h).resolve_left hprefix

/-- The lexicographic clause of the manuscript's ternary-model lemma for
arbitrary prefix-incomparable literal words. -/
theorem wordBelow_prefix_incomparable_lex {x y : List TernaryLetter}
    (hinc : ¬ x.IsPrefix y ∧ ¬ y.IsPrefix x) (h : wordBelow y x) :
    Sparse.lexLess x y = true :=
  wordBelow_lex_of_not_prefix h hinc.2

end AllThoseBigRamsey.Pseudotree
