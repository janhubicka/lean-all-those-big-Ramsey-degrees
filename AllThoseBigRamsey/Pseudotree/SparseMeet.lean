import AllThoseBigRamsey.Pseudotree.Sparse

/-!
# Meet closure of the literal sparse construction

In a block pseudotree with a selective coordinate minimum, a meet is either
one of its arguments or a truncation immediately before one of its separators.
The parser/printer equivalence transports that statement to literal ternary
words. The proved origin invariant for the sparse queue then gives meet
closure; no isomorphism or meet-preservation hypothesis is assumed.
-/
namespace AllThoseBigRamsey.Pseudotree

namespace RayTree

/-- Truncations immediately before separators, omitting the whole node. -/
def separatorRoots : RayTree α → List (RayTree α)
  | .point _ => []
  | .above a s => .point a :: (separatorRoots s).map (.above a)

/-- A selective coordinate meet cannot create an unrecorded branching point. -/
theorem meet_operand_or_separator [DecidableEq α] (μ : α → α → α)
    (hμ : ∀ a b, μ a b = a ∨ μ a b = b) (s t : RayTree α) :
    meet μ s t = s ∨ meet μ s t = t ∨
      meet μ s t ∈ separatorRoots s ∨ meet μ s t ∈ separatorRoots t := by
  induction s generalizing t with
  | point a =>
      cases t with
      | point b =>
          rcases hμ a b with h | h
          · exact Or.inl (by simp [meet, h])
          · exact Or.inr (Or.inl (by simp [meet, h]))
      | above b t =>
          rcases hμ a b with h | h
          · exact Or.inl (by simp [meet, h])
          · exact Or.inr (Or.inr (Or.inr (by simp [meet, h, separatorRoots])))
  | above a s ih =>
      cases t with
      | point b =>
          rcases hμ a b with h | h
          · exact Or.inr (Or.inr (Or.inl (by simp [meet, h, separatorRoots])))
          · exact Or.inr (Or.inl (by simp [meet, h]))
      | above b t =>
          by_cases hab : a = b
          · subst b
            simp only [meet, ↓reduceIte]
            rcases ih t with h | h | h | h
            · exact Or.inl (congrArg (RayTree.above a) h)
            · exact Or.inr (Or.inl (congrArg (RayTree.above a) h))
            · exact Or.inr (Or.inr (Or.inl (by
                simp only [separatorRoots, List.mem_cons]
                exact Or.inr (List.mem_map.mpr ⟨_, h, rfl⟩))))
            · exact Or.inr (Or.inr (Or.inr (by
                simp only [separatorRoots, List.mem_cons]
                exact Or.inr (List.mem_map.mpr ⟨_, h, rfl⟩))))
          · rcases hμ a b with h | h
            · exact Or.inr (Or.inr (Or.inl (by simp [meet, hab, h, separatorRoots])))
            · exact Or.inr (Or.inr (Or.inr (by simp [meet, hab, h, separatorRoots])))

end RayTree

namespace Sparse

theorem onePrefixes_binary (s : List Bool) : onePrefixes (s.map binaryLetter) = [] := by
  induction s with
  | nil => rfl
  | cons b s ih => cases b <;> simp [binaryLetter, onePrefixes, ih]

/-- The block-model truncations are exactly the literal prefixes before 1s. -/
theorem print_separatorRoots (s : RayTree (List Bool)) :
    (s.separatorRoots.map printWord) = onePrefixes (printWord s) := by
  induction s with
  | point a => simp [RayTree.separatorRoots, printWord, onePrefixes_binary]
  | above a s ih =>
      simp [RayTree.separatorRoots, printWord, onePrefixes_append, onePrefixes_binary,
        onePrefixes, List.map_map, Function.comp_def, ← ih]

/-- Exact literal version of the truncation property of the manuscript's meet. -/
theorem wordMeet_operand_or_onePrefix (s t : Word) :
    wordMeet s t = s ∨ wordMeet s t = t ∨
      wordMeet s t ∈ onePrefixes s ∨ wordMeet s t ∈ onePrefixes t := by
  have hmin : ∀ a b, binaryMin a b = a ∨ binaryMin a b = b := by
    intro a b
    unfold binaryMin
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases RayTree.meet_operand_or_separator binaryMin hmin (parseWord s) (parseWord t)
    with h | h | h | h
  · exact Or.inl (by simpa [wordMeet] using congrArg printWord h)
  · exact Or.inr (Or.inl (by simpa [wordMeet] using congrArg printWord h))
  · apply Or.inr ∘ Or.inr ∘ Or.inl
    have hp := (List.mem_map (f := printWord)).mpr ⟨_, h, rfl⟩
    simpa [print_separatorRoots, wordMeet] using hp
  · apply Or.inr ∘ Or.inr ∘ Or.inr
    have hp := (List.mem_map (f := printWord)).mpr ⟨_, h, rfl⟩
    simpa [print_separatorRoots, wordMeet] using hp

/-- Closure under separator prefixes suffices for actual meet closure. -/
theorem meet_closed_of_origins (P : Word → Prop)
    (horig : ∀ w, P w → ∀ p ∈ onePrefixes w, P p)
    (hs : P s) (ht : P t) : P (wordMeet s t) := by
  rcases wordMeet_operand_or_onePrefix s t with he | he | hp | hp
  · simpa [he] using hs
  · simpa [he] using ht
  · exact horig s hs _ hp
  · exact horig t ht _ hp

/-- Every finite accumulated set of coding nodes is already meet-closed. -/
theorem stage_codes_meet_closed (n : Nat) (hs : s ∈ (stage n).codes)
    (ht : t ∈ (stage n).codes) : wordMeet s t ∈ (stage n).codes :=
  meet_closed_of_origins (fun w => w ∈ (stage n).codes) (stage_origins n).2 hs ht

/-- The infinite set obtained as the union of the finite coding sets. -/
def InSparse (w : Word) : Prop := ∃ n, w ∈ (stage n).codes

theorem inSparse_origins (hw : InSparse w) (hp : p ∈ onePrefixes w) : InSparse p := by
  obtain ⟨n, hn⟩ := hw
  exact ⟨n, (stage_origins n).2 w hn p hp⟩

/-- The actual sparse set is meet-closed for the explicit ternary-word meet. -/
theorem sparse_meet_closed (hs : InSparse s) (ht : InSparse t) :
    InSparse (wordMeet s t) :=
  meet_closed_of_origins InSparse (fun _ hw _ hp => inSparse_origins hw hp) hs ht

/-- The union of stage code sets is exactly the range of the coding sequence. -/
theorem inSparse_iff_code (w : Word) : InSparse w ↔ ∃ n, w = code n := by
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨j, _, hj⟩ := (mem_stage_codes_iff n w).mp hn
    exact ⟨j, hj⟩
  · rintro ⟨n, rfl⟩
    exact ⟨n + 1, code_mem_next n⟩

/-- The meet of any two generated nodes is a node generated no later than
both inputs have been generated. This is the literal meet-closure claim in
Lemma 5.2, rather than a statement about an abstract assumed substructure. -/
theorem code_meet (n m : Nat) :
    ∃ j, j ≤ max n m ∧ wordMeet (code n) (code m) = code j := by
  rcases wordMeet_operand_or_onePrefix (code n) (code m) with h | h | hp | hp
  · exact ⟨n, Nat.le_max_left _ _, h⟩
  · exact ⟨m, Nat.le_max_right _ _, h⟩
  · obtain ⟨j, hj, heq⟩ := code_onePrefixes_earlier n _ hp
    exact ⟨j, by omega, heq⟩
  · obtain ⟨j, hj, heq⟩ := code_onePrefixes_earlier m _ hp
    exact ⟨j, by omega, heq⟩

end Sparse
end AllThoseBigRamsey.Pseudotree
