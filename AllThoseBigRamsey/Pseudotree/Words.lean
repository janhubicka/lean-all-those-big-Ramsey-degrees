import AllThoseBigRamsey.Pseudotree.Model

/-!
# Literal ternary words and their ray coordinates

Binary letters are `false = 0` and `true = 2`. The comparison below puts
`2 < end-of-word < 0`, exactly as in the note. Ternary words split at `one`
into the nonempty block sequence of `RayTree`. The parser and printer are
proved inverse, so the block-model laws apply to the actual word carrier.
-/

namespace AllThoseBigRamsey.Pseudotree

def binaryLE : List Bool → List Bool → Bool
  | [], [] => true
  | [], b :: _ => !b
  | a :: _, [] => a
  | a :: s, b :: t => if a == b then binaryLE s t else a

theorem binaryLE_refl (s : List Bool) : binaryLE s s = true := by
  induction s with
  | nil => rfl
  | cons a s ih => simp [binaryLE, ih]

theorem binaryLE_total (s t : List Bool) : binaryLE s t = true ∨ binaryLE t s = true := by
  induction s generalizing t with
  | nil => cases t with
    | nil => exact Or.inl rfl
    | cons b t => cases b <;> simp [binaryLE]
  | cons a s ih => cases t with
    | nil => cases a <;> simp [binaryLE]
    | cons b t => cases a <;> cases b <;> simp [binaryLE, ih t]

theorem binaryLE_antisymm {s t : List Bool}
    (hst : binaryLE s t = true) (hts : binaryLE t s = true) : s = t := by
  induction s generalizing t with
  | nil => cases t with
    | nil => rfl
    | cons b t => cases b <;> simp [binaryLE] at *
  | cons a s ih => cases t with
    | nil => cases a <;> simp [binaryLE] at *
    | cons b t =>
      cases a <;> cases b <;> simp [binaryLE] at hst hts
      · exact congrArg (List.cons false) (ih hst hts)
      · exact congrArg (List.cons true) (ih hst hts)

theorem binaryLE_trans {s t u : List Bool}
    (hst : binaryLE s t = true) (htu : binaryLE t u = true) : binaryLE s u = true := by
  induction s generalizing t u with
  | nil =>
    cases t with
    | nil => exact htu
    | cons b t =>
      cases u with
      | nil => rfl
      | cons c u => cases b <;> cases c <;> simp_all [binaryLE]
  | cons a s ih =>
    cases t with
    | nil =>
      cases u with
      | nil => exact hst
      | cons c u => cases a <;> cases c <;> simp_all [binaryLE]
    | cons b t =>
      cases u with
      | nil => cases a <;> cases b <;> simp_all [binaryLE]
      | cons c u =>
        cases a <;> cases b <;> cases c <;> simp_all [binaryLE] <;> exact ih hst htu

theorem binaryLE_append_lower (s : List Bool) :
    binaryLE (s ++ [true]) s = true ∧ binaryLE s (s ++ [true]) = false := by
  induction s with
  | nil => simp [binaryLE]
  | cons a s ih => simp [binaryLE, ih]

theorem binaryLE_append_upper (s : List Bool) :
    binaryLE s (s ++ [false]) = true ∧ binaryLE (s ++ [false]) s = false := by
  induction s with
  | nil => simp [binaryLE]
  | cons a s ih => simp [binaryLE, ih]

/-- Binary words under the note's order have no endpoints. -/
theorem binary_no_endpoints (s : List Bool) :
    (∃ t, binaryLE t s = true ∧ t ≠ s) ∧
    (∃ t, binaryLE s t = true ∧ t ≠ s) := by
  constructor
  · refine ⟨s ++ [true], (binaryLE_append_lower s).1, ?_⟩
    intro heq
    have hlen := congrArg List.length heq
    simp at hlen
  · refine ⟨s ++ [false], (binaryLE_append_upper s).1, ?_⟩
    intro heq
    have hlen := congrArg List.length heq
    simp at hlen

/-- Density of the binary-word order is proved directly, without using Cantor's
classification theorem or assuming the ray is rational. -/
theorem binary_dense {s t : List Bool} (hst : binaryLE s t = true) (hne : s ≠ t) :
    ∃ u, binaryLE s u = true ∧ s ≠ u ∧ binaryLE u t = true ∧ u ≠ t := by
  induction s generalizing t with
  | nil =>
    cases t with
    | nil => exact False.elim (hne rfl)
    | cons b t =>
      cases b with
      | true => simp [binaryLE] at hst
      | false =>
        refine ⟨false :: (t ++ [true]), by simp [binaryLE], by simp, ?_, ?_⟩
        · simpa [binaryLE] using (binaryLE_append_lower t).1
        · intro heq
          have hlen := congrArg List.length heq
          simp at hlen
  | cons a s ih =>
    cases t with
    | nil =>
      cases a with
      | false => simp [binaryLE] at hst
      | true =>
        refine ⟨true :: (s ++ [false]), ?_, ?_, by simp [binaryLE], by simp⟩
        · simpa [binaryLE] using (binaryLE_append_upper s).1
        · intro heq
          have hlen := congrArg List.length heq
          simp at hlen
    | cons b t =>
      cases a <;> cases b
      · have hst' : binaryLE s t = true := by simpa [binaryLE] using hst
        obtain ⟨u, hsu, hsne, hut, hune⟩ := ih hst' (fun h => hne (congrArg (List.cons false) h))
        exact ⟨false :: u, by simpa [binaryLE] using hsu,
          by simpa using hsne, by simpa [binaryLE] using hut, by simpa using hune⟩
      · simp [binaryLE] at hst
      · exact ⟨[], by simp [binaryLE], by simp, by simp [binaryLE], by simp⟩
      · have hst' : binaryLE s t = true := by simpa [binaryLE] using hst
        obtain ⟨u, hsu, hsne, hut, hune⟩ := ih hst' (fun h => hne (congrArg (List.cons true) h))
        exact ⟨true :: u, by simpa [binaryLE] using hsu,
          by simpa using hsne, by simpa [binaryLE] using hut, by simpa using hune⟩

inductive TernaryLetter where
  | zero | one | two
  deriving DecidableEq, Repr

def binaryLetter (b : Bool) : TernaryLetter := if b then .two else .zero

def prependBlock (b : Bool) : RayTree (List Bool) → RayTree (List Bool)
  | .point s => .point (b :: s)
  | .above s t => .above (b :: s) t

def parseWord : List TernaryLetter → RayTree (List Bool)
  | [] => .point []
  | .zero :: s => prependBlock false (parseWord s)
  | .one :: s => .above [] (parseWord s)
  | .two :: s => prependBlock true (parseWord s)

def printWord : RayTree (List Bool) → List TernaryLetter
  | .point s => s.map binaryLetter
  | .above s t => s.map binaryLetter ++ .one :: printWord t

@[simp] theorem printWord_prependBlock (b : Bool) (s : RayTree (List Bool)) :
    printWord (prependBlock b s) = binaryLetter b :: printWord s := by
  cases s <;> simp [printWord, prependBlock]

@[simp] theorem parseWord_binary_cons (b : Bool) (s : List TernaryLetter) :
    parseWord (binaryLetter b :: s) = prependBlock b (parseWord s) := by
  cases b <;> rfl

@[simp] theorem parseWord_binary (s : List Bool) :
    parseWord (s.map binaryLetter) = .point s := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [parseWord_binary_cons, ih, prependBlock]

@[simp] theorem parseWord_prefix (s : List Bool) (t : List TernaryLetter) :
    parseWord (s.map binaryLetter ++ .one :: t) = .above s (parseWord t) := by
  induction s with
  | nil => rfl
  | cons b s ih => simp [parseWord_binary_cons, ih, prependBlock]

/-- Parsing after printing recovers every block sequence. -/
@[simp] theorem parse_print (s : RayTree (List Bool)) : parseWord (printWord s) = s := by
  induction s with
  | point a => exact parseWord_binary a
  | above a s ih => simpa [printWord] using congrArg (RayTree.above a) ih

/-- Printing after parsing recovers every literal ternary word. -/
@[simp] theorem print_parse (s : List TernaryLetter) : printWord (parseWord s) = s := by
  induction s with
  | nil => rfl
  | cons a s ih => cases a <;> simp [parseWord, printWord, binaryLetter, ih]

def wordBelow (s t : List TernaryLetter) : Prop :=
  RayTree.Below (fun a b => binaryLE a b = true) (parseWord s) (parseWord t)

theorem wordBelow_refl (s : List TernaryLetter) : wordBelow s s :=
  RayTree.below_refl binaryLE_refl _

theorem wordBelow_trans {s t u : List TernaryLetter}
    (hst : wordBelow s t) (htu : wordBelow t u) : wordBelow s u :=
  RayTree.below_trans (r := fun a b : List Bool => binaryLE a b = true)
    (fun h₁ h₂ => binaryLE_trans h₁ h₂) hst htu

theorem wordBelow_antisymm {s t : List TernaryLetter}
    (hst : wordBelow s t) (hts : wordBelow t s) : s = t := by
  have h := RayTree.below_antisymm binaryLE_antisymm hst hts
  have hp := congrArg printWord h
  simpa using hp

theorem word_predecessors_comparable {s t u : List TernaryLetter}
    (hs : wordBelow s u) (ht : wordBelow t u) : wordBelow s t ∨ wordBelow t s :=
  RayTree.predecessors_comparable binaryLE_total hs ht

def binaryMin (s t : List Bool) : List Bool := if binaryLE s t then s else t

theorem binaryMin_le_left (s t : List Bool) : binaryLE (binaryMin s t) s = true := by
  by_cases h : binaryLE s t = true
  · simpa [binaryMin, h] using binaryLE_refl s
  · obtain h' | h' := binaryLE_total s t
    · contradiction
    · simpa [binaryMin, h] using h'

theorem binaryMin_le_right (s t : List Bool) : binaryLE (binaryMin s t) t = true := by
  by_cases h : binaryLE s t = true
  · simp [binaryMin, h]
  · simpa [binaryMin, h] using binaryLE_refl t

theorem le_binaryMin {s t u : List Bool}
    (hs : binaryLE u s = true) (ht : binaryLE u t = true) :
    binaryLE u (binaryMin s t) = true := by
  by_cases h : binaryLE s t = true
  · simpa [binaryMin, h] using hs
  · simpa [binaryMin, h] using ht

def wordMeet (s t : List TernaryLetter) : List TernaryLetter :=
  printWord (RayTree.meet binaryMin (parseWord s) (parseWord t))

/-- The manuscript's meet operation is the actual greatest lower bound on
literal ternary words. -/
theorem wordBelow_meet_iff (s t u : List TernaryLetter) :
    wordBelow u (wordMeet s t) ↔ wordBelow u s ∧ wordBelow u t := by
  simp only [wordBelow, wordMeet, parse_print]
  exact RayTree.below_meet_iff (r := fun a b : List Bool => binaryLE a b = true)
    (fun h₁ h₂ => binaryLE_trans h₁ h₂)
    binaryMin_le_left binaryMin_le_right (fun h₁ h₂ => le_binaryMin h₁ h₂)

/-- The two chain elements used to refute the original 'lexicographically
least' sentence: the smaller one is a proper prefix of the larger one. -/
theorem prefix_chain_regression :
    wordBelow [.zero, .two] [.zero, .two, .one, .two, .two, .two, .zero, .two] ∧
    ([.zero, .two] : List TernaryLetter) ≠
      [.zero, .two, .one, .two, .two, .two, .zero, .two] := by
  simp [wordBelow, parseWord, prependBlock, RayTree.first, binaryLE]

end AllThoseBigRamsey.Pseudotree
