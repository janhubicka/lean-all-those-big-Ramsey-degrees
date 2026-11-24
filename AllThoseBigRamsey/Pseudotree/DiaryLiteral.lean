import AllThoseBigRamsey.Pseudotree.DiaryComplete

/-!
# Literal diaries specified by local level rules

A literal level consists of actual ternary words and its coding marks.
`LiteralLevels` checks the four child rules, the restriction of continuations
to words over `{0,1}`, the type-(d) adjacency restriction, and termination.
Its definition mentions neither the indexed `Diary` grammar nor `execute`.

This is an ordered-frontier presentation of literal trees. The results below
give a genuine grammar bijection and exact counts for this independently
specified class. Translating an unordered finite-set presentation into its
canonical lexicographically ordered levels is a separate representation step.
-/

namespace AllThoseBigRamsey.Pseudotree

structure LiteralLevel where
  frontier : List DiaryWord
  codes : List DiaryWord
  deriving DecidableEq, Repr

def DiaryEvent.allowsTurn : DiaryEvent → Bool
  | .split _ | .leaf _ => true
  | .code | .turn => false

/-- Direct local axioms on literal word levels. No grammar object, indexed
coding budget, or execution-image condition occurs in this definition. -/
inductive LiteralLevels : Bool → List DiaryWord → List LiteralLevel → Prop
  | done (allowed : Bool) : LiteralLevels allowed [] []
  | step {allowed : Bool} {ws : List DiaryWord} {rest : List LiteralLevel}
      (e : DiaryEvent) (legal : e.legal ws.length)
      (original : e = .code ∨ e = .turn → ∀ w ∈ ws.head?.toList, (2 : Fin 3) ∉ w)
      (turn_allowed : e = .turn → allowed = true)
      (tail : LiteralLevels e.allowsTurn (e.next ws) rest) :
      LiteralLevels allowed ws (⟨ws, e.coding ws⟩ :: rest)

/-- Collect the literal levels of a trace. This is used to prove a bridge;
it is not part of the definition of `LiteralLevels`. -/
def literalLevelsOf : List DiaryEvent → List DiaryWord → List LiteralLevel
  | [], _ => []
  | e :: es, ws => ⟨ws, e.coding ws⟩ :: literalLevelsOf es (e.next ws)

theorem originalFrontier_left_true (ho : OriginalFrontier left ws)
    (hp : 0 < ws.length) (hone : ∀ w ∈ ws.head?.toList, (2 : Fin 3) ∉ w) : left = true := by
  cases ws with
  | nil => simp at hp
  | cons w ws => exact ho.1.mp (hone w (by simp))

theorem DiaryEvent.tail_leftValid (hl : LeftValid left (e :: es)) :
    LeftValid (e.nextLeft left) es := by
  cases e with
  | split => exact hl
  | leaf => exact hl
  | code => exact hl.2
  | turn => exact hl.2

theorem DiaryEvent.tail_turnsLegal (ht : TurnsLegal allowed (e :: es)) :
    TurnsLegal e.allowsTurn es := by
  cases e with
  | split => exact ht
  | leaf => exact ht
  | code => exact ht
  | turn => exact ht.2

/-- Every locally specified literal diagram has a legal expanded trace;
the original-branch state is inferred from the actual letters. -/
theorem LiteralLevels.trace (hL : LiteralLevels allowed ws levels)
    (ho : OriginalFrontier left ws) :
    ∃ es, WidthValid ws.length es ∧ LeftValid left es ∧ TurnsLegal allowed es ∧
      literalLevelsOf es ws = levels := by
  induction hL generalizing left with
  | done allowed => exact ⟨[], rfl, trivial, trivial, rfl⟩
  | @step allowed ws rest e he hone hturn tail ih =>
      obtain ⟨es, hw, hl, ht, hlevels⟩ := ih (e.next_original ho)
      have hwcons : WidthValid ws.length (e :: es) := by
        cases e with
        | split i => exact ⟨he, by simpa [DiaryEvent.next, splitFrontier_length he] using hw⟩
        | leaf i => exact ⟨he, by simpa [DiaryEvent.next, leafFrontier_length he] using hw⟩
        | code => exact ⟨he, by simpa [DiaryEvent.next] using hw⟩
        | turn => exact ⟨he, by simpa [DiaryEvent.next] using hw⟩
      have hlcons : LeftValid left (e :: es) := by
        cases e with
        | split => exact hl
        | leaf => exact hl
        | code => exact ⟨originalFrontier_left_true ho he (hone (Or.inl rfl)), hl⟩
        | turn => exact ⟨originalFrontier_left_true ho he (hone (Or.inr rfl)), hl⟩
      have htcons : TurnsLegal allowed (e :: es) := by
        cases e with
        | split => exact ht
        | leaf => exact ht
        | code => exact ht
        | turn => exact ⟨hturn rfl, ht⟩
      exact ⟨e :: es, hwcons, hlcons, htcons, congrArg (List.cons _) hlevels⟩

/-- Conversely, a legal event trace satisfies the independently stated local
literal rules. -/
theorem literalLevelsOf_legal (es : List DiaryEvent)
    (hw : WidthValid ws.length es) (hl : LeftValid left es)
    (ht : TurnsLegal allowed es) (ho : OriginalFrontier left ws) :
    LiteralLevels allowed ws (literalLevelsOf es ws) := by
  induction es generalizing ws left allowed with
  | nil =>
      have hnil : ws = [] := List.eq_nil_of_length_eq_zero hw
      subst ws
      exact .done allowed
  | cons e es ih =>
      refine .step e (e.legal_of_width hw) ?_ ?_ ?_
      · intro heq w hw'
        rcases heq with rfl | rfl
        · obtain ⟨rfl, _⟩ := hl
          exact originalFrontier_head ho hw'
        · obtain ⟨rfl, _⟩ := hl
          exact originalFrontier_head ho hw'
      · intro heq
        subst e
        exact ht.1
      · exact ih (e.next_width_valid hw) (e.tail_leftValid hl)
          (e.tail_turnsLegal ht) (e.next_original ho)

@[simp] theorem literalLevelsOf_codes (es : List DiaryEvent) (ws : List DiaryWord) :
    ((literalLevelsOf es ws).flatMap LiteralLevel.codes) = (execute es ws).codes := by
  induction es generalizing ws <;> simp_all [literalLevelsOf, execute]

theorem literalLevelsOf_nodes (es : List DiaryEvent) (hw : WidthValid ws.length es) :
    ((literalLevelsOf es ws).flatMap LiteralLevel.frontier) = (execute es ws).nodes := by
  induction es generalizing ws with
  | nil =>
      have hnil : ws = [] := List.eq_nil_of_length_eq_zero hw
      simp [literalLevelsOf, execute, hnil]
  | cons e es ih =>
      simp only [literalLevelsOf, List.flatMap_cons, execute]
      rw [ih (e.next_width_valid hw)]

/-- Literal diagrams have an independently specified finite level list and
coding-node count. They are not defined as the image of grammar execution. -/
def LiteralDiary (n : Nat) :=
  { levels : List LiteralLevel // LiteralLevels false [[]] levels ∧
    (levels.flatMap LiteralLevel.codes).length = n }

namespace LiteralDiary

def levels (D : LiteralDiary n) : List LiteralLevel := D.val

def tree (D : LiteralDiary n) : DiaryTree :=
  ⟨D.levels.flatMap LiteralLevel.frontier, D.levels.flatMap LiteralLevel.codes⟩

/-- Every independently specified literal diary is represented by a grammar
diary, with equality of its literal levels. -/
theorem represented (D : LiteralDiary n) :
    ∃ d : Diary true n 1, literalLevelsOf d.events [[]] = D.levels := by
  obtain ⟨es, hw, hl, ht, hlevels⟩ := D.property.1.trace (left := true)
    (by simp [OriginalFrontier])
  have hc : (es.filter DiaryEvent.isCode).length = n := by
    rw [← execute_code_count es hw, ← literalLevelsOf_codes, hlevels]
    exact D.property.2
  obtain ⟨d, hd, _⟩ := diary_of_events_unique es true 1 n (by simpa using hw) hl ht hc
  exact ⟨d, by change literalLevelsOf d.events [[]] = D.val; rw [hd]; exact hlevels⟩

end LiteralDiary

/-- The direct map from event diaries to literal diagrams satisfies all
local axioms and preserves the coding-node count. -/
def Diary.toLiteral (d : Diary true n 1) : LiteralDiary n :=
  ⟨literalLevelsOf d.events [[]],
    literalLevelsOf_legal d.events (by simpa using d.width_valid) d.left_valid
      (d.turns_legal false) (by simp [OriginalFrontier]),
    by rw [literalLevelsOf_codes]; exact d.toTree_coding_count⟩

theorem Diary.toLiteral_tree (d : Diary true n 1) : d.toLiteral.tree = d.toTree := by
  change DiaryTree.mk ((literalLevelsOf d.events [[]]).flatMap LiteralLevel.frontier)
    ((literalLevelsOf d.events [[]]).flatMap LiteralLevel.codes) = d.toTree
  rw [literalLevelsOf_nodes d.events (by simpa using d.width_valid), literalLevelsOf_codes]
  rfl

theorem Diary.toLiteral_injective (d e : Diary true n 1) (h : d.toLiteral = e.toLiteral) : d = e := by
  apply d.toTree_injective e
  simpa only [toLiteral_tree] using congrArg LiteralDiary.tree h

theorem Diary.toLiteral_surjective (D : LiteralDiary n) : ∃ d : Diary true n 1, d.toLiteral = D := by
  obtain ⟨d, hd⟩ := D.represented
  exact ⟨d, Subtype.ext hd⟩

/-- A complete duplicate-free enumeration of the independent literal class. -/
def literalDiaryEnum (n : Nat) : List (LiteralDiary n) :=
  (diaryEnum true n 1).map Diary.toLiteral

theorem literalDiaryEnum_complete (D : LiteralDiary n) : D ∈ literalDiaryEnum n := by
  obtain ⟨d, rfl⟩ := Diary.toLiteral_surjective D
  exact List.mem_map.mpr ⟨d, diaryEnum_complete d, rfl⟩

theorem literalDiaryEnum_nodup (n : Nat) : (literalDiaryEnum n).Nodup :=
  diaryMap_nodup _ _ (diaryEnum_nodup true n 1) Diary.toLiteral_injective

theorem literalDiaryEnum_length (n : Nat) : (literalDiaryEnum n).length = diaryCount true n 1 := by
  simp only [literalDiaryEnum, List.length_map, diaryEnum_length]

/-- The recurrence is the exact cardinality of independently locally defined
literal diaries, not just a count of grammar terms or their image. -/
theorem literalDiary_cardinality (n : Nat) :
    ∃ all : List (LiteralDiary n), all.Nodup ∧ all.length = diaryCount true n 1 ∧
      ∀ D : LiteralDiary n, D ∈ all :=
  ⟨literalDiaryEnum n, literalDiaryEnum_nodup n, literalDiaryEnum_length n,
    literalDiaryEnum_complete⟩

end AllThoseBigRamsey.Pseudotree
