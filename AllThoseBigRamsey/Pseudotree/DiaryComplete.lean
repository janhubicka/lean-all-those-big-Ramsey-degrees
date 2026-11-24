import AllThoseBigRamsey.Pseudotree.DiaryInjective

/-!
# Completeness of the finite event grammar

An expanded event sequence is specified by independent local width,
original-branch, and type-(d) legality predicates. These are sufficient to
reconstruct a grammar diary; no assumed decoder or model bridge is used.
-/

namespace AllThoseBigRamsey.Pseudotree

theorem turnsLegal_false_of_ne_turn (es : List DiaryEvent)
    (ht : TurnsLegal true es) (hne : ∀ rest, es ≠ .turn :: rest) : TurnsLegal false es := by
  cases es with
  | nil => trivial
  | cons e es =>
      cases e with
      | split => exact ht
      | leaf => exact ht
      | code => exact ht
      | turn => exact False.elim (hne es rfl)

/-- Closed-original-branch states have no continuation events. Thus their
initial type-(d) permission is immaterial. -/
theorem turnsLegal_false_of_closed (es : List DiaryEvent)
    (hl : LeftValid false es) (ht : TurnsLegal true es) : TurnsLegal false es := by
  apply turnsLegal_false_of_ne_turn es ht
  intro rest heq
  rw [heq] at hl
  simp [LeftValid] at hl

/-- Every complete locally legal trace comes from a unique packaged grammar
object. The coding-node index is computed from the trace itself. -/
theorem diary_of_events (es : List DiaryEvent) (left : Bool) (k : Nat)
    (hw : WidthValid k es) (hl : LeftValid left es) (ht : TurnsLegal false es) :
    ∃ d : Diary left (es.filter DiaryEvent.isCode).length k, d.events = es := by
  cases es with
  | nil =>
      have hk : k = 0 := hw
      subst k
      exact ⟨.done left, rfl⟩
  | cons e es =>
      cases e with
      | turn => simp [TurnsLegal] at ht
      | code =>
          obtain ⟨rfl, hl⟩ := hl
          obtain ⟨hk, hw⟩ := hw
          cases k with
          | zero => omega
          | succ k =>
              obtain ⟨d, hd⟩ := diary_of_events es true (k + 1) hw hl ht
              exact ⟨.continueLeft d, congrArg (List.cons DiaryEvent.code) hd⟩
      | leaf i =>
          obtain ⟨hi, hw⟩ := hw
          cases k with
          | zero => omega
          | succ k =>
              have hw' : WidthValid k es := by simpa using hw
              cases left with
              | false =>
                  have hl' : LeftValid false es := by simpa [LeftValid] using hl
                  have ht' := turnsLegal_false_of_closed es hl' ht
                  obtain ⟨d, hd⟩ := diary_of_events es false k hw' hl' ht'
                  exact ⟨.leafClosed ⟨i, hi⟩ d, congrArg (List.cons (DiaryEvent.leaf i)) hd⟩
              | true =>
                  cases i with
                  | zero =>
                      have hl' : LeftValid false es := by simpa [LeftValid] using hl
                      have ht' := turnsLegal_false_of_closed es hl' ht
                      obtain ⟨d, hd⟩ := diary_of_events es false k hw' hl' ht'
                      exact ⟨.endLeft d, congrArg (List.cons (DiaryEvent.leaf 0)) hd⟩
                  | succ i =>
                      have hi' : i < k := by omega
                      have hl' : LeftValid true es := by simpa [LeftValid] using hl
                      by_cases hturn : ∃ rest, es = .turn :: rest
                      · obtain ⟨rest, rfl⟩ := hturn
                        obtain ⟨d, hd⟩ := diary_of_events rest true k hw'.2 hl'.2 ht.2
                        exact ⟨.leafRight ⟨i, hi'⟩ true d,
                          congrArg (fun xs => DiaryEvent.leaf (i + 1) :: DiaryEvent.turn :: xs) hd⟩
                      · have hne : ∀ rest, es ≠ .turn :: rest := by simpa using hturn
                        have ht' := turnsLegal_false_of_ne_turn es ht hne
                        obtain ⟨d, hd⟩ := diary_of_events es true k hw' hl' ht'
                        exact ⟨.leafRight ⟨i, hi'⟩ false d,
                          congrArg (List.cons (DiaryEvent.leaf (i + 1))) hd⟩
      | split i =>
          obtain ⟨hi, hw⟩ := hw
          cases left with
          | false =>
              have ht' := turnsLegal_false_of_closed es hl ht
              obtain ⟨d, hd⟩ := diary_of_events es false (k + 1) hw hl ht'
              exact ⟨.splitClosed ⟨i, hi⟩ d, congrArg (List.cons (DiaryEvent.split i)) hd⟩
          | true =>
              by_cases hturn : ∃ rest, es = .turn :: rest
              · obtain ⟨rest, rfl⟩ := hturn
                obtain ⟨d, hd⟩ := diary_of_events rest true (k + 1) hw.2 hl.2 ht.2
                exact ⟨.splitOpen ⟨i, hi⟩ true d,
                  congrArg (fun xs => DiaryEvent.split i :: DiaryEvent.turn :: xs) hd⟩
              · have hne : ∀ rest, es ≠ .turn :: rest := by simpa using hturn
                have ht' := turnsLegal_false_of_ne_turn es ht hne
                obtain ⟨d, hd⟩ := diary_of_events es true (k + 1) hw hl ht'
                exact ⟨.splitOpen ⟨i, hi⟩ false d, congrArg (List.cons (DiaryEvent.split i)) hd⟩

termination_by es.length
decreasing_by all_goals simp_all <;> omega

theorem diary_of_events_unique (es : List DiaryEvent) (left : Bool) (k n : Nat)
    (hw : WidthValid k es) (hl : LeftValid left es) (ht : TurnsLegal false es)
    (hc : (es.filter DiaryEvent.isCode).length = n) :
    ∃ d : Diary left n k, d.events = es ∧
      ∀ e : Diary left n k, e.events = es → e = d := by
  subst n
  obtain ⟨d, hd⟩ := diary_of_events es left k hw hl ht
  exact ⟨d, hd, fun e he => e.events_injective d (he.trans hd.symm)⟩

end AllThoseBigRamsey.Pseudotree
