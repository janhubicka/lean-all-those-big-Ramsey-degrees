import Std

/-!
# Finite event diaries for chains in the binary pseudotree

The four level types in `pseudotree_degrees.tex` are split, coding leaf,
coding continuation and noncoding continuation. A noncoding continuation
is only allowed immediately after a split or a coding leaf away from the
original leftmost branch. We package that optional continuation with its
preceding level.

`Diary left m k` is the resulting *event grammar*: `m` coding nodes remain,
`k` active branches remain, and `left` records whether the original leftmost
branch remains. The finite indices specify which ordered active branch is
used. This file checks the grammar, its height bound and its counting
recurrence. The equivalence with the manuscript's literal prefix-closed
ternary trees, and the Ramsey/unavoidability theorems, are separate obligations.
-/
namespace AllThoseBigRamsey.Pseudotree

/-- The finite ordered event grammar, with optional noncoding continuation
packaged with the only event types that may precede it. -/
inductive Diary : Bool → Nat → Nat → Type
  | done (left : Bool) : Diary left 0 0
  | splitClosed {m k : Nat} (idx : Fin k) :
      Diary false m (k + 1) → Diary false m k
  | leafClosed {m k : Nat} (idx : Fin (k + 1)) :
      Diary false m k → Diary false (m + 1) (k + 1)
  | splitOpen {m k : Nat} (idx : Fin k) (turn : Bool) :
      Diary true m (k + 1) → Diary true m k
  | endLeft {m k : Nat} :
      Diary false m k → Diary true (m + 1) (k + 1)
  | leafRight {m k : Nat} (idx : Fin k) (turn : Bool) :
      Diary true m k → Diary true (m + 1) (k + 1)
  | continueLeft {m k : Nat} :
      Diary true m (k + 1) → Diary true (m + 1) (k + 1)

/-- Number of actual levels, counting a packaged turn as a second level. -/
def Diary.levels : Diary left m k → Nat
  | .done _ => 0
  | .splitClosed _ d => d.levels + 1
  | .leafClosed _ d => d.levels + 1
  | .splitOpen _ turn d => d.levels + 1 + (if turn then 1 else 0)
  | .endLeft d => d.levels + 1
  | .leafRight _ turn d => d.levels + 1 + (if turn then 1 else 0)
  | .continueLeft d => d.levels + 1

/-- Every active branch must eventually receive its own coding leaf. -/
theorem Diary.width_le (d : Diary left m k) : k ≤ m := by
  induction d <;> omega

/-- A zero-width grammar has no coding nodes left. -/
theorem Diary.zero_width (d : Diary left m 0) : m = 0 := by
  cases d with
  | done => rfl
  | splitClosed idx => exact Fin.elim0 idx
  | splitOpen idx => exact Fin.elim0 idx

/-- A quantitative height bound, including the original leftmost-branch state. -/
theorem Diary.height_bound (d : Diary left m k) :
    if left then
      if k = 0 then d.levels = 0 else d.levels + 2 * k + 1 ≤ 4 * m
    else d.levels + k ≤ 2 * m := by
  induction d with
  | done left => cases left <;> simp [levels]
  | splitClosed idx d ih =>
      simp only [Bool.false_eq_true, ↓reduceIte, levels] at *
      omega
  | leafClosed idx d ih =>
      simp only [Bool.false_eq_true, ↓reduceIte, levels] at *
      omega
  | splitOpen idx turn d ih =>
      have hk := idx.isLt
      simp only [↓reduceIte, Nat.add_eq_zero_iff, Nat.succ_ne_zero,
        levels] at *
      have hkpos : 0 < _ := Nat.zero_lt_of_lt hk
      have hkne : _ ≠ 0 := Nat.ne_of_gt hkpos
      cases turn <;> simp_all <;> omega
  | endLeft d ih =>
      have hw := d.width_le
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.succ_ne_zero, levels] at *
      omega
  | leafRight idx turn d ih =>
      have hk := idx.isLt
      simp only [↓reduceIte, Nat.succ_ne_zero, levels] at *
      have hkpos : 0 < _ := Nat.zero_lt_of_lt hk
      have hkne : _ ≠ 0 := Nat.ne_of_gt hkpos
      cases turn <;> simp_all <;> omega
  | continueLeft d ih =>
      simp only [↓reduceIte, Nat.succ_ne_zero, levels] at *
      omega

/-- Every size-`n` event diary has at most `4*n-3` levels. -/
theorem Diary.chain_height_bound (d : Diary true n 1) :
    d.levels ≤ 4 * n - 3 := by
  have h := d.height_bound
  simp only [↓reduceIte, Nat.one_ne_zero] at h
  omega

/-- A family attaining the height bound: split, turn, right leaf, turn,
then repeat, ending with the original leftmost coding leaf. -/
def longestDiary : (n : Nat) → Diary true (n + 1) 1
  | 0 => .endLeft (.done false)
  | n + 1 => .splitOpen 0 true (.leafRight 0 true (longestDiary n))

@[simp] theorem longestDiary_levels (n : Nat) :
    (longestDiary n).levels = 4 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [longestDiary, Diary.levels, ih]; omega

/-- Counting recurrence from the paper. The decreasing measure is `2*m-k`;
invalid states are discarded before a recursive call is made. -/
def diaryCount (left : Bool) (m k : Nat) : Nat :=
  if hvalid : m < k then 0
  else match m, k with
    | 0, 0 => 1
    | _ + 1, 0 => 0
    | 0, _ + 1 => 0
    | m + 1, k + 1 =>
      if left then
        2 * (k + 1) * diaryCount true (m + 1) (k + 2) +
          diaryCount false m k +
          2 * k * diaryCount true m k +
          diaryCount true m (k + 1)
      else
        (k + 1) * diaryCount false (m + 1) (k + 2) +
          (k + 1) * diaryCount false m k
termination_by 2 * m - k
decreasing_by all_goals simp_all; all_goals omega

@[simp] theorem diaryCount_zero (left : Bool) : diaryCount left 0 0 = 1 := by
  rw [diaryCount]
  rfl

@[simp] theorem diaryCount_invalid (left : Bool) (h : m < k) :
    diaryCount left m k = 0 := by
  rw [diaryCount.eq_def]
  simp [h]

@[simp] theorem diaryCount_empty (left : Bool) (m : Nat) :
    diaryCount left (m + 1) 0 = 0 := by
  rw [diaryCount]
  simp

/-- Exactly the closed-state recurrence, with the valid-state condition explicit. -/
theorem diaryCount_closed (h : k ≤ m) :
    diaryCount false (m + 1) (k + 1) =
      (k + 1) * diaryCount false (m + 1) (k + 2) +
      (k + 1) * diaryCount false m k := by
  rw [diaryCount]
  simp [show ¬m + 1 < k + 1 by omega]

/-- Exactly the open-state recurrence, with the valid-state condition explicit. -/
theorem diaryCount_open (h : k ≤ m) :
    diaryCount true (m + 1) (k + 1) =
      2 * (k + 1) * diaryCount true (m + 1) (k + 2) +
      diaryCount false m k + 2 * k * diaryCount true m k +
      diaryCount true m (k + 1) := by
  rw [diaryCount]
  simp [show ¬m + 1 < k + 1 by omega]

/-- Ordered Cartesian product with a constructor applied to each pair. -/
def diaryChoices (xs : List α) (ys : List β) (f : α → β → γ) : List γ :=
  xs.flatMap fun x => ys.map (f x)

@[simp] theorem diaryChoices_length (xs : List α) (ys : List β)
    (f : α → β → γ) : (diaryChoices xs ys f).length = xs.length * ys.length := by
  induction xs with
  | nil => simp [diaryChoices]
  | cons x xs ih =>
      simp only [diaryChoices, List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons] at *
      rw [ih, Nat.add_mul]
      omega

/-- Cartesian-product constructors introduce no repetitions when injective. -/
theorem diaryChoices_nodup (xs : List α) (ys : List β) (f : α → β → γ)
    (hx : xs.Nodup) (hy : ys.Nodup)
    (hf : ∀ a b a' b', f a b = f a' b' → a = a' ∧ b = b') :
    (diaryChoices xs ys f).Nodup := by
  unfold diaryChoices List.Nodup
  rw [List.pairwise_flatMap]
  constructor
  · intro a _
    rw [List.pairwise_map]
    exact hy.imp (fun {b b'} hne heq => hne (hf a b a b' heq).2)
  · apply hx.imp
    intro a a' hne x hx' y hy' heq
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx'
    obtain ⟨b', _, rfl⟩ := List.mem_map.mp hy'
    exact hne (hf a b a' b' heq).1

/-- Injective constructors preserve absence of repetitions. -/
theorem diaryMap_nodup (xs : List α) (f : α → β) (hx : xs.Nodup)
    (hf : ∀ a b, f a = f b → a = b) : (xs.map f).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact hx.imp (fun {a b} hne heq => hne (hf a b heq))

/-- Exhaustive enumeration of the indexed event grammar. -/
def diaryEnum (left : Bool) (m k : Nat) : List (Diary left m k) :=
  if _hvalid : m < k then []
  else match m, k with
    | 0, 0 => [.done left]
    | _ + 1, 0 => []
    | 0, _ + 1 => []
    | m + 1, k + 1 =>
      match left with
      | false =>
        diaryChoices (List.finRange (k + 1))
          (diaryEnum false (m + 1) (k + 2)) Diary.splitClosed ++
        diaryChoices (List.finRange (k + 1))
          (diaryEnum false m k) Diary.leafClosed
      | true =>
        diaryChoices (List.finRange (k + 1))
          (diaryEnum true (m + 1) (k + 2)) (fun i d => .splitOpen i false d) ++
        diaryChoices (List.finRange (k + 1))
          (diaryEnum true (m + 1) (k + 2)) (fun i d => .splitOpen i true d) ++
        (diaryEnum false m k).map Diary.endLeft ++
        diaryChoices (List.finRange k)
          (diaryEnum true m k) (fun i d => .leafRight i false d) ++
        diaryChoices (List.finRange k)
          (diaryEnum true m k) (fun i d => .leafRight i true d) ++
        (diaryEnum true m (k + 1)).map Diary.continueLeft
termination_by 2 * m - k
decreasing_by all_goals simp_all; all_goals omega

/-- Every event diary occurs in the enumeration. The index itself guarantees
that no invalid or wrong-size object is enumerated. -/
theorem diaryEnum_complete (d : Diary left m k) : d ∈ diaryEnum left m k := by
  induction d with
  | done left =>
      rw [diaryEnum.eq_def]
      simp
  | @splitClosed m k idx d ih =>
      have hw := d.width_le
      have hi := idx.isLt
      cases k with
      | zero => exact Fin.elim0 idx
      | succ k =>
          cases m with
          | zero => omega
          | succ m =>
              rw [diaryEnum.eq_def]
              simp [show ¬m + 1 < k + 1 by omega, diaryChoices,
                List.mem_finRange, ih]
  | @leafClosed m k idx d ih =>
      have hw := d.width_le
      rw [diaryEnum.eq_def]
      simp [show ¬m + 1 < k + 1 by omega, diaryChoices,
        List.mem_finRange, ih]
  | @splitOpen m k idx turn d ih =>
      have hw := d.width_le
      have hi := idx.isLt
      cases k with
      | zero => exact Fin.elim0 idx
      | succ k =>
          cases m with
          | zero => omega
          | succ m =>
              rw [diaryEnum.eq_def]
              cases turn <;> simp [show ¬m + 1 < k + 1 by omega,
                diaryChoices, List.mem_finRange, ih]
  | @endLeft m k d ih =>
      have hw := d.width_le
      rw [diaryEnum.eq_def]
      simp [show ¬m + 1 < k + 1 by omega, diaryChoices,
        List.mem_finRange, ih]
  | @leafRight m k idx turn d ih =>
      have hw := d.width_le
      rw [diaryEnum.eq_def]
      cases turn <;> simp [show ¬m + 1 < k + 1 by omega,
        diaryChoices, List.mem_finRange, ih]
  | @continueLeft m k d ih =>
      have hw := d.width_le
      rw [diaryEnum.eq_def]
      simp [show ¬m + 1 < k + 1 by omega, diaryChoices,
        List.mem_finRange, ih]

/-- The enumeration has no duplicate event diaries. -/
theorem diaryEnum_nodup (left : Bool) (m k : Nat) :
    (diaryEnum left m k).Nodup := by
  generalize he : 2 * m - k = budget
  induction budget using Nat.strongRecOn generalizing left m k with
  | ind budget ih =>
      rw [diaryEnum.eq_def]
      by_cases hinvalid : m < k
      · simp [hinvalid]
      · simp only [hinvalid, ↓reduceDIte]
        cases m with
        | zero => cases k <;> simp
        | succ m =>
          cases k with
          | zero => simp
          | succ k =>
            have hsplit (b : Bool) := ih (2 * (m + 1) - (k + 2)) (by omega)
              b (m + 1) (k + 2) rfl
            have hleaf (b : Bool) := ih (2 * m - k) (by omega) b m k rfl
            have hcont := ih (2 * m - (k + 1)) (by omega) true m (k + 1) rfl
            cases left with
            | false =>
                have hs := diaryChoices_nodup (List.finRange (k + 1))
                  (diaryEnum false (m + 1) (k + 2)) Diary.splitClosed
                  (List.nodup_finRange _) (hsplit false) (by
                    intro a b a' b' h; simpa using h)
                have hl := diaryChoices_nodup (List.finRange (k + 1))
                  (diaryEnum false m k) Diary.leafClosed
                  (List.nodup_finRange _) (hleaf false) (by
                    intro a b a' b' h; simpa using h)
                simp only [List.nodup_append, hs, hl, true_and]
                simp [diaryChoices]
                grind
            | true =>
                have hs (turn : Bool) := diaryChoices_nodup (List.finRange (k + 1))
                  (diaryEnum true (m + 1) (k + 2))
                  (fun i d => Diary.splitOpen i turn d)
                  (List.nodup_finRange _) (hsplit true) (by
                    intro a b a' b' h; simpa using h)
                have he := diaryMap_nodup (diaryEnum false m k) Diary.endLeft
                  (hleaf false) (by intro a b h; simpa using h)
                have hl (turn : Bool) := diaryChoices_nodup (List.finRange k)
                  (diaryEnum true m k) (fun i d => Diary.leafRight i turn d)
                  (List.nodup_finRange _) (hleaf true) (by
                    intro a b a' b' h; simpa using h)
                have hc := diaryMap_nodup (diaryEnum true m (k + 1))
                  Diary.continueLeft hcont (by intro a b h; simpa using h)
                simp only [List.nodup_append, hs, he, hl, hc, true_and]
                simp [diaryChoices]
                grind

/-- The numerical recurrence is the length of an explicit grammar enumeration. -/
theorem diaryEnum_length (left : Bool) (m k : Nat) :
    (diaryEnum left m k).length = diaryCount left m k := by
  generalize he : 2 * m - k = budget
  induction budget using Nat.strongRecOn generalizing left m k with
  | ind budget ih =>
      rw [diaryEnum.eq_def, diaryCount.eq_def]
      by_cases hinvalid : m < k
      · simp [hinvalid]
      · simp only [hinvalid, ↓reduceDIte]
        cases m with
        | zero => cases k <;> simp
        | succ m =>
          cases k with
          | zero => simp
          | succ k =>
            have hsplit (b : Bool) := ih (2 * (m + 1) - (k + 2)) (by omega)
              b (m + 1) (k + 2) rfl
            have hleaf (b : Bool) := ih (2 * m - k) (by omega) b m k rfl
            have hcont := ih (2 * m - (k + 1)) (by omega) true m (k + 1) rfl
            cases left <;>
              simp only [↓reduceIte, List.length_append, diaryChoices_length,
                List.length_finRange, List.length_map, hsplit, hleaf, hcont]
            · rfl
            · simp only [Nat.two_mul, Nat.add_mul]
              omega

/-- Exact cardinality certificate for the event grammar, without any
external finite-set/cardinality library. -/
theorem diary_cardinality (left : Bool) (m k : Nat) :
    ∃ ds : List (Diary left m k), ds.Nodup ∧
      (∀ d : Diary left m k, d ∈ ds) ∧ ds.length = diaryCount left m k :=
  ⟨diaryEnum left m k, diaryEnum_nodup left m k,
    diaryEnum_complete, diaryEnum_length left m k⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Kernel-checked values of the recurrence (not a claim of Ramsey validation). -/
theorem diaryCount_first_five :
    (List.range 5).map (fun i => diaryCount true (i + 1) 1) =
      [1, 7, 157, 7927, 727741] := by
  decide +kernel

end AllThoseBigRamsey.Pseudotree
