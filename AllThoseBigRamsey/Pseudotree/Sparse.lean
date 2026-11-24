import AllThoseBigRamsey.Pseudotree.Words

/-!
# The literal queue in the sparse-copy construction

This is the three-level stage from Lemma 5.2 of the note. The queue is not
lexicographically sorted: it is a fair scheduling queue. At a stage, each
unselected word receives three 0s or three 2s according to its position
relative to the selected word; three new intervals are appended to the queue.

The module checks the length/level invariants and the origin of every `1`.
The infinite copy's rational-ray and diary-extraction properties are separate
obligations, not hypotheses disguised as proved consequences of this program.
-/

namespace AllThoseBigRamsey.Pseudotree.Sparse

abbrev Word := List TernaryLetter

def rank : TernaryLetter → Nat
  | .zero => 0
  | .one => 1
  | .two => 2

def lexLess : Word → Word → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: s, b :: t => if rank a = rank b then lexLess s t else decide (rank a < rank b)

def pad (u w : Word) : Word :=
  w ++ List.replicate 3 (if lexLess w u then .zero else .two)

def newCode (u : Word) : Word := u ++ [.zero, .two]

def newSlots (u : Word) : List Word :=
  [u ++ [.zero, .zero, .zero], u ++ [.zero, .two, .one], u ++ [.two, .two, .two]]

structure Stage where
  active : List Word
  codes : List Word

def advance (s : Stage) : Stage :=
  match s.active with
  | [] => s
  | u :: rest => ⟨rest.map (pad u) ++ newSlots u, s.codes ++ [newCode u]⟩

def stage : Nat → Stage
  | 0 => ⟨[[]], []⟩
  | n + 1 => advance (stage n)

theorem stage_lengths (n : Nat) :
    (stage n).active.length = 2 * n + 1 ∧ (stage n).codes.length = n := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    have hn : (stage n).active ≠ [] := by
      intro h
      simp [h] at ih
    obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
    simp [stage, advance, ha, newSlots]
    have hlen : rest.length = 2 * n := by simpa [ha] using ih.1
    omega

theorem active_length (n : Nat) : ∀ w ∈ (stage n).active, w.length = 3 * n := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    have hn : (stage n).active ≠ [] := by
      intro h
      have hl := (stage_lengths n).1
      simp [h] at hl
    obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
    have hu : u.length = 3 * n := ih u (by simp [ha])
    intro w hw
    simp only [stage, advance, ha] at hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
      have hvlen := ih v (by simp [ha, hv])
      simp [pad, hvlen, Nat.mul_add]
    · simp only [newSlots, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> simp [hu, Nat.mul_add]

/-- Prefixes just before occurrences of `1`, excluding the whole word. -/
def onePrefixes : Word → List Word
  | [] => []
  | a :: w => (if a = .one then [[]] else []) ++ (onePrefixes w).map (List.cons a)

theorem onePrefixes_append (s t : Word) :
    onePrefixes (s ++ t) = onePrefixes s ++ (onePrefixes t).map (s ++ ·) := by
  induction s with
  | nil => simp [onePrefixes]
  | cons a s ih =>
    simp [onePrefixes, ih, List.map_append, List.map_map, Function.comp_def,
      List.append_assoc]

theorem onePrefixes_pad (u w : Word) : onePrefixes (pad u w) = onePrefixes w := by
  unfold pad
  rw [onePrefixes_append]
  cases lexLess w u <;> simp [onePrefixes, List.replicate_succ]

theorem onePrefixes_newCode (u : Word) : onePrefixes (newCode u) = onePrefixes u := by
  simp [newCode, onePrefixes_append, onePrefixes]

def Origins (s : Stage) : Prop :=
  (∀ w ∈ s.active, ∀ p ∈ onePrefixes w, p ∈ s.codes) ∧
  (∀ w ∈ s.codes, ∀ p ∈ onePrefixes w, p ∈ s.codes)

theorem advance_origins (s : Stage) (hs : Origins s) : Origins (advance s) := by
  cases ha : s.active with
  | nil => simpa [advance, ha] using hs
  | cons u rest =>
    have hu : u ∈ s.active := by simp [ha]
    have old : ∀ p ∈ s.codes, p ∈ s.codes ++ [newCode u] := by
      intro p hp
      exact List.mem_append_left _ hp
    simp only [Origins, advance, ha]
    constructor
    · intro w hw p hp
      change w ∈ rest.map (pad u) ++ newSlots u at hw
      change p ∈ s.codes ++ [newCode u]
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
        rw [onePrefixes_pad] at hp
        exact old p (hs.1 v (by simp [ha, hv]) p hp)
      · simp only [newSlots, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · simp [onePrefixes_append, onePrefixes] at hp
          exact old p (hs.1 u hu p hp)
        · simp [onePrefixes_append, onePrefixes] at hp
          rcases hp with hp | hp
          · exact old p (hs.1 u hu p hp)
          · subst p
            simp [newCode]
        · simp [onePrefixes_append, onePrefixes] at hp
          exact old p (hs.1 u hu p hp)
    · intro w hw p hp
      change w ∈ s.codes ++ [newCode u] at hw
      change p ∈ s.codes ++ [newCode u]
      rcases List.mem_append.mp hw with hw | hw
      · exact old p (hs.2 w hw p hp)
      · have hw' : w = newCode u := List.mem_singleton.mp hw
        rw [hw', onePrefixes_newCode] at hp
        exact old p (hs.1 u hu p hp)

/-- Every `1` in a scheduled word or a coding node begins immediately after
an earlier coding node. -/
theorem stage_origins (n : Nat) : Origins (stage n) := by
  induction n with
  | zero => simp [stage, Origins, onePrefixes]
  | succ n ih => exact advance_origins _ ih

def code (n : Nat) : Word := newCode ((stage n).active.head!)

theorem code_length (n : Nat) : (code n).length = 3 * n + 2 := by
  have hn : (stage n).active ≠ [] := by
    intro h
    have hl := (stage_lengths n).1
    simp [h] at hl
  obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
  have hu := active_length n u (by simp [ha])
  simpa [code, ha, newCode, List.head!] using hu

/-- In particular, distinct stages produce distinct coding nodes. -/
theorem code_injective {n m : Nat} (h : code n = code m) : n = m := by
  have hh := congrArg List.length h
  rw [code_length, code_length] at hh
  omega

theorem stage_codes_succ (n : Nat) :
    (stage (n + 1)).codes = (stage n).codes ++ [code n] := by
  have hn : (stage n).active ≠ [] := by
    intro h
    have hl := (stage_lengths n).1
    simp [h] at hl
  obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
  simp [stage, advance, code, ha, List.head!]

/-- The finite code list is precisely the initial segment of the infinite
sequence, with the direction of the equality convenient for rewriting. -/
theorem mem_stage_codes_iff (n : Nat) (w : Word) :
    w ∈ (stage n).codes ↔ ∃ j, j < n ∧ w = code j := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    rw [stage_codes_succ, List.mem_append, List.mem_singleton, ih]
    constructor
    · rintro (⟨j, hj, hw⟩ | hw)
      · exact ⟨j, by omega, hw⟩
      · exact ⟨n, by omega, hw⟩
    · rintro ⟨j, hj, hw⟩
      by_cases h : j < n
      · exact Or.inl ⟨j, h, hw⟩
      · have heq : j = n := by omega
        subst j
        exact Or.inr hw

theorem code_mem_next (n : Nat) : code n ∈ (stage (n + 1)).codes := by
  rw [stage_codes_succ]
  simp

theorem code_onePrefixes_earlier (n : Nat) (p : Word)
    (hp : p ∈ onePrefixes (code n)) : ∃ j, j < n ∧ p = code j := by
  have hn : (stage n).active ≠ [] := by
    intro h
    have hl := (stage_lengths n).1
    simp [h] at hl
  obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
  have hu : u ∈ (stage n).active := by simp [ha]
  have hp' : p ∈ onePrefixes u := by
    simpa only [code, ha, List.head!, onePrefixes_newCode] using hp
  exact (mem_stage_codes_iff n p).1 ((stage_origins n).1 u hu p hp')

/-- An entry at queue position `i` is selected after exactly `i` stages,
up to the prescribed binary padding accumulated while waiting. -/
theorem queued_prefix_code (i n : Nat) (hi : i < (stage n).active.length) :
    ((stage n).active[i]).IsPrefix (code (n + i)) := by
  induction i generalizing n with
  | zero =>
    have hn : (stage n).active ≠ [] := by
      intro h
      simp [h] at hi
    obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
    simp [ha, code, List.head!, newCode]
  | succ i ih =>
    have hn : (stage n).active ≠ [] := by
      intro h
      simp [h] at hi
    obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
    have hir : i < rest.length := by simpa [ha] using hi
    have hnext : (stage (n + 1)).active = rest.map (pad u) ++ newSlots u := by
      simp [stage, advance, ha]
    have hinext : i < (stage (n + 1)).active.length := by simp [hnext, newSlots]; omega
    have hget : (stage (n + 1)).active[i] = pad u rest[i] := by
      simp [hnext, List.getElem_append_left, hir]
    have hp := ih (n + 1) hinext
    rw [hget] at hp
    have hpad : rest[i].IsPrefix (pad u rest[i]) := ⟨_, rfl⟩
    have hfinal := hpad.trans hp
    simpa only [ha, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using hfinal

/-- Every scheduled interval receives a coding node after finitely many stages. -/
theorem every_active_eventually_coded (n : Nat) (w : Word) (hw : w ∈ (stage n).active) :
    ∃ m, n ≤ m ∧ m ≤ 3 * n ∧ w.IsPrefix (code m) := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hw
  have hlen := (stage_lengths n).1
  refine ⟨n + i, by omega, by omega, ?_⟩
  rw [← heq]
  exact queued_prefix_code i n hi

end AllThoseBigRamsey.Pseudotree.Sparse
