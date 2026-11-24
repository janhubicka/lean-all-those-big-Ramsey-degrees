import Std

/-!
# Oscillation on finite subsets of the natural numbers

A finite subset is represented by its finite binary characteristic word.
Trailing `false` entries are harmless. `differenceWord s t` lists, in order,
which of the two sets contains each point of their symmetric difference.
The oscillation is the number of constant runs in this word.

The end-extension hypothesis below is the elementary, topology-free form of
having no isolated points in FIN. The theorem in this file proves the
oscillation lemma itself; the pseudotree profile construction is separate.
-/

namespace AllThoseBigRamsey.Pseudotree.Oscillation

def differenceWord : List Bool → List Bool → List Bool
  | [], [] => []
  | a :: s, [] => (if a then [true] else []) ++ differenceWord s []
  | [], b :: t => (if b then [false] else []) ++ differenceWord [] t
  | a :: s, b :: t => (if a == b then [] else [a]) ++ differenceWord s t

def runCountFrom (previous : Option Bool) : List Bool → Nat
  | [] => 0
  | a :: s => (if previous = some a then 0 else 1) + runCountFrom (some a) s

def lastFrom (previous : Option Bool) : List Bool → Option Bool
  | [] => previous
  | a :: s => lastFrom (some a) s

def oscillation (s t : List Bool) : Nat :=
  runCountFrom none (differenceWord s t)

@[simp] theorem differenceWord_self (s : List Bool) : differenceWord s s = [] := by
  induction s with
  | nil => simp [differenceWord]
  | cons a s ih => simp [differenceWord, ih]

@[simp] theorem runCountFrom_nil (p : Option Bool) : runCountFrom p [] = 0 := rfl

@[simp] theorem lastFrom_nil (p : Option Bool) : lastFrom p [] = p := rfl

@[simp] theorem lastFrom_cons (p : Option Bool) (a : Bool) (s : List Bool) :
    lastFrom p (a :: s) = lastFrom (some a) s := rfl

theorem runCountFrom_append (p : Option Bool) (s t : List Bool) :
    runCountFrom p (s ++ t) = runCountFrom p s + runCountFrom (lastFrom p s) t := by
  induction s generalizing p with
  | nil => simp [runCountFrom]
  | cons a s ih => simp [runCountFrom, ih, Nat.add_assoc]

theorem runCountFrom_replicate_same (a : Bool) (n : Nat) :
    runCountFrom (some a) (List.replicate n a) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, runCountFrom, ih]

theorem runCountFrom_replicate (p : Option Bool) (a : Bool) (n : Nat)
    (hn : 0 < n) (hp : p ≠ some a) :
    runCountFrom p (List.replicate n a) = 1 := by
  cases n with
  | zero => omega
  | succ n => simp [List.replicate_succ, runCountFrom, hp, runCountFrom_replicate_same]

theorem differenceWord_swap (s t : List Bool) :
    differenceWord t s = (differenceWord s t).map Bool.not := by
  induction s generalizing t with
  | nil =>
    induction t with
    | nil => simp
    | cons a t ih => cases a <;> simp [differenceWord, ih]
  | cons a s ih =>
    cases t with
    | nil => cases a <;> simp [differenceWord, ih]
    | cons b t => cases a <;> cases b <;> simp [differenceWord, ih]

theorem runCountFrom_not (p : Option Bool) (s : List Bool) :
    runCountFrom (p.map Bool.not) (s.map Bool.not) = runCountFrom p s := by
  induction s generalizing p with
  | nil => rfl
  | cons a s ih =>
    have ih' := ih (some a)
    simp only [Option.map_some] at ih'
    cases p with
    | none => simp [runCountFrom, ih']
    | some b => cases a <;> cases b <;> simp [runCountFrom] <;> exact ih'

theorem oscillation_symm (s t : List Bool) : oscillation t s = oscillation s t := by
  unfold oscillation
  rw [differenceWord_swap s t]
  exact runCountFrom_not none _

theorem differenceWord_zero_left (n : Nat) (t : List Bool) :
    differenceWord (List.replicate n false) t = differenceWord [] t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    cases t with
    | nil => simp [List.replicate_succ, differenceWord, ih]
    | cons b t => cases b <;> simp [List.replicate_succ, differenceWord, ih]

theorem differenceWord_pad_left (s t : List Bool) (n : Nat) :
    differenceWord (s ++ List.replicate n false) t = differenceWord s t := by
  induction s generalizing t with
  | nil => exact differenceWord_zero_left n t
  | cons a s ih =>
    cases t with
    | nil => cases a <;> simp [differenceWord, ih]
    | cons b t => cases a <;> cases b <;> simp [differenceWord, ih]

def trueCount (s : List Bool) : Nat := s.count true

theorem differenceWord_nil_right (s : List Bool) :
    differenceWord s [] = List.replicate (trueCount s) true := by
  induction s with
  | nil => simp [trueCount]
  | cons a s ih => cases a <;> simp [differenceWord, trueCount, List.replicate_succ, ih]

theorem differenceWord_append_of_length (s t u : List Bool)
    (h : t.length ≤ s.length) :
    differenceWord (s ++ u) t = differenceWord s t ++ differenceWord u [] := by
  induction s generalizing t with
  | nil =>
    have ht : t = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst t
    simp
  | cons a s ih =>
    cases t with
    | nil => cases a <;> simp [differenceWord, ih [] (by simp)]
    | cons b t =>
      have h' : t.length ≤ s.length := by simpa using h
      cases a <;> cases b <;> simp [differenceWord, ih t h']

theorem differenceWord_extend_left (s t u : List Bool) (N : Nat)
    (h : t.length ≤ s.length + N) :
    differenceWord (s ++ List.replicate N false ++ u) t =
      differenceWord s t ++ List.replicate (trueCount u) true := by
  rw [differenceWord_append_of_length (s ++ List.replicate N false) t u (by simpa using h)]
  rw [differenceWord_pad_left, differenceWord_nil_right]

/-- If the first finite set is contained in the second, all symmetric-
difference points belong to the second set, so there is at most one run. -/
theorem differenceWord_subset (s t : List Bool)
    (hsub : ∀ i : Nat, s[i]? = some true → t[i]? = some true) :
    ∃ n, differenceWord s t = List.replicate n false := by
  induction s generalizing t with
  | nil =>
    refine ⟨trueCount t, ?_⟩
    rw [differenceWord_swap t [], differenceWord_nil_right]
    simp
  | cons a s ih =>
    cases t with
    | nil =>
      have hhead := hsub 0
      cases a with
      | true => simp at hhead
      | false =>
        have ht : ∀ i : Nat, s[i]? = some true → ([] : List Bool)[i]? = some true := by
          intro i hi
          have hh := hsub (i + 1) (by simpa using hi)
          simp at hh
        obtain ⟨n, hn⟩ := ih [] ht
        exact ⟨n, by simpa [differenceWord] using hn⟩
    | cons b t =>
      have ht : ∀ i : Nat, s[i]? = some true → t[i]? = some true := by
        intro i hi
        have hh := hsub (i + 1) (by simpa using hi)
        simpa using hh
      obtain ⟨n, hn⟩ := ih t ht
      have hhead := hsub 0
      cases a <;> cases b
      · exact ⟨n, by simpa [differenceWord] using hn⟩
      · exact ⟨n + 1, by simp [differenceWord, hn, List.replicate_succ]⟩
      · simp at hhead
      · exact ⟨n, by simpa [differenceWord] using hn⟩

theorem oscillation_le_one_of_subset (s t : List Bool)
    (hsub : ∀ i : Nat, s[i]? = some true → t[i]? = some true) : oscillation s t ≤ 1 := by
  obtain ⟨n, hn⟩ := differenceWord_subset s t hsub
  unfold oscillation
  rw [hn]
  cases n with
  | zero => simp
  | succ n =>
    rw [runCountFrom_replicate none false (n + 1) (by omega) (by decide)]
    exact Nat.le_refl 1

theorem lastFrom_append (p : Option Bool) (s t : List Bool) :
    lastFrom p (s ++ t) = lastFrom (lastFrom p s) t := by
  induction s generalizing p with
  | nil => rfl
  | cons a s ih => simpa only [List.cons_append, lastFrom_cons] using ih (some a)

theorem lastFrom_replicate (p : Option Bool) (a : Bool) (n : Nat) (hn : 0 < n) :
    lastFrom p (List.replicate n a) = some a := by
  induction n generalizing p with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n => simpa only [List.replicate_succ, lastFrom_cons] using ih (some a) (by omega)

theorem lastFrom_not (p : Option Bool) (s : List Bool) :
    lastFrom (p.map Bool.not) (s.map Bool.not) = (lastFrom p s).map Bool.not := by
  induction s generalizing p with
  | nil => rfl
  | cons a s ih => simpa only [List.map_cons, lastFrom_cons, Option.map_some] using ih (some a)

/-- Every finite initial segment can be retained while adding a nonempty new tail. -/
def EndExtensions (X : List Bool → Prop) : Prop :=
  ∀ s, X s → ∀ N, ∃ u, true ∈ u ∧ X (s ++ List.replicate N false ++ u)

/-- The elementary oscillation lemma, including the zero case. -/
theorem all_oscillations (X : List Bool → Prop)
    (hne : ∃ s, X s) (hext : EndExtensions X) (k : Nat) :
    ∃ s t, X s ∧ X t ∧ oscillation s t = k := by
  suffices hs : ∀ k, ∃ s t, X s ∧ X t ∧ oscillation s t = k ∧
      lastFrom none (differenceWord s t) ≠ some true by
    obtain ⟨s, t, hs, ht, hk, _⟩ := hs k
    exact ⟨s, t, hs, ht, hk⟩
  intro k
  induction k with
  | zero =>
    obtain ⟨s, hs⟩ := hne
    exact ⟨s, s, hs, hs, by simp [oscillation], by simp⟩
  | succ k ih =>
    obtain ⟨s, t, hs, ht, hk, hlast⟩ := ih
    obtain ⟨u, hu, hsu⟩ := hext s hs t.length
    let s' := s ++ List.replicate t.length false ++ u
    have hn : 0 < trueCount u := by simpa [trueCount] using List.count_pos_iff.mpr hu
    have hd : differenceWord s' t = differenceWord s t ++ List.replicate (trueCount u) true :=
      differenceWord_extend_left s t u t.length (by omega)
    have hcount : oscillation s' t = k + 1 := by
      simp only [oscillation, hd, runCountFrom_append]
      rw [runCountFrom_replicate _ true _ hn hlast]
      exact congrArg (fun n => n + 1) hk
    have hlast' : lastFrom none (differenceWord s' t) = some true := by
      rw [hd, lastFrom_append, lastFrom_replicate _ true _ hn]
    refine ⟨t, s', ht, hsu, ?_, ?_⟩
    · rw [oscillation_symm]
      exact hcount
    · rw [differenceWord_swap]
      have hh := lastFrom_not none (differenceWord s' t)
      simp only [Option.map_none] at hh
      rw [hh, hlast']
      decide

end AllThoseBigRamsey.Pseudotree.Oscillation
