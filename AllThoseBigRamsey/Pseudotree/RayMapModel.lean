import AllThoseBigRamsey.Pseudotree.Words
import AllThoseBigRamsey.Pseudotree.RayEmbeddings

/-!
# Ray-preserving strong maps are embeddings of the actual pseudotree

We identify the two literal alphabet representations, then prove order
reflection and meet preservation. Binary padding is reflected as well as
preserved: a retained `one` cannot disappear. The proof reduces a pair of
words to its first disagreement and keeps track of the initial binary
segment before the next `one`.
-/

namespace AllThoseBigRamsey.Pseudotree.RayMapModel

open RayEmbeddings

def toLetter (a : Fin 3) : TernaryLetter :=
  if a = 0 then .zero else if a = 1 then .one else .two

def toFin : TernaryLetter → Fin 3
  | .zero => 0
  | .one => 1
  | .two => 2

@[simp] theorem toLetter_toFin (a : TernaryLetter) : toLetter (toFin a) = a := by
  cases a <;> decide

@[simp] theorem toFin_toLetter (a : Fin 3) : toFin (toLetter a) = a := by
  by_cases h0 : a = 0
  · simp [toLetter, h0, toFin]
  by_cases h1 : a = 1
  · simp [toLetter, h1, toFin]
  have h2 : a = 2 := by
    apply Fin.ext
    have h0' : a.val ≠ 0 := fun h => h0 (Fin.ext h)
    have h1' : a.val ≠ 1 := fun h => h1 (Fin.ext h)
    omega
  simp [toLetter, h2, toFin]

@[simp] theorem toLetter_eq_one (a : Fin 3) : toLetter a = .one ↔ a = 1 := by
  constructor
  · intro h
    have hh := congrArg toFin h
    rw [toFin_toLetter] at hh
    exact hh
  · rintro rfl
    rfl

@[simp] theorem toFin_eq_one (a : TernaryLetter) : toFin a = 1 ↔ a = .one := by
  cases a <;> decide

def NoOne (s : List TernaryLetter) : Prop := ∀ a ∈ s, a ≠ .one

@[simp] theorem noOne_nil : NoOne [] := by simp [NoOne]

@[simp] theorem noOne_cons (a : TernaryLetter) (s : List TernaryLetter) :
    NoOne (a :: s) ↔ a ≠ .one ∧ NoOne s := by simp [NoOne]

@[simp] theorem noOne_append (s t : List TernaryLetter) :
    NoOne (s ++ t) ↔ NoOne s ∧ NoOne t := by
  simp only [NoOne, List.mem_append, or_imp, forall_and]

@[simp] theorem noOne_map (s : Word) : NoOne (s.map toLetter) ↔ Binary s := by
  simp [NoOne, Binary]

@[simp] theorem binary_map (s : List TernaryLetter) : Binary (s.map toFin) ↔ NoOne s := by
  simp [NoOne, Binary]

private theorem map_append_exact (f : RayStrongMap) (s t : Word) :
    ∃ padding : Word,
      f.map (s ++ t) = f.map s ++ padding ∧ (Binary padding ↔ Binary t) := by
  induction t generalizing s with
  | nil => exact ⟨[], by simp, Iff.rfl⟩
  | cons a t ih =>
      obtain ⟨p, hp, hpb⟩ := f.step s a
      obtain ⟨q, hq, hqb⟩ := ih (s ++ [a])
      refine ⟨a :: (p ++ q), ?_, ?_⟩
      · calc
          f.map (s ++ a :: t) = f.map ((s ++ [a]) ++ t) := by simp
          _ = f.map (s ++ [a]) ++ q := hq
          _ = f.map s ++ a :: (p ++ q) := by rw [hp]; simp
      · simp only [binary_cons, binary_append, hqb]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hpb h.1, h.2⟩⟩

private theorem map_append_cons_exact (f : RayStrongMap) (s : Word) (a : Fin 3) (t : Word) :
    ∃ padding : Word,
      f.map (s ++ a :: t) = f.map s ++ a :: padding ∧
      (a ≠ 1 → (Binary padding ↔ Binary t)) := by
  obtain ⟨p, hp, hpb⟩ := f.step s a
  obtain ⟨q, hq, hqb⟩ := map_append_exact f (s ++ [a]) t
  refine ⟨p ++ q, ?_, ?_⟩
  · calc
      f.map (s ++ a :: t) = f.map ((s ++ [a]) ++ t) := by simp
      _ = f.map (s ++ [a]) ++ q := hq
      _ = f.map s ++ a :: (p ++ q) := by rw [hp]; simp
  · intro ha
    simp [binary_append, hpb ha, hqb]

/-- The same map on the literal ternary-word representation of the model. -/
def act (f : RayStrongMap) (s : List TernaryLetter) : List TernaryLetter :=
  (f.map (s.map toFin)).map toLetter

private theorem act_append_cons (f : RayStrongMap)
    (s : List TernaryLetter) (a : TernaryLetter) (t : List TernaryLetter) :
    ∃ padding : List TernaryLetter,
      act f (s ++ a :: t) = act f s ++ a :: padding ∧
      (a ≠ .one → (NoOne padding ↔ NoOne t)) := by
  obtain ⟨p, hp, hpb⟩ := map_append_cons_exact f (s.map toFin) (toFin a) (t.map toFin)
  refine ⟨p.map toLetter, ?_, ?_⟩
  · simpa [act] using congrArg (List.map toLetter) hp
  · intro ha
    simpa using hpb (by simpa using ha)

private theorem noOne_iff_point (s : List TernaryLetter) :
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

private theorem below_cons_same (a : TernaryLetter) (s t : List TernaryLetter) :
    wordBelow (a :: s) (a :: t) ↔ wordBelow s t := by
  cases a <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp [wordBelow, parseWord, prependBlock, hs, ht, RayTree.Below, RayTree.first, binaryLE]

private theorem below_common_prefix (p s t : List TernaryLetter) :
    wordBelow (p ++ s) (p ++ t) ↔ wordBelow s t := by
  induction p with
  | nil => rfl
  | cons a p ih => simpa only [List.cons_append, below_cons_same] using ih

private theorem below_nil_cons (a : TernaryLetter) (t : List TernaryLetter) :
    wordBelow [] (a :: t) ↔ a ≠ .two := by
  cases a <;> cases h : parseWord t <;>
    simp [wordBelow, parseWord, prependBlock, h, RayTree.first, binaryLE]

private theorem below_cons_nil (a : TernaryLetter) (s : List TernaryLetter) :
    wordBelow (a :: s) [] ↔ a = .two ∧ NoOne s := by
  rw [noOne_iff_point]
  cases a <;> cases h : parseWord s <;>
    simp [wordBelow, parseWord, prependBlock, h, RayTree.first, binaryLE]

private theorem below_cons_distinct (a b : TernaryLetter) (s t : List TernaryLetter)
    (hab : a ≠ b) : wordBelow (a :: s) (b :: t) ↔ a = .two ∧ NoOne s := by
  rw [noOne_iff_point]
  cases a <;> cases b <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp_all [wordBelow, parseWord, prependBlock, RayTree.first, binaryLE]

/-- Every ray-preserving strong map preserves and reflects the actual
pseudotree order on literal ternary words. -/
theorem act_wordBelow (f : RayStrongMap) (s t : List TernaryLetter) :
    wordBelow (act f s) (act f t) ↔ wordBelow s t := by
  suffices h : ∀ s t u : List TernaryLetter,
      wordBelow (act f (u ++ s)) (act f (u ++ t)) ↔ wordBelow s t by
    simpa using h s t []
  intro s
  induction s with
  | nil =>
      intro t u
      cases t with
      | nil => simp only [List.append_nil]; exact ⟨fun _ => wordBelow_refl [], fun _ => wordBelow_refl _⟩
      | cons b t =>
          obtain ⟨p, hp, _⟩ := act_append_cons f u b t
          rw [hp, List.append_nil]
          have h := below_common_prefix (act f u) [] (b :: p)
          simpa only [List.append_nil, below_nil_cons] using h
  | cons a s ih =>
      intro t u
      cases t with
      | nil =>
          obtain ⟨p, hp, hpb⟩ := act_append_cons f u a s
          rw [hp, List.append_nil]
          have h := below_common_prefix (act f u) (a :: p) []
          simp only [List.append_nil, below_cons_nil] at h ⊢
          rw [h]
          cases a <;> simp [hpb]
      | cons b t =>
          by_cases hab : a = b
          · subst b
            simpa only [List.append_assoc, List.singleton_append, below_cons_same] using
              ih t (u ++ [a])
          · obtain ⟨p, hp, hpb⟩ := act_append_cons f u a s
            obtain ⟨q, hq, _⟩ := act_append_cons f u b t
            rw [hp, hq, below_common_prefix, below_cons_distinct a b p q hab,
              below_cons_distinct a b s t hab]
            cases a <;> simp [hpb]

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

private theorem meet_cons_same (a : TernaryLetter) (s t : List TernaryLetter) :
    wordMeet (a :: s) (a :: t) = a :: wordMeet s t := by
  cases a
  · simp only [wordMeet, parseWord, meet_prependBlock, printWord_prependBlock]
    rfl
  · simp [wordMeet, parseWord, RayTree.meet, printWord]
  · simp only [wordMeet, parseWord, meet_prependBlock, printWord_prependBlock]
    rfl

private theorem meet_common_prefix (p s t : List TernaryLetter) :
    wordMeet (p ++ s) (p ++ t) = p ++ wordMeet s t := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.cons_append, meet_cons_same, ih]

/-- The binary initial segment before the first `one`. -/
def headBinary : List TernaryLetter → List TernaryLetter
  | [] => []
  | .zero :: s => .zero :: headBinary s
  | .one :: _ => []
  | .two :: s => .two :: headBinary s

private theorem headBinary_first (s : List TernaryLetter) :
    headBinary s = (parseWord s).first.map binaryLetter := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      cases h : parseWord s <;> cases a <;>
        simp_all [headBinary, parseWord, prependBlock, RayTree.first, binaryLetter]

private theorem headBinary_cons (a : TernaryLetter) (s : List TernaryLetter)
    (ha : a ≠ .one) : headBinary (a :: s) = a :: headBinary s := by
  cases a <;> simp_all [headBinary]

private theorem headBinary_append (s t : List TernaryLetter) (hs : NoOne s) :
    headBinary (s ++ t) = s ++ headBinary t := by
  induction s with
  | nil => rfl
  | cons a s ih =>
      obtain ⟨ha, hs⟩ := (noOne_cons a s).mp hs
      simp only [List.cons_append, headBinary_cons _ _ ha, ih hs]

private theorem act_headBinary (f : RayStrongMap) (u s : List TernaryLetter) :
    ∃ p : List TernaryLetter,
      act f (u ++ s) = act f u ++ p ∧
      act f (u ++ headBinary s) = act f u ++ headBinary p := by
  induction s generalizing u with
  | nil => exact ⟨[], by simp, by simp [headBinary]⟩
  | cons a s ih =>
      by_cases ha : a = .one
      · subst a
        obtain ⟨p, hp, _⟩ := act_append_cons f u .one s
        exact ⟨.one :: p, hp, by simp [headBinary]⟩
      · obtain ⟨p, hp, hpb⟩ := act_append_cons f u a []
        obtain ⟨q, hq, hh⟩ := ih (u ++ [a])
        have hbin : NoOne p := (hpb ha).mpr noOne_nil
        refine ⟨a :: (p ++ q), ?_, ?_⟩
        · calc
            act f (u ++ a :: s) = act f ((u ++ [a]) ++ s) := by simp
            _ = act f (u ++ [a]) ++ q := hq
            _ = act f u ++ a :: (p ++ q) := by rw [hp]; simp
        · calc
            act f (u ++ headBinary (a :: s)) =
                act f ((u ++ [a]) ++ headBinary s) := by rw [headBinary_cons _ _ ha]; simp
            _ = act f (u ++ [a]) ++ headBinary q := hh
            _ = act f u ++ headBinary (a :: (p ++ q)) := by
              rw [hp, headBinary_cons _ _ ha, headBinary_append p q hbin]
              simp

private theorem act_headBinary_of_eq (f : RayStrongMap) (u s p : List TernaryLetter)
    (hp : act f (u ++ s) = act f u ++ p) :
    act f (u ++ headBinary s) = act f u ++ headBinary p := by
  obtain ⟨q, hq, hh⟩ := act_headBinary f u s
  have heq : q = p := List.append_cancel_left (hq.symm.trans hp)
  simpa only [heq] using hh

private theorem meet_nil_cons (a : TernaryLetter) (t : List TernaryLetter) :
    wordMeet [] (a :: t) = if a = .two then headBinary (a :: t) else [] := by
  rw [headBinary_first]
  cases a <;> cases h : parseWord t <;>
    simp [wordMeet, parseWord, prependBlock, h, RayTree.first, RayTree.meet,
      binaryMin, binaryLE, printWord, binaryLetter]

private theorem meet_cons_nil (a : TernaryLetter) (s : List TernaryLetter) :
    wordMeet (a :: s) [] = if a = .two then headBinary (a :: s) else [] := by
  rw [headBinary_first]
  cases a <;> cases h : parseWord s <;>
    simp [wordMeet, parseWord, prependBlock, h, RayTree.first, RayTree.meet,
      binaryMin, binaryLE, printWord, binaryLetter]

private theorem meet_cons_distinct (a b : TernaryLetter) (s t : List TernaryLetter)
    (hab : a ≠ b) :
    wordMeet (a :: s) (b :: t) =
      if a = .two then headBinary (a :: s)
      else if b = .two then headBinary (b :: t) else [] := by
  rw [headBinary_first, headBinary_first]
  cases a <;> cases b <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp_all [wordMeet, parseWord, prependBlock, RayTree.first, RayTree.meet,
      binaryMin, binaryLE, printWord, binaryLetter]

/-- The same local conditions also preserve the manuscript's meet operation. -/
theorem act_wordMeet (f : RayStrongMap) (s t : List TernaryLetter) :
    wordMeet (act f s) (act f t) = act f (wordMeet s t) := by
  suffices h : ∀ s t u : List TernaryLetter,
      wordMeet (act f (u ++ s)) (act f (u ++ t)) = act f (u ++ wordMeet s t) by
    simpa using h s t []
  intro s
  induction s with
  | nil =>
      intro t u
      cases t with
      | nil =>
          have hmeet : wordMeet (act f u) (act f u) = act f u := by
            apply wordBelow_antisymm
            · exact ((wordBelow_meet_iff _ _ _).mp (wordBelow_refl _)).1
            · exact (wordBelow_meet_iff _ _ _).mpr ⟨wordBelow_refl _, wordBelow_refl _⟩
          simpa [wordMeet, parseWord, RayTree.meet, binaryMin, printWord] using hmeet
      | cons b t =>
          obtain ⟨p, hp, _⟩ := act_append_cons f u b t
          have hh := act_headBinary_of_eq f u (b :: t) (b :: p) hp
          rw [hp, List.append_nil]
          have hmeet := meet_common_prefix (act f u) [] (b :: p)
          simp only [List.append_nil, meet_nil_cons] at hmeet ⊢
          rw [hmeet]
          cases b with
          | zero => simp
          | one => simp
          | two => simpa using hh.symm
  | cons a s ih =>
      intro t u
      cases t with
      | nil =>
          obtain ⟨p, hp, _⟩ := act_append_cons f u a s
          have hh := act_headBinary_of_eq f u (a :: s) (a :: p) hp
          rw [hp, List.append_nil]
          have hmeet := meet_common_prefix (act f u) (a :: p) []
          simp only [List.append_nil, meet_cons_nil] at hmeet ⊢
          rw [hmeet]
          cases a with
          | zero => simp
          | one => simp
          | two => simpa using hh.symm
      | cons b t =>
          by_cases hab : a = b
          · subst b
            simpa only [List.append_assoc, List.singleton_append, meet_cons_same] using
              ih t (u ++ [a])
          · obtain ⟨p, hp, _⟩ := act_append_cons f u a s
            obtain ⟨q, hq, _⟩ := act_append_cons f u b t
            have hs := act_headBinary_of_eq f u (a :: s) (a :: p) hp
            have ht := act_headBinary_of_eq f u (b :: t) (b :: q) hq
            rw [hp, hq, meet_common_prefix, meet_cons_distinct a b p q hab,
              meet_cons_distinct a b s t hab]
            by_cases ha : a = .two
            · simpa [ha] using hs.symm
            · by_cases hb : b = .two
              · simpa [ha, hb] using ht.symm
              · simp [ha, hb]

theorem act_injective (f : RayStrongMap) : Function.Injective (act f) := by
  intro s t heq
  apply wordBelow_antisymm
  · apply (act_wordBelow f s t).mp
    rw [heq]
    exact wordBelow_refl _
  · apply (act_wordBelow f t s).mp
    rw [heq]
    exact wordBelow_refl _

@[simp] theorem act_length (f : RayStrongMap) (s : List TernaryLetter) :
    (act f s).length = f.level s.length := by
  simp [act, f.length_map]

end AllThoseBigRamsey.Pseudotree.RayMapModel
