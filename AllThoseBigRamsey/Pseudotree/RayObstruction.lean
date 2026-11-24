import AllThoseBigRamsey.Pseudotree.RayEmbeddings

/-!
# Why the mixed ray-preserving theorem permits only one ternary factor

The fixed two-colouring compares the last occurrences of `1`. For any two
ray-preserving maps with equal root length, the tuples of images of `(1,0)`
and `(0,1)` have opposite colours. This verifies the sharpness remark in the
manuscript; it does not assume a Ramsey theorem.
-/

namespace AllThoseBigRamsey.Pseudotree.RayEmbeddings

/-- One plus the position of the last `1`, with zero for a word having no `1`.
This natural-number convention is equivalent to using position `-1` in the
manuscript's comparison. -/
def lastOneEnd : Word → Nat
  | [] => 0
  | a :: s => if lastOneEnd s = 0 then (if a = 1 then 1 else 0) else lastOneEnd s + 1

theorem lastOneEnd_le_length (s : Word) : lastOneEnd s ≤ s.length := by
  induction s with
  | nil => simp [lastOneEnd]
  | cons a s ih =>
    simp only [lastOneEnd, List.length_cons]
    split
    · split <;> omega
    · omega

theorem lastOneEnd_eq_zero_of_binary {s : Word} (hs : Binary s) : lastOneEnd s = 0 := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨ha, hs⟩ := (binary_cons a s).mp hs
    simp [lastOneEnd, ih hs, ha]

theorem lastOneEnd_append_binary (s t : Word) (ht : Binary t) :
    lastOneEnd (s ++ t) = lastOneEnd s := by
  induction s with
  | nil => simpa only [List.nil_append, lastOneEnd] using lastOneEnd_eq_zero_of_binary ht
  | cons a s ih => simp only [List.cons_append, lastOneEnd, ih]

theorem lastOneEnd_append_one (s t : Word) :
    s.length + 1 ≤ lastOneEnd (s ++ (1 : Fin 3) :: t) := by
  induction s with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.zero_add, lastOneEnd]
    split
    · decide
    · omega
  | cons a s ih =>
    simp only [List.cons_append, lastOneEnd, List.length_cons]
    split <;> omega

theorem RayStrongMap.lastOneEnd_zero (f : RayStrongMap) :
    lastOneEnd (f.map [0]) ≤ f.level 0 := by
  obtain ⟨p, hp, hpb⟩ := f.step [] 0
  have hb : Binary ((0 : Fin 3) :: p) :=
    (binary_cons 0 p).mpr ⟨by decide, hpb (by decide)⟩
  have heq : f.map [0] = f.map [] ++ (0 : Fin 3) :: p := by simpa using hp
  rw [heq, lastOneEnd_append_binary _ _ hb]
  simpa only [f.length_map, List.length_nil] using lastOneEnd_le_length (f.map [])

theorem RayStrongMap.lastOneEnd_one (f : RayStrongMap) :
    f.level 0 < lastOneEnd (f.map [1]) := by
  obtain ⟨p, hp, _⟩ := f.step [] 1
  have heq : f.map [1] = f.map [] ++ (1 : Fin 3) :: p := by simpa using hp
  have h := lastOneEnd_append_one (f.map []) p
  rw [← heq, f.length_map] at h
  exact h

def lastOneColour (s t : Word) : Bool := decide (lastOneEnd t < lastOneEnd s)

/-- Even the first non-root source level forces both colours. Full
synchronization implies the root-length equality used here. -/
theorem two_ternary_obstruction (f g : RayStrongMap) (hsync : f.level 0 = g.level 0) :
    lastOneColour (f.map [1]) (g.map [0]) = true ∧
      lastOneColour (f.map [0]) (g.map [1]) = false := by
  have hf0 := f.lastOneEnd_zero
  have hf1 := f.lastOneEnd_one
  have hg0 := g.lastOneEnd_zero
  have hg1 := g.lastOneEnd_one
  constructor
  · apply decide_eq_true
    omega
  · apply decide_eq_false
    omega

end AllThoseBigRamsey.Pseudotree.RayEmbeddings
