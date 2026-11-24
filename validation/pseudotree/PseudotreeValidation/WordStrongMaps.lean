import PseudotreeValidation.WordTrees

/-!
# Library strong subtrees as letter-preserving word maps

The library's strong subtrees are sets with selected levels.  This module
recursively labels each selected successor by its original immediate child,
obtaining exactly the letter-preserving strong maps used in the manuscript.
The predecessor clause rules out unlabelled nodes: every node of the library
subtree is realized by a word of the corresponding source length.
-/

namespace AllThoseBigRamsey.Pseudotree.WordTrees

open Milliken Milliken.GeneralTree

/-- The local level-and-edge definition of an ordinary strong word map.
There is no ray-preservation restriction on its inserted letters. -/
structure StrongWordMap (α : Type) where
  map : List α → List α
  level : ℕ → ℕ
  level_strict : StrictMono level
  length_map : ∀ s, (map s).length = level s.length
  step : ∀ s a, map s ++ [a] <+: map (s ++ [a])

namespace StrongWordMap

variable {α : Type} (f : StrongWordMap α)

theorem map_append (s t : List α) : f.map s <+: f.map (s ++ t) := by
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t a ih =>
      simpa only [List.append_assoc] using
        ih.trans ((List.prefix_append _ _).trans (f.step (s ++ t) a))

theorem map_append_cons (s : List α) (a : α) (t : List α) :
    ∃ padding, f.map (s ++ a :: t) = f.map s ++ a :: padding := by
  obtain ⟨p, hp⟩ := f.step s a
  obtain ⟨q, hq⟩ := f.map_append (s ++ [a]) t
  refine ⟨p ++ q, ?_⟩
  calc
    f.map (s ++ a :: t) = f.map ((s ++ [a]) ++ t) := by simp
    _ = f.map (s ++ [a]) ++ q := hq.symm
    _ = f.map s ++ a :: (p ++ q) := by rw [← hp]; simp

private theorem injective_at_level (n : ℕ) :
    ∀ s t u : List α, s.length = n → t.length = n →
      f.map (u ++ s) = f.map (u ++ t) → s = t := by
  induction n with
  | zero =>
      intro s t u hs ht _
      have hs' : s = [] := List.length_eq_zero_iff.mp hs
      have ht' : t = [] := List.length_eq_zero_iff.mp ht
      simp [hs', ht']
  | succ n ih =>
      intro s t u hs ht h
      cases s with
      | nil => simp at hs
      | cons a s =>
          cases t with
          | nil => simp at ht
          | cons b t =>
              obtain ⟨p, hp⟩ := f.map_append_cons u a s
              obtain ⟨q, hq⟩ := f.map_append_cons u b t
              have hab : a = b := by
                rw [hp, hq] at h
                exact (List.cons.inj (List.append_cancel_left h)).1
              subst b
              have hst := ih s t (u ++ [a]) (by simpa using hs) (by simpa using ht)
                (by simpa using h)
              simp [hst]

/-- Letter preservation and a strict level map imply injectivity. -/
theorem injective : Function.Injective f.map := by
  intro s t h
  have hlevels : f.level s.length = f.level t.length := by
    simpa only [f.length_map] using congrArg List.length h
  have hlen := f.level_strict.injective hlevels
  exact f.injective_at_level s.length s t [] rfl hlen.symm (by simpa using h)

/-- Place a strong map above an arbitrary prescribed word root. -/
def prepend (root : List α) : StrongWordMap α where
  map s := root ++ f.map s
  level n := root.length + f.level n
  level_strict := fun _ _ h => Nat.add_lt_add_left (f.level_strict h) _
  length_map s := by simp [f.length_map]
  step s a := by
    obtain ⟨p, hp⟩ := f.step s a
    exact ⟨p, by simpa only [List.append_assoc] using congrArg (fun t : List α => root ++ t) hp⟩

end StrongWordMap

section LabelSubtree

variable {α : Type} [Finite α] [Nonempty α] [DecidableEq α]
variable (S : StrongSubtree (ambientTree α))

private structure Cursor where
  depth : ℕ
  node : Node α
  onLevel : node ∈ S.sourceLevel depth

private noncomputable def nextCursor (c : Cursor S) (a : α) : Cursor S := by
  let h := S.successor_unique c.depth c.node c.onLevel.1 c.onLevel.2
    ⟨c.node.letters ++ [a]⟩ (append_singleton_covBy c.node.letters a)
  exact ⟨c.depth + 1, h.choose, h.choose_spec.1.1, h.choose_spec.1.2.1⟩

private theorem nextCursor_depth (c : Cursor S) (a : α) :
    (nextCursor S c a).depth = c.depth + 1 := rfl

private theorem nextCursor_step (c : Cursor S) (a : α) :
    c.node.letters ++ [a] <+: (nextCursor S c a).node.letters := by
  exact (S.successor_unique c.depth c.node c.onLevel.1 c.onLevel.2
    ⟨c.node.letters ++ [a]⟩ (append_singleton_covBy c.node.letters a)).choose_spec.1.2.2

private theorem nextCursor_unique (c : Cursor S) (a : α) (z : Node α)
    (hz : z ∈ S.sourceLevel (c.depth + 1))
    (hprefix : c.node.letters ++ [a] <+: z.letters) :
    z = (nextCursor S c a).node := by
  exact (S.successor_unique c.depth c.node c.onLevel.1 c.onLevel.2
    ⟨c.node.letters ++ [a]⟩ (append_singleton_covBy c.node.letters a)).choose_spec.2
      z ⟨hz.1, hz.2, hprefix⟩

private noncomputable def wordCursor (s : List α) : Cursor S :=
  s.foldl (nextCursor S) ⟨0, S.root, S.root_mem, S.root_level⟩

private theorem wordCursor_snoc (s : List α) (a : α) :
    wordCursor S (s ++ [a]) = nextCursor S (wordCursor S s) a := by
  simp only [wordCursor, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem wordCursor_depth (s : List α) : (wordCursor S s).depth = s.length := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s a ih =>
      rw [wordCursor_snoc, nextCursor_depth, ih]
      simp

/-- Recursively take the unique selected successor in each original
letter cone. -/
noncomputable def subtreeWordMap (s : List α) : List α := (wordCursor S s).node.letters

@[simp] theorem subtreeWordMap_nil : subtreeWordMap S [] = S.root.letters := rfl

theorem subtreeWordMap_onLevel (s : List α) :
    (⟨subtreeWordMap S s⟩ : Node α) ∈ S.sourceLevel s.length := by
  have h := (wordCursor S s).onLevel
  rwa [wordCursor_depth] at h

theorem subtreeWordMap_length (s : List α) :
    (subtreeWordMap S s).length = S.levels s.length := by
  simpa only [level_eq_length] using (subtreeWordMap_onLevel S s).2

theorem subtreeWordMap_step (s : List α) (a : α) :
    subtreeWordMap S s ++ [a] <+: subtreeWordMap S (s ++ [a]) := by
  change (wordCursor S s).node.letters ++ [a] <+: (wordCursor S (s ++ [a])).node.letters
  rw [wordCursor_snoc]
  exact nextCursor_step S _ _

/-- Every library strong subtree of the full alphabet tree has the literal
strong-map representation used by the manuscript. -/
noncomputable def toWordStrongMap : StrongWordMap α where
  map := subtreeWordMap S
  level := S.levels
  level_strict := S.levels_strictMono
  length_map := subtreeWordMap_length S
  step := subtreeWordMap_step S

/-- No ghost nodes remain in the map representation: it realizes the whole
selected level, with exactly the corresponding source-word length. -/
theorem subtreeWordMap_realizes (n : ℕ) (z : Node α) (hz : z ∈ S.sourceLevel n) :
    ∃ s : List α, s.length = n ∧ subtreeWordMap S s = z.letters := by
  induction n generalizing z with
  | zero =>
      have hzroot : z = S.root := by
        have hp := S.root_below z hz.1
        apply Node.ext
        exact (hp.eq_of_length_le (by
          have hl := S.root_level.trans hz.2.symm
          rw [level_eq_length (α := α) S.root, level_eq_length (α := α) z] at hl
          exact hl.ge)).symm
      exact ⟨[], rfl, by simp [hzroot]⟩
  | succ n ih =>
      obtain ⟨x, hx, hxlevel, hxz⟩ := S.predecessor_exists n z hz.1 hz.2
      obtain ⟨s, hs, hmap⟩ := ih x ⟨hx, hxlevel⟩
      have hlen : x.letters.length < z.letters.length := by
        have h := S.levels_strictMono (Nat.lt_succ_self n)
        rw [← hxlevel, ← hz.2] at h
        rwa [level_eq_length (α := α) x, level_eq_length (α := α) z] at h
      obtain ⟨t, ht⟩ := hxz
      cases t with
      | nil => simp at ht; exact False.elim (Nat.ne_of_lt hlen (congrArg List.length ht))
      | cons a t =>
          refine ⟨s ++ [a], by simp [hs], ?_⟩
          have hxmap : (wordCursor S s).node = x := Node.ext hmap
          have hz' : z ∈ S.sourceLevel ((wordCursor S s).depth + 1) := by
            simpa only [wordCursor_depth, hs] using hz
          have hprefix : (wordCursor S s).node.letters ++ [a] <+: z.letters := by
            rw [hxmap]
            exact ⟨t, by simpa only [List.append_assoc, List.singleton_append] using ht⟩
          have heq := nextCursor_unique S (wordCursor S s) a z hz' hprefix
          change (wordCursor S (s ++ [a])).node.letters = z.letters
          rw [wordCursor_snoc, ← heq]

theorem subtreeWordMap_range :
    Set.range (subtreeWordMap S) = {s | (⟨s⟩ : Node α) ∈ S.carrier} := by
  ext s
  constructor
  · rintro ⟨t, rfl⟩
    exact (subtreeWordMap_onLevel S t).1
  · intro hs
    obtain ⟨n, hn⟩ := S.carrier_levels ⟨s⟩ hs
    obtain ⟨t, _, ht⟩ := subtreeWordMap_realizes S n ⟨s⟩ ⟨hs, hn⟩
    exact ⟨t, ht⟩

end LabelSubtree

/-- Ordinary product HL with actual synchronized, letter-preserving maps,
instead of merely library strong-subtree records. -/
theorem wordStrongMapsHL
    (A : Type) [Finite A] [Nonempty A] [DecidableEq A]
    (I : Type) [Fintype I] (colors : ℕ) [NeZero colors]
    (colour : (I → List A) → Fin colors) :
    ∃ c : Fin colors, ∃ M : ℕ → ℕ, ∃ f : I → StrongWordMap A,
      StrictMono M ∧ (∀ i, (f i).level = M) ∧
      ∀ k (x : I → List A), (∀ i, (x i).length = k) →
        colour (fun i => (f i).map (x i)) = c := by
  obtain ⟨c, M, F, hM, hLevels, hMono⟩ := wordStrongProductHL A I colors colour
  refine ⟨c, M, (fun i => toWordStrongMap (F i)), hM, hLevels, ?_⟩
  intro k x hx
  apply hMono k (fun i => subtreeWordMap (F i) (x i))
  intro i
  simpa only [← hx i] using subtreeWordMap_onLevel (F i) (x i)

/-- The map formulation also uses the original word lengths above prescribed
roots of a common length, exactly as in the manuscript's cone formulation. -/
theorem rootedWordStrongMapsHL
    (A : Type) [Finite A] [Nonempty A] [DecidableEq A]
    (I : Type) [Fintype I] (root : I → List A)
    (r : ℕ) (hroot : ∀ i, (root i).length = r)
    (colors : ℕ) [NeZero colors] (colour : (I → List A) → Fin colors) :
    ∃ c : Fin colors, ∃ M : ℕ → ℕ, ∃ f : I → StrongWordMap A,
      StrictMono M ∧ (∀ i, (f i).level = M) ∧
      (∀ i s, root i <+: (f i).map s) ∧
      ∀ k (x : I → List A), (∀ i, (x i).length = k) →
        colour (fun i => (f i).map (x i)) = c := by
  obtain ⟨c, M, f, hM, hLevels, hMono⟩ := wordStrongMapsHL A I colors
    (fun x => colour (fun i => root i ++ x i))
  refine ⟨c, (fun n => r + M n), (fun i => (f i).prepend (root i)),
    (fun _ _ h => Nat.add_lt_add_left (hM h) r), ?_, ?_, ?_⟩
  · intro i
    funext n
    change (root i).length + (f i).level n = r + M n
    rw [hroot, hLevels]
  · intro i s
    exact List.prefix_append _ _
  · exact hMono

end AllThoseBigRamsey.Pseudotree.WordTrees
