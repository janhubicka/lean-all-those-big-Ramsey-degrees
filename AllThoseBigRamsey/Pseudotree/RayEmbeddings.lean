import Std

/-!
# Ray-preserving strong maps of the ternary word tree

These definitions are the literal local conditions in the note: every
edge keeps its first letter; padding after 0 and 2 contains no 1. We check
preservation of arbitrary binary extensions and closure under composition.
The Ramsey/fusion existence theorem is not assumed here.
-/

namespace AllThoseBigRamsey.Pseudotree.RayEmbeddings

abbrev Word := List (Fin 3)

def Binary (w : Word) : Prop := ∀ a ∈ w, a ≠ 1

@[simp] theorem binary_nil : Binary [] := by simp [Binary]

@[simp] theorem binary_cons (a : Fin 3) (w : Word) :
    Binary (a :: w) ↔ a ≠ 1 ∧ Binary w := by simp [Binary]

@[simp] theorem binary_append (u v : Word) :
    Binary (u ++ v) ↔ Binary u ∧ Binary v := by
  simp only [Binary, List.mem_append, or_imp, forall_and]

/-- The level/edge definition of a ray-preserving strong embedding. -/
structure RayStrongMap where
  map : Word → Word
  level : Nat → Nat
  level_strict : ∀ {i j}, i < j → level i < level j
  length_map : ∀ s, (map s).length = level s.length
  step : ∀ s a, ∃ padding : Word,
    map (s ++ [a]) = map s ++ a :: padding ∧
      (a ≠ 1 → Binary padding)

namespace RayStrongMap

/-- A strong map sends arbitrary extensions to extensions. On binary
extensions, its entire added word stays binary. -/
theorem map_append (f : RayStrongMap) (s t : Word) :
    ∃ padding : Word,
      f.map (s ++ t) = f.map s ++ padding ∧
      (Binary t → Binary padding) := by
  induction t generalizing s with
  | nil => exact ⟨[], by simp, fun _ => binary_nil⟩
  | cons a t ih =>
      obtain ⟨p, hp, hpb⟩ := f.step s a
      obtain ⟨q, hq, hqb⟩ := ih (s ++ [a])
      refine ⟨a :: (p ++ q), ?_, ?_⟩
      · calc
          f.map (s ++ a :: t) = f.map ((s ++ [a]) ++ t) := by simp
          _ = f.map (s ++ [a]) ++ q := hq
          _ = f.map s ++ a :: (p ++ q) := by rw [hp]; simp
      · intro ht
        obtain ⟨ha, ht⟩ := binary_cons a t |>.mp ht
        exact (binary_cons a (p ++ q)).mpr
          ⟨ha, (binary_append p q).mpr ⟨hpb ha, hqb ht⟩⟩

/-- In particular every binary ray above an arbitrary word maps into
the binary ray above its image, as required in the fusion invariant. -/
theorem maps_binary_ray (f : RayStrongMap) (s t : Word) (ht : Binary t) :
    ∃ padding : Word, Binary padding ∧
      f.map (s ++ t) = f.map s ++ padding := by
  obtain ⟨p, hp, hpb⟩ := f.map_append s t
  exact ⟨p, hpb ht, hp⟩

/-- The first letter of an extension is retained at the image edge. -/
theorem map_append_cons (f : RayStrongMap) (s : Word) (a : Fin 3) (t : Word) :
    ∃ padding : Word, f.map (s ++ a :: t) = f.map s ++ a :: padding := by
  obtain ⟨p, hp, _⟩ := f.step s a
  obtain ⟨q, hq, _⟩ := f.map_append (s ++ [a]) t
  refine ⟨p ++ q, ?_⟩
  calc
    f.map (s ++ a :: t) = f.map ((s ++ [a]) ++ t) := by simp
    _ = f.map (s ++ [a]) ++ q := hq
    _ = f.map s ++ a :: (p ++ q) := by rw [hp]; simp

private theorem injective_at_level (f : RayStrongMap) (n : Nat) :
    ∀ s t u : Word, s.length = n → t.length = n →
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
          have hst : s = t := ih s t (u ++ [a])
            (by simpa using hs) (by simpa using ht) (by simpa using h)
          simp [hst]

/-- Thus the local edge and level conditions really give an injective map;
injectivity does not need to be added as a redundant structure field. -/
theorem injective (f : RayStrongMap) : Function.Injective f.map := by
  intro s t h
  have hlen : f.level s.length = f.level t.length := by
    simpa only [f.length_map] using congrArg List.length h
  have heqlen : s.length = t.length := by
    by_cases hlt : s.length < t.length
    · have hstrict := f.level_strict hlt
      omega
    by_cases hgt : t.length < s.length
    · have hstrict := f.level_strict hgt
      omega
    omega
  exact f.injective_at_level s.length s t [] rfl heqlen.symm (by simpa using h)

/-- The identity has no inserted padding. -/
def identity : RayStrongMap where
  map := id
  level := id
  level_strict := fun h => h
  length_map := fun _ => rfl
  step := by
    intro s a
    exact ⟨[], rfl, fun _ => binary_nil⟩

/-- Composition preserves both the level map and the no-1 condition. -/
def comp (f g : RayStrongMap) : RayStrongMap where
  map := f.map ∘ g.map
  level := f.level ∘ g.level
  level_strict := fun h => f.level_strict (g.level_strict h)
  length_map := by
    intro s
    change (f.map (g.map s)).length = f.level (g.level s.length)
    rw [f.length_map, g.length_map]
  step := by
    intro s a
    obtain ⟨p, hp, hpb⟩ := g.step s a
    obtain ⟨q, hq, hqb⟩ := f.step (g.map s) a
    obtain ⟨r, hr, hrb⟩ := f.map_append (g.map s ++ [a]) p
    refine ⟨q ++ r, ?_, ?_⟩
    · change f.map (g.map (s ++ [a])) = f.map (g.map s) ++ a :: (q ++ r)
      rw [hp]
      calc
        f.map (g.map s ++ a :: p) = f.map ((g.map s ++ [a]) ++ p) := by simp
        _ = f.map (g.map s ++ [a]) ++ r := hr
        _ = f.map (g.map s) ++ a :: (q ++ r) := by rw [hq]; simp
    · intro ha
      exact (binary_append q r).mpr ⟨hqb ha, hrb (hpb ha)⟩

@[simp] theorem comp_map (f g : RayStrongMap) (s : Word) :
    (f.comp g).map s = f.map (g.map s) := rfl

/-- Later approximations agree with stage i on all words through level i. -/
def Coherent (F : Nat → RayStrongMap) : Prop :=
  ∀ i j, i ≤ j → ∀ s : Word, s.length ≤ i → (F j).map s = (F i).map s

/-- Coherence of maps also forces coherence of their level functions.
It suffices to test one word at each level. -/
theorem coherent_levels (F : Nat → RayStrongMap) (hF : Coherent F)
    {i j n : Nat} (hij : i ≤ j) (hni : n ≤ i) :
    (F j).level n = (F i).level n := by
  have h := hF i j hij (List.replicate n (0 : Fin 3)) (by simpa using hni)
  simpa only [length_map, List.length_replicate] using congrArg List.length h

/-- A coherent pointwise limit is still a ray-preserving strong map. -/
def limit (F : Nat → RayStrongMap) (hF : Coherent F) : RayStrongMap where
  map := fun s => (F s.length).map s
  level := fun n => (F n).level n
  level_strict := by
    intro i j hij
    have h := (F j).level_strict hij
    rw [coherent_levels F hF (Nat.le_of_lt hij) (Nat.le_refl i)] at h
    exact h
  length_map := fun s => (F s.length).length_map s
  step := by
    intro s a
    obtain ⟨p, hp, hpb⟩ := (F (s.length + 1)).step s a
    refine ⟨p, ?_, hpb⟩
    have hs : (F (s.length + 1)).map s = (F s.length).map s :=
      hF s.length (s.length + 1) (Nat.le_succ _) s (Nat.le_refl _)
    simpa only [List.length_append, List.length_cons, List.length_nil,
      Nat.zero_add, hs] using hp

/-- The limit agrees with each sufficiently late approximation. -/
theorem limit_agrees (F : Nat → RayStrongMap) (hF : Coherent F)
    (k : Nat) (s : Word) (hs : s.length ≤ k) :
    (limit F hF).map s = (F k).map s :=
  (hF s.length k hs s (Nat.le_refl _)).symm

/-- The right-composition convention used in the manuscript's fusion. -/
def compositions (g : Nat → RayStrongMap) : Nat → RayStrongMap
  | 0 => g 0
  | j + 1 => (compositions g j).comp (g (j + 1))

/-- Fixing the first j+1 levels at stage j+1 makes the right-composition
sequence coherent. This is the preservation invariant used by fusion. -/
theorem compositions_coherent (g : Nat → RayStrongMap)
    (hfix : ∀ j (s : Word), s.length ≤ j → (g (j + 1)).map s = s) :
    Coherent (compositions g) := by
  intro i j hij s hsi
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      rfl
  | succ j ih =>
      by_cases hi : i = j + 1
      · subst i
        rfl
      · have hij' : i ≤ j := by omega
        change (compositions g j).map ((g (j + 1)).map s) =
          (compositions g i).map s
        rw [hfix j s (Nat.le_trans hsi hij')]
        exact ih hij'

/-- The usual fusion sequence therefore has a ray-preserving strong
limit, with no added fusion axiom. -/
def fusion (g : Nat → RayStrongMap)
    (hfix : ∀ j (s : Word), s.length ≤ j → (g (j + 1)).map s = s) :
    RayStrongMap :=
  limit (compositions g) (compositions_coherent g hfix)

theorem fusion_agrees (g : Nat → RayStrongMap)
    (hfix : ∀ j (s : Word), s.length ≤ j → (g (j + 1)).map s = s)
    (k : Nat) (s : Word) (hs : s.length ≤ k) :
    (fusion g hfix).map s = (compositions g k).map s :=
  limit_agrees _ _ k s hs

/-- The unconsumed tail after stage j still satisfies the fusion rule. -/
theorem tail_fixes (g : Nat → RayStrongMap)
    (hfix : ∀ j (s : Word), s.length ≤ j → (g (j + 1)).map s = s)
    (j k : Nat) (s : Word) (hs : s.length ≤ k) :
    (g (j + (k + 1) + 1)).map s = s := by
  apply hfix (j + (k + 1)) s
  omega

/-- Factor a finite right-composition sequence at any earlier stage. -/
theorem compositions_split (g : Nat → RayStrongMap) (j k : Nat) (s : Word) :
    (compositions g (j + k + 1)).map s =
      (compositions g j).map
        ((compositions (fun n => g (j + n + 1)) k).map s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
      calc
        (compositions g (j + (k + 1) + 1)).map s =
            (compositions g (j + k + 1)).map ((g (j + k + 2)).map s) := by
              rw [show j + (k + 1) + 1 = (j + k + 1) + 1 by omega]
              rfl
        _ = (compositions g j).map
            ((compositions (fun n => g (j + n + 1)) k).map
              ((g (j + k + 2)).map s)) := ih _
        _ = (compositions g j).map
            ((compositions (fun n => g (j + n + 1)) (k + 1)).map s) := by
              simp only [compositions, comp_map, Nat.add_assoc]

/-- Every stage of the remaining tail fixes the already protected levels. -/
theorem tail_compositions_fix (g : Nat → RayStrongMap)
    (hfix : ∀ j (s : Word), s.length ≤ j → (g (j + 1)).map s = s)
    (j k : Nat) (s : Word) (hs : s.length ≤ j) :
    (compositions (fun n => g (j + n + 1)) k).map s = s := by
  induction k with
  | zero => exact hfix j s hs
  | succ k ih =>
      change (compositions (fun n => g (j + n + 1)) k).map
        ((g (j + (k + 1) + 1)).map s) = s
      rw [hfix (j + (k + 1)) s (by omega)]
      exact ih

/-- The pointwise limit factors through every finite fusion stage by
another ray-preserving strong map fixing the protected initial levels. -/
theorem fusion_factors (g : Nat → RayStrongMap)
    (hfix : ∀ j (s : Word), s.length ≤ j → (g (j + 1)).map s = s)
    (j : Nat) :
    ∃ h : RayStrongMap,
      (∀ s : Word, s.length ≤ j → h.map s = s) ∧
      ∀ s : Word, (fusion g hfix).map s = (compositions g j).map (h.map s) := by
  let tail : Nat → RayStrongMap := fun n => g (j + n + 1)
  have htail : ∀ k (s : Word), s.length ≤ k → (tail (k + 1)).map s = s :=
    tail_fixes g hfix j
  let h : RayStrongMap := fusion tail htail
  refine ⟨h, ?_, ?_⟩
  · intro s hs
    change (compositions tail s.length).map s = s
    exact tail_compositions_fix g hfix j s.length s hs
  · intro s
    have hs : s.length ≤ j + s.length + 1 := by omega
    rw [fusion_agrees g hfix (j + s.length + 1) s hs]
    exact compositions_split g j s.length s

end RayStrongMap
end AllThoseBigRamsey.Pseudotree.RayEmbeddings
