import AllThoseBigRamsey.Pseudotree.RayEmbeddings

/-!
# Completion of ray-preserving maps on prefix-closed domains

The partial data consist only of the actual local edge and level
conditions. The completion is defined explicitly: retain prescribed
values, and fill each unprescribed edge with zeros to reach its scheduled
level. A finite strictly increasing level schedule is extended linearly.
-/

namespace AllThoseBigRamsey.Pseudotree.RayEmbeddings

/-- Local strong-map data on a rooted prefix-closed domain. Values of `map`
outside the domain are irrelevant; no completion is assumed as a field. -/
structure PrefixRayMap (F : Word → Prop) where
  root_mem : F []
  prefix_closed : ∀ s t, F (s ++ t) → F s
  map : Word → Word
  level : Nat → Nat
  level_strict : ∀ {i j}, i < j → level i < level j
  length_map : ∀ s, F s → (map s).length = level s.length
  step : ∀ s a, F (s ++ [a]) → ∃ padding : Word,
    map (s ++ [a]) = map s ++ a :: padding ∧ (a ≠ 1 → Binary padding)

namespace PrefixRayMap

variable {F : Word → Prop}

noncomputable def completeValue (e : PrefixRayMap F) (s : Word) : Word := by
  classical
  exact if F s then e.map s else
    if hn : s = [] then e.map [] else
      completeValue e s.dropLast ++ s.getLast hn ::
        List.replicate (e.level s.length - e.level s.dropLast.length - 1) 0
termination_by s.length
decreasing_by
  have hs : 0 < s.length := List.length_pos_iff.mpr hn
  simp only [List.length_dropLast]
  omega

@[simp] theorem completeValue_of_mem (e : PrefixRayMap F) (s : Word) (hs : F s) :
    e.completeValue s = e.map s := by
  rw [completeValue]
  simp only [hs, ↓reduceIte]

theorem completeValue_append_of_not_mem (e : PrefixRayMap F) (s : Word) (a : Fin 3)
    (hs : ¬ F (s ++ [a])) :
    e.completeValue (s ++ [a]) = e.completeValue s ++ a ::
      List.replicate (e.level (s.length + 1) - e.level s.length - 1) 0 := by
  rw [completeValue]
  simp [hs]

theorem completeValue_length (e : PrefixRayMap F) (s : Word) :
    (e.completeValue s).length = e.level s.length := by
  suffices hh : ∀ t : Word, (e.completeValue t.reverse).length = e.level t.reverse.length by
    simpa only [List.reverse_reverse] using hh s.reverse
  intro t
  induction t with
  | nil =>
      change (e.completeValue []).length = e.level 0
      rw [e.completeValue_of_mem [] e.root_mem]
      exact e.length_map [] e.root_mem
  | cons a t ih =>
      rw [List.reverse_cons]
      by_cases hs : F (t.reverse ++ [a])
      · rw [e.completeValue_of_mem _ hs]
        exact e.length_map _ hs
      · rw [e.completeValue_append_of_not_mem t.reverse a hs]
        simp only [List.length_append, List.length_cons, List.length_replicate,
          List.length_nil, Nat.zero_add, ih]
        have hlt := e.level_strict (Nat.lt_succ_self t.reverse.length)
        simp only [Nat.succ_eq_add_one] at hlt
        omega

/-- Explicit completion by zero padding on all missing edges. -/
noncomputable def completion (e : PrefixRayMap F) : RayStrongMap where
  map := e.completeValue
  level := e.level
  level_strict := e.level_strict
  length_map := e.completeValue_length
  step := by
    intro s a
    by_cases hs : F (s ++ [a])
    · obtain ⟨p, hp, hpb⟩ := e.step s a hs
      have hs' : F s := e.prefix_closed s [a] hs
      exact ⟨p, by simpa only [e.completeValue_of_mem _ hs,
        e.completeValue_of_mem _ hs'] using hp, hpb⟩
    · refine ⟨List.replicate (e.level (s.length + 1) - e.level s.length - 1) 0,
        e.completeValue_append_of_not_mem s a hs, ?_⟩
      intro _ b hb
      have hb' : b = 0 := List.eq_of_mem_replicate hb
      subst b
      decide

@[simp] theorem completion_agrees (e : PrefixRayMap F) (s : Word) (hs : F s) :
    e.completion.map s = e.map s := e.completeValue_of_mem s hs

end PrefixRayMap

/-- Continue a finite level schedule by successive levels after its last
entry. Its values outside the original finite range are not used. -/
def extendLevels (height : Nat) (levels : Nat → Nat) (n : Nat) : Nat :=
  if n < height then levels n else levels (height - 1) + n - (height - 1)

theorem extendLevels_agrees {height : Nat} (levels : Nat → Nat) {n : Nat}
    (hn : n < height) : extendLevels height levels n = levels n := by
  simp [extendLevels, hn]

theorem extendLevels_strict {height : Nat} (hheight : 0 < height) (levels : Nat → Nat)
    (hlevels : ∀ {i j}, i < j → j < height → levels i < levels j) :
    ∀ {i j}, i < j → extendLevels height levels i < extendLevels height levels j := by
  intro i j hij
  by_cases hj : j < height
  · have hi : i < height := Nat.lt_trans hij hj
    simp only [extendLevels, hi, hj, ↓reduceIte]
    exact hlevels hij hj
  · by_cases hi : i < height
    · have hbound : levels i ≤ levels (height - 1) := by
        by_cases hilast : i < height - 1
        · exact Nat.le_of_lt (hlevels hilast (by omega))
        · have heq : i = height - 1 := by omega
          simp [heq]
      simp only [extendLevels, hi, hj, ↓reduceIte]
      omega
    · simp only [extendLevels, hi, hj, ↓reduceIte]
      omega

/-- Every locally ray-preserving strong map on a nonempty prefix-closed
domain of finite height extends to a total ray-preserving strong map. For
the finite ternary alphabet, bounded height is the finite-domain condition.
The prescribed image levels are retained exactly. -/
theorem finite_completion
    (F : Word → Prop) (hF : ∃ s, F s)
    (hprefix : ∀ s t, F (s ++ t) → F s)
    (height : Nat) (hbound : ∀ s, F s → s.length < height)
    (e : Word → Word) (levels : Nat → Nat)
    (hlevels : ∀ {i j}, i < j → j < height → levels i < levels j)
    (hlength : ∀ s, F s → (e s).length = levels s.length)
    (hstep : ∀ s a, F (s ++ [a]) → ∃ padding : Word,
      e (s ++ [a]) = e s ++ a :: padding ∧ (a ≠ 1 → Binary padding)) :
    ∃ f : RayStrongMap,
      (∀ s, F s → f.map s = e s) ∧
      (∀ k, k < height → f.level k = levels k) := by
  obtain ⟨s, hs⟩ := hF
  have hroot : F [] := hprefix [] s (by simpa using hs)
  have hheight : 0 < height := by simpa using hbound [] hroot
  let p : PrefixRayMap F := {
    root_mem := hroot
    prefix_closed := hprefix
    map := e
    level := extendLevels height levels
    level_strict := extendLevels_strict hheight levels hlevels
    length_map := fun s hs => (hlength s hs).trans
      (extendLevels_agrees levels (hbound s hs)).symm
    step := hstep }
  exact ⟨p.completion, p.completion_agrees,
    fun k hk => extendLevels_agrees levels hk⟩

end AllThoseBigRamsey.Pseudotree.RayEmbeddings
