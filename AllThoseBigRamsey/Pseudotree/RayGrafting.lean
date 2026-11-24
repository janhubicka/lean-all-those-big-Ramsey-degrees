import AllThoseBigRamsey.Pseudotree.RayExtension

/-!
# Grafting compatible boundary maps

`BoundaryData.domain u x` says that the value at the tail `x` above boundary
node `u` is prescribed. It may be false everywhere (no prescribed map),
binary words only, or all words. The hypotheses are local edge, level and
incoming-root compatibility conditions; they do not assert an extension.
-/

namespace AllThoseBigRamsey.Pseudotree.RayEmbeddings

def spliceLevels (f₀ : RayStrongMap) (j : Nat) (L : Nat → Nat) (n : Nat) : Nat :=
  if n < j then f₀.level n else L (n - j)

private theorem level_le_of_le (L : Nat → Nat)
    (hL : ∀ {i j}, i < j → L i < L j) {i j : Nat} (hij : i ≤ j) : L i ≤ L j := by
  by_cases h : i < j
  · exact Nat.le_of_lt (hL h)
  · have : i = j := by omega
    simp [this]

theorem spliceLevels_strict (f₀ : RayStrongMap) (j : Nat) (L : Nat → Nat)
    (hL : ∀ {i k}, i < k → L i < L k) (hroot : f₀.level j ≤ L 0) :
    ∀ {i k}, i < k → spliceLevels f₀ j L i < spliceLevels f₀ j L k := by
  intro i k hik
  by_cases hk : k < j
  · have hi : i < j := Nat.lt_trans hik hk
    simp only [spliceLevels, hi, hk, ↓reduceIte]
    exact f₀.level_strict hik
  · by_cases hi : i < j
    · have hbefore := f₀.level_strict hi
      have hafter := level_le_of_le L hL (Nat.zero_le (k - j))
      simp only [spliceLevels, hi, hk, ↓reduceIte]
      omega
    · simp only [spliceLevels, hi, hk, ↓reduceIte]
      exact hL (by omega)

/-- A possibly empty family of partially prescribed boundary maps. Root
padding must be binary on an incoming `0` or `2` edge. Thus arbitrary
ternary roots are permitted only after an incoming `1`, or at depth zero. -/
structure BoundaryData (f₀ : RayStrongMap) (j : Nat) (L : Nat → Nat) where
  domain : Word → Word → Prop
  map : Word → Word → Word
  parent_closed : ∀ u, u.length = j → ∀ x a, domain u (x ++ [a]) → domain u x
  length_map : ∀ u, u.length = j → ∀ x, domain u x → (map u x).length = L x.length
  step : ∀ u, u.length = j → ∀ x a, domain u (x ++ [a]) → ∃ p : Word,
    map u (x ++ [a]) = map u x ++ a :: p ∧ (a ≠ 1 → Binary p)
  root_padding : ∀ s a, (s ++ [a]).length = j → domain (s ++ [a]) [] → ∃ p : Word,
    map (s ++ [a]) [] = f₀.map (s ++ [a]) ++ p ∧ (a ≠ 1 → Binary p)

namespace BoundaryData

variable {f₀ : RayStrongMap} {j : Nat} {L : Nat → Nat}

def combinedDomain (b : BoundaryData f₀ j L) (s : Word) : Prop :=
  s.length < j ∨ b.domain (s.take j) (s.drop j) ∨ s = []

noncomputable def combinedMap (b : BoundaryData f₀ j L) (s : Word) : Word := by
  classical
  exact if s.length < j then f₀.map s else
    if b.domain (s.take j) (s.drop j) then b.map (s.take j) (s.drop j) else
      f₀.map [] ++ List.replicate (L 0 - f₀.level 0) 0

theorem combinedMap_below (b : BoundaryData f₀ j L) (s : Word) (hs : s.length < j) :
    b.combinedMap s = f₀.map s := by simp [combinedMap, hs]

theorem combinedMap_prescribed (b : BoundaryData f₀ j L) (s : Word)
    (hs : j ≤ s.length) (hD : b.domain (s.take j) (s.drop j)) :
    b.combinedMap s = b.map (s.take j) (s.drop j) := by
  simp [combinedMap, Nat.not_lt.mpr hs, hD]

private theorem combinedDomain_parent (b : BoundaryData f₀ j L) (s : Word) (a : Fin 3)
    (h : b.combinedDomain (s ++ [a])) : b.combinedDomain s := by
  by_cases hs : s.length < j
  · exact Or.inl hs
  have hle : j ≤ s.length := Nat.le_of_not_lt hs
  have htake : (s.take j).length = j := List.length_take_of_le hle
  rcases h with h | h | h
  · simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at h
    omega
  · rw [List.take_append_of_le_length hle, List.drop_append_of_le_length hle] at h
    exact Or.inr (Or.inl (b.parent_closed _ htake _ _ h))
  · simp at h

private theorem prefix_closed_of_parent (F : Word → Prop)
    (hparent : ∀ s a, F (s ++ [a]) → F s) (s t : Word) : F (s ++ t) → F s := by
  suffices h : ∀ q : Word, F (s ++ q.reverse) → F s by
    simpa only [List.reverse_reverse] using h t.reverse
  intro q
  induction q with
  | nil => simp
  | cons a q ih =>
      intro h
      apply ih
      apply hparent (s ++ q.reverse) a
      simpa only [List.reverse_cons, List.append_assoc] using h

theorem combinedMap_length (b : BoundaryData f₀ j L) (hroot : f₀.level j ≤ L 0)
    (s : Word) (hs : b.combinedDomain s) :
    (b.combinedMap s).length = spliceLevels f₀ j L s.length := by
  by_cases hlow : s.length < j
  · rw [b.combinedMap_below s hlow]
    simp [spliceLevels, hlow, f₀.length_map]
  have hle : j ≤ s.length := Nat.le_of_not_lt hlow
  by_cases hD : b.domain (s.take j) (s.drop j)
  · rw [b.combinedMap_prescribed s hle hD]
    have h := b.length_map _ (List.length_take_of_le hle) _ hD
    simpa only [List.length_drop, spliceLevels, hlow, ↓reduceIte] using h
  · have hnil : s = [] := hs.resolve_left hlow |>.resolve_left hD
    subst s
    have hj : j = 0 := by simp only [List.length_nil] at hlow; omega
    subst j
    have hD' : ¬ b.domain [] [] := by simpa using hD
    simp only [combinedMap, List.length_nil, Nat.lt_irrefl, ↓reduceIte,
      List.take_nil, List.drop_nil, hD', List.length_append, f₀.length_map,
      List.length_replicate, spliceLevels, Nat.sub_self]
    omega

theorem combinedMap_step (b : BoundaryData f₀ j L) (s : Word) (a : Fin 3)
    (hs : b.combinedDomain (s ++ [a])) : ∃ p : Word,
      b.combinedMap (s ++ [a]) = b.combinedMap s ++ a :: p ∧
      (a ≠ 1 → Binary p) := by
  by_cases hchild : (s ++ [a]).length < j
  · have hparent : s.length < j := by simp only [List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add] at hchild; omega
    simpa only [b.combinedMap_below _ hchild, b.combinedMap_below _ hparent] using f₀.step s a
  have hD : b.domain ((s ++ [a]).take j) ((s ++ [a]).drop j) := by
    rcases hs with h | h | h
    · contradiction
    · exact h
    · simp at h
  have hchildle : j ≤ (s ++ [a]).length := Nat.le_of_not_lt hchild
  rw [b.combinedMap_prescribed _ hchildle hD]
  by_cases hparent : s.length < j
  · have heq : (s ++ [a]).length = j := by
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add] at hchild ⊢
      omega
    have ht : (s ++ [a]).take j = s ++ [a] := by rw [← heq]; exact List.take_length
    have hd : (s ++ [a]).drop j = [] := by rw [← heq]; exact List.drop_length
    rw [ht, hd] at hD ⊢
    rw [b.combinedMap_below _ hparent]
    obtain ⟨p, hp, hpb⟩ := b.root_padding s a heq hD
    obtain ⟨q, hq, hqb⟩ := f₀.step s a
    refine ⟨q ++ p, ?_, ?_⟩
    · rw [hp, hq]
      simp
    · intro ha
      exact (binary_append q p).mpr ⟨hqb ha, hpb ha⟩
  · have hle : j ≤ s.length := Nat.le_of_not_lt hparent
    have ht : (s.take j).length = j := List.length_take_of_le hle
    rw [List.take_append_of_le_length hle, List.drop_append_of_le_length hle] at hD ⊢
    have hDparent := b.parent_closed _ ht _ a hD
    rw [b.combinedMap_prescribed s hle hDparent]
    exact b.step _ ht _ a hD

/-- Complete all unprescribed branches after gluing the compatible local
maps. Below the boundary the original map is retained exactly. -/
noncomputable def graft (b : BoundaryData f₀ j L)
    (hL : ∀ {i k}, i < k → L i < L k) (hroot : f₀.level j ≤ L 0) : RayStrongMap :=
  PrefixRayMap.completion {
    root_mem := Or.inr (Or.inr rfl)
    prefix_closed := prefix_closed_of_parent b.combinedDomain b.combinedDomain_parent
    map := b.combinedMap
    level := spliceLevels f₀ j L
    level_strict := spliceLevels_strict f₀ j L hL hroot
    length_map := b.combinedMap_length hroot
    step := b.combinedMap_step }

theorem graft_below (b : BoundaryData f₀ j L)
    (hL : ∀ {i k}, i < k → L i < L k) (hroot : f₀.level j ≤ L 0)
    (s : Word) (hs : s.length < j) : (b.graft hL hroot).map s = f₀.map s := by
  change (PrefixRayMap.completion _).map s = _
  rw [PrefixRayMap.completion_agrees _ s (Or.inl hs)]
  exact b.combinedMap_below s hs

theorem graft_prescribed (b : BoundaryData f₀ j L)
    (hL : ∀ {i k}, i < k → L i < L k) (hroot : f₀.level j ≤ L 0)
    (u x : Word) (hu : u.length = j) (hx : b.domain u x) :
    (b.graft hL hroot).map (u ++ x) = b.map u x := by
  have ht : (u ++ x).take j = u := List.take_left' hu
  have hd : (u ++ x).drop j = x := List.drop_left' hu
  have hD : b.domain ((u ++ x).take j) ((u ++ x).drop j) := by simpa only [ht, hd] using hx
  change (PrefixRayMap.completion _).map (u ++ x) = _
  rw [PrefixRayMap.completion_agrees _ (u ++ x) (Or.inr (Or.inl hD))]
  change b.combinedMap (u ++ x) = b.map u x
  rw [b.combinedMap_prescribed _ (by simp [hu]) hD, ht, hd]

@[simp] theorem graft_levels (b : BoundaryData f₀ j L)
    (hL : ∀ {i k}, i < k → L i < L k) (hroot : f₀.level j ≤ L 0) :
    (b.graft hL hroot).level = spliceLevels f₀ j L := rfl

end BoundaryData

/-- The boundary grafting theorem with the manuscript's binary/full
domains and its restriction on incoming `1` edges made explicit.
Only prescribed nodes need supply local maps. A map specified solely
through level `j` may first be completed using `finite_completion`.
-/
theorem graft_binary_ternary
    (f₀ : RayStrongMap) (j : Nat) (L : Nat → Nat)
    (hL : ∀ {i k}, i < k → L i < L k) (hroot : f₀.level j ≤ L 0)
    (prescribed ternary : Word → Prop) (H : Word → Word → Word)
    (hallowed : ∀ u, u.length = j → prescribed u → ternary u →
      u = [] ∨ ∃ s, u = s ++ [1])
    (hlength : ∀ u, u.length = j → prescribed u → ∀ x,
      ternary u ∨ Binary x → (H u x).length = L x.length)
    (hstep : ∀ u, u.length = j → prescribed u → ∀ x a,
      ternary u ∨ Binary (x ++ [a]) → ∃ p : Word,
        H u (x ++ [a]) = H u x ++ a :: p ∧ (a ≠ 1 → Binary p))
    (hpadding : ∀ u, u.length = j → prescribed u → ∃ p : Word,
      H u [] = f₀.map u ++ p ∧ (¬ ternary u → Binary p)) :
    ∃ f : RayStrongMap,
      (∀ s, s.length < j → f.map s = f₀.map s) ∧
      (∀ u, u.length = j → prescribed u → ∀ x,
        ternary u ∨ Binary x → f.map (u ++ x) = H u x) ∧
      f.level = spliceLevels f₀ j L := by
  classical
  let b : BoundaryData f₀ j L := {
    domain := fun u x => prescribed u ∧ (ternary u ∨ Binary x)
    map := H
    parent_closed := by
      intro u hu x a hx
      refine ⟨hx.1, ?_⟩
      rcases hx.2 with ht | hb
      · exact Or.inl ht
      · exact Or.inr ((binary_append x [a]).mp hb).1
    length_map := by
      intro u hu x hx
      exact hlength u hu hx.1 x hx.2
    step := by
      intro u hu x a hx
      exact hstep u hu hx.1 x a hx.2
    root_padding := by
      intro s a hlen hD
      obtain ⟨p, hp, hpb⟩ := hpadding (s ++ [a]) hlen hD.1
      refine ⟨p, hp, ?_⟩
      intro ha
      apply hpb
      intro hternary
      rcases hallowed (s ++ [a]) hlen hD.1 hternary with hnil | ⟨t, ht⟩
      · simp at hnil
      · have hlast := congrArg List.getLast? ht
        have ha' : a = 1 := by simpa using hlast
        exact ha ha' }
  refine ⟨b.graft hL hroot, b.graft_below hL hroot, ?_, b.graft_levels hL hroot⟩
  intro u hu hp x hx
  exact b.graft_prescribed hL hroot u x hu ⟨hp, hx⟩

/-- The finite-prefix version: the initial map and level schedule are
required only through level `j`, exactly as in the manuscript. -/
theorem finite_boundary_grafting
    (j : Nat) (e : Word → Word) (levels L : Nat → Nat)
    (hlevels : ∀ {i k}, i < k → k ≤ j → levels i < levels k)
    (heLength : ∀ s, s.length ≤ j → (e s).length = levels s.length)
    (heStep : ∀ s a, (s ++ [a]).length ≤ j → ∃ p : Word,
      e (s ++ [a]) = e s ++ a :: p ∧ (a ≠ 1 → Binary p))
    (hL : ∀ {i k}, i < k → L i < L k) (hroot : levels j ≤ L 0)
    (prescribed ternary : Word → Prop) (H : Word → Word → Word)
    (hallowed : ∀ u, u.length = j → prescribed u → ternary u →
      u = [] ∨ ∃ s, u = s ++ [1])
    (hLength : ∀ u, u.length = j → prescribed u → ∀ x,
      ternary u ∨ Binary x → (H u x).length = L x.length)
    (hStep : ∀ u, u.length = j → prescribed u → ∀ x a,
      ternary u ∨ Binary (x ++ [a]) → ∃ p : Word,
        H u (x ++ [a]) = H u x ++ a :: p ∧ (a ≠ 1 → Binary p))
    (hpadding : ∀ u, u.length = j → prescribed u → ∃ p : Word,
      H u [] = e u ++ p ∧ (¬ ternary u → Binary p)) :
    ∃ f : RayStrongMap,
      (∀ s, s.length < j → f.map s = e s) ∧
      (∀ u, u.length = j → prescribed u → ∀ x,
        ternary u ∨ Binary x → f.map (u ++ x) = H u x) ∧
      (∀ n, f.level n = if n < j then levels n else L (n - j)) := by
  obtain ⟨f₀, hf₀, hl₀⟩ := finite_completion
    (fun s => s.length ≤ j) ⟨[], by simp⟩
    (by intro s t h; simp only [List.length_append] at h; omega)
    (j + 1) (by intro s hs; omega) e levels
    (by intro i k hik hk; exact hlevels hik (by omega)) heLength heStep
  have hroot' : f₀.level j ≤ L 0 := by
    rw [hl₀ j (by omega)]
    exact hroot
  have hpadding' : ∀ u, u.length = j → prescribed u → ∃ p : Word,
      H u [] = f₀.map u ++ p ∧ (¬ ternary u → Binary p) := by
    intro u hu hp
    obtain ⟨p, heq, hbin⟩ := hpadding u hu hp
    refine ⟨p, ?_, hbin⟩
    rw [hf₀ u (Nat.le_of_eq hu)]
    exact heq
  obtain ⟨f, hbelow, hprescribed, hlevel⟩ :=
    graft_binary_ternary f₀ j L hL hroot' prescribed ternary H
      hallowed hLength hStep hpadding'
  refine ⟨f, ?_, hprescribed, ?_⟩
  · intro s hs
    exact (hbelow s hs).trans (hf₀ s (Nat.le_of_lt hs))
  · intro n
    rw [hlevel]
    by_cases hn : n < j
    · simp only [spliceLevels, hn, ↓reduceIte]
      exact hl₀ n (by omega)
    · simp only [spliceLevels, hn, ↓reduceIte]

end AllThoseBigRamsey.Pseudotree.RayEmbeddings
