import PseudotreeValidation.MixedFusion

/-! Extend a synchronized mixed embedding by one explicitly prescribed level. -/

namespace AllThoseBigRamsey.Pseudotree.Mixed

open RayEmbeddings

/-- Arbitrary prescribed successors satisfying the actual length and ray
conditions extend to total synchronized embeddings. Binary roots are retained
from `F`; no separate conclusion about the new maps is assumed. -/
theorem extend_level {m : ℕ} (F : Embedding m) (r newLevel : ℕ)
    (hnew : F.level r < newLevel)
    (next : Fin (m + 1) → Word → Fin 3 → Word)
    (hlength : ∀ i s a, s.length = r → (next i s a).length = newLevel)
    (hstep : ∀ i s a, s.length = r → ∃ padding : Word,
      next i s a = (F.maps i).map s ++ a :: padding ∧
        (a ≠ 1 → Binary padding)) :
    ∃ G : Embedding m, FixesThrough F G r ∧
      (∀ i s a, s.length = r → (G.maps i).map (s ++ [a]) = next i s a) ∧
      G.level (r + 1) = newLevel ∧
      ∀ n, n ≤ r → G.level n = F.level n := by
  classical
  let levels (n : ℕ) := if n ≤ r then F.level n else newLevel
  let L := extendLevels (r + 2) levels
  have hlevels : ∀ {i j}, i < j → j < r + 2 → levels i < levels j := by
    intro i j hij hj
    by_cases hjr : j ≤ r
    · have hir : i ≤ r := by omega
      simpa only [levels, hir, hjr, ↓reduceIte] using F.level_strict hij
    · have hir : i ≤ r := by omega
      have hle : F.level i ≤ F.level r := F.level_strict.monotone hir
      simp only [levels, hir, hjr, ↓reduceIte]
      omega
  let e (i : Fin (m + 1)) (s : Word) :=
    if s.length ≤ r then (F.maps i).map s else next i s.dropLast s.getLast!
  have e_old (i : Fin (m + 1)) (s : Word) (hs : s.length ≤ r) :
      e i s = (F.maps i).map s := by simp [e, hs]
  have e_next (i : Fin (m + 1)) (s : Word) (a : Fin 3) (hs : s.length = r) :
      e i (s ++ [a]) = next i s a := by simp [e, hs]
  let P (s : Word) := s.length < r + 2
  let p (i : Fin (m + 1)) : PrefixRayMap P := {
    root_mem := by simp [P]
    prefix_closed := by
      intro s t h
      dsimp [P] at *
      simp only [List.length_append] at h
      omega
    map := e i
    level := L
    level_strict := extendLevels_strict (by omega) levels hlevels
    length_map := by
      intro s hs
      have hs' : s.length < r + 2 := hs
      change (e i s).length = extendLevels (r + 2) levels s.length
      rw [extendLevels_agrees levels hs']
      by_cases hsr : s.length ≤ r
      · rw [e_old i s hsr, F.length_map]
        simp [levels, hsr]
      · have hdr : s.dropLast.length = r := by simp only [List.length_dropLast]; omega
        simp only [e, hsr, ↓reduceIte, levels]
        exact hlength i s.dropLast s.getLast! hdr
    step := by
      intro s a hs
      have hs' : (s ++ [a]).length < r + 2 := hs
      have hsr : s.length ≤ r := by simp only [List.length_append, List.length_singleton] at hs'; omega
      by_cases hlt : s.length < r
      · obtain ⟨padding, hp, hbin⟩ := (F.maps i).step s a
        refine ⟨padding, ?_, hbin⟩
        rw [e_old i s hsr, e_old i (s ++ [a]) (by simp only [List.length_append, List.length_singleton]; omega)]
        exact hp
      · have heq : s.length = r := by omega
        obtain ⟨padding, hp, hbin⟩ := hstep i s a heq
        refine ⟨padding, ?_, hbin⟩
        rw [e_next i s a heq, e_old i s hsr]
        exact hp }
  let G : Embedding m := {
    maps i := (p i).completion
    level := L
    synchronized _ := rfl
    binary_roots := by
      intro i hi
      rw [(p i).completion_agrees [] (by simp [P])]
      change Binary (e i [])
      rw [e_old i [] (by simp)]
      exact F.binary_roots i hi }
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro i s hs
    change (p i).completion.map s = (F.maps i).map s
    rw [(p i).completion_agrees s (by dsimp [P]; omega)]
    exact e_old i s hs
  · intro i s a hs
    change (p i).completion.map (s ++ [a]) = next i s a
    rw [(p i).completion_agrees (s ++ [a]) (by simp [P, hs])]
    exact e_next i s a hs
  · change extendLevels (r + 2) levels (r + 1) = newLevel
    rw [extendLevels_agrees levels (by omega)]
    simp [levels]
  · intro n hn
    change extendLevels (r + 2) levels n = F.level n
    rw [extendLevels_agrees levels (by omega)]
    simp [levels, hn]

end AllThoseBigRamsey.Pseudotree.Mixed
