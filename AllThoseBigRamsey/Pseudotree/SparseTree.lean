import AllThoseBigRamsey.Pseudotree.SparseShape
import AllThoseBigRamsey.Pseudotree.SparseMeet

/-! The actual prefix closure of the sparse coding set. -/

namespace AllThoseBigRamsey.Pseudotree.Sparse

def InTree (w : Word) : Prop := ∃ n, w.IsPrefix (code n)

theorem inTree_prefix (hw : InTree w) (hp : p.IsPrefix w) : InTree p := by
  obtain ⟨n, hn⟩ := hw
  exact ⟨n, hp.trans hn⟩

theorem active_inTree (n : Nat) (w : Word) (hw : w ∈ (stage n).active) : InTree w := by
  obtain ⟨m, _, _, hm⟩ := every_active_eventually_coded n w hw
  exact ⟨m, hm⟩

theorem active_next_ancestor (n : Nat) (w : Word) (hw : w ∈ (stage (n + 1)).active) :
    ∃ v ∈ (stage n).active, v.IsPrefix w := by
  have hn : (stage n).active ≠ [] := by
    intro h
    have hl := (stage_lengths n).1
    simp [h] at hl
  obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
  have hw' : w ∈ rest.map (pad u) ++ newSlots u := by simpa [stage, advance, ha] using hw
  rcases List.mem_append.mp hw' with hw' | hw'
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw'
    exact ⟨v, by simp [ha, hv], ⟨_, rfl⟩⟩
  · simp only [newSlots, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl <;> exact ⟨u, by simp [ha], ⟨_, rfl⟩⟩

theorem active_ancestor (n k : Nat) (hnk : n ≤ k) (w : Word) (hw : w ∈ (stage k).active) :
    ∃ v ∈ (stage n).active, v.IsPrefix w := by
  induction k generalizing w with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact ⟨w, hw, List.prefix_rfl⟩
  | succ k ih =>
    by_cases heq : n = k + 1
    · subst n
      exact ⟨w, hw, List.prefix_rfl⟩
    · obtain ⟨u, hu, huw⟩ := active_next_ancestor k w hw
      obtain ⟨v, hv, hvu⟩ := ih (by omega) u hu
      exact ⟨v, hv, hvu.trans huw⟩

theorem active_next_descendant (n : Nat) (v : Word) (hv : v ∈ (stage n).active) :
    ∃ w ∈ (stage (n + 1)).active, v.IsPrefix w := by
  have hn : (stage n).active ≠ [] := by
    intro h
    simp [h] at hv
  obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
  have hnext : (stage (n + 1)).active = rest.map (pad u) ++ newSlots u := by
    simp [stage, advance, ha]
  rcases List.mem_cons.mp (ha ▸ hv) with rfl | hv
  · exact ⟨v ++ [.zero, .zero, .zero], by simp [hnext, newSlots], ⟨_, rfl⟩⟩
  · refine ⟨pad u v, ?_, ⟨_, rfl⟩⟩
    rw [hnext]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩)

theorem old_code_active_descendant (n : Nat) {m : Nat} (hm : m < n) :
    ∃ w ∈ (stage n).active, (code m).IsPrefix w := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : m = n
    · subst m
      have hn : (stage n).active ≠ [] := by
        intro h
        have hl := (stage_lengths n).1
        simp [h] at hl
      obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
      refine ⟨u ++ [.zero, .two, .one], ?_, ?_⟩
      · simp [stage, advance, ha, newSlots]
      · refine ⟨[.one], ?_⟩
        simp [code, ha, List.head!, newCode]
    · obtain ⟨v, hv, hp⟩ := ih (by omega)
      obtain ⟨w, hw, hp'⟩ := active_next_descendant n v hv
      exact ⟨w, hw, hp.trans hp'⟩

/-- At any stage beyond its length, a tree word is exactly a prefix of an
active slot. In particular the finite queue records the entire tree level. -/
theorem inTree_iff_active_prefix (n : Nat) (w : Word) (hlen : w.length ≤ 3 * n) :
    InTree w ↔ ∃ v ∈ (stage n).active, w.IsPrefix v := by
  constructor
  · rintro ⟨m, hm⟩
    by_cases hmn : m < n
    · obtain ⟨v, hv, hp⟩ := old_code_active_descendant n hmn
      exact ⟨v, hv, hm.trans hp⟩
    · have hne : (stage m).active ≠ [] := by
        intro h
        have hl := (stage_lengths m).1
        simp [h] at hl
      obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hne
      have hu : u ∈ (stage m).active := by simp [ha]
      have hup : u.IsPrefix (code m) := by
        refine ⟨[.zero, .two], ?_⟩
        simp [code, ha, List.head!, newCode]
      have hwu : w.IsPrefix u := List.prefix_of_prefix_length_le hm hup
        (by rw [active_length m u hu]; omega)
      obtain ⟨v, hv, hvu⟩ := active_ancestor n m (by omega) u hu
      exact ⟨v, hv, List.prefix_of_prefix_length_le hwu hvu
        (by rw [active_length n v hv]; exact hlen)⟩
  · rintro ⟨v, hv, hp⟩
    exact inTree_prefix (active_inTree n v hv) hp

theorem inTree_stage_level (n : Nat) (w : Word) (hlen : w.length = 3 * n) :
    InTree w ↔ w ∈ (stage n).active := by
  rw [inTree_iff_active_prefix n w (Nat.le_of_eq hlen)]
  constructor
  · rintro ⟨v, hv, hp⟩
    have heq : w = v := hp.eq_of_length (hlen.trans (active_length n v hv).symm)
    exact heq.symm ▸ hv
  · intro hw
    exact ⟨w, hw, List.prefix_rfl⟩

theorem onePrefixes_of_prefix {s t : Word} (hp : s.IsPrefix t) :
    onePrefixes s ⊆ onePrefixes t := by
  obtain ⟨u, rfl⟩ := hp
  rw [onePrefixes_append]
  exact List.subset_append_left _ _

/-- Every upper-cone edge of the infinite tree begins at a coding node. -/
theorem inTree_one_parent {w : Word} (hw : InTree (w ++ [.one])) : InSparse w := by
  obtain ⟨n, hn⟩ := hw
  have hmem : w ∈ onePrefixes (w ++ [.one]) := by simp [onePrefixes_append, onePrefixes]
  obtain ⟨j, _, hj⟩ := code_onePrefixes_earlier n w (onePrefixes_of_prefix hn hmem)
  exact (inSparse_iff_code w).mpr ⟨j, hj⟩

end AllThoseBigRamsey.Pseudotree.Sparse
