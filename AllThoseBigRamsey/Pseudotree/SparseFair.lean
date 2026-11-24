import AllThoseBigRamsey.Pseudotree.Sparse

/-! Fairness of the sparse queue with control of every intervening letter. -/

namespace AllThoseBigRamsey.Pseudotree.Sparse

/-- Waiting in the queue adds only binary letters. The selected coding node
is therefore in the original binary ray of its queued slot. -/
theorem queued_binary_code (i n : Nat) (hi : i < (stage n).active.length) :
    ∃ b : Word, .one ∉ b ∧ code (n + i) = (stage n).active[i] ++ b := by
  induction i generalizing n with
  | zero =>
    have hn : (stage n).active ≠ [] := by
      intro h
      simp [h] at hi
    obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
    refine ⟨[.zero, .two], by simp, ?_⟩
    simp [ha, code, List.head!, newCode]
  | succ i ih =>
    have hn : (stage n).active ≠ [] := by
      intro h
      simp [h] at hi
    obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
    have hir : i < rest.length := by simpa [ha] using hi
    have hnext : (stage (n + 1)).active = rest.map (pad u) ++ newSlots u := by
      simp [stage, advance, ha]
    have hinext : i < (stage (n + 1)).active.length := by
      simp [hnext, newSlots]
      omega
    have hget : (stage (n + 1)).active[i] = pad u rest[i] := by
      simp [hnext, List.getElem_append_left, hir]
    obtain ⟨b, hb, heq⟩ := ih (n + 1) hinext
    rw [hget] at heq
    refine ⟨List.replicate 3 (if lexLess rest[i] u then .zero else .two) ++ b, ?_, ?_⟩
    · cases lexLess rest[i] u <;> simp_all
    · simpa only [ha, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 i,
        pad, List.append_assoc] using heq

theorem every_active_binary_coded (n : Nat) (w : Word) (hw : w ∈ (stage n).active) :
    ∃ m, n ≤ m ∧ m ≤ 3 * n ∧ ∃ b : Word, .one ∉ b ∧ code m = w ++ b := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hw
  have hlen := (stage_lengths n).1
  refine ⟨n + i, by omega, by omega, ?_⟩
  rw [← heq]
  exact queued_binary_code i n hi

/-- The three children appended at stage `n` are selected at the explicit
stages `3*n+1`, `3*n+2`, and `3*n+3`. -/
theorem child_binary_code (n i : Nat) (hi : i < 3) {u : Word} {rest : List Word}
    (ha : (stage n).active = u :: rest) :
    ∃ b : Word, .one ∉ b ∧
      code (3 * n + 1 + i) = (newSlots u)[i]'(by simpa [newSlots] using hi) ++ b := by
  have hrest : rest.length = 2 * n := by
    have hlen := (stage_lengths n).1
    simp only [ha, List.length_cons] at hlen
    omega
  have hnext : (stage (n + 1)).active = rest.map (pad u) ++ newSlots u := by
    simp [stage, advance, ha]
  have hindex : 2 * n + i < (stage (n + 1)).active.length := by
    simp only [hnext, List.length_append, List.length_map, hrest, newSlots,
      List.length_cons, List.length_nil]
    omega
  obtain ⟨b, hb, heq⟩ := queued_binary_code (2 * n + i) (n + 1) hindex
  refine ⟨b, hb, ?_⟩
  have harith : n + 1 + (2 * n + i) = 3 * n + 1 + i := by omega
  rw [harith] at heq
  simpa [hnext, List.getElem_append_right, hrest] using heq

end AllThoseBigRamsey.Pseudotree.Sparse
