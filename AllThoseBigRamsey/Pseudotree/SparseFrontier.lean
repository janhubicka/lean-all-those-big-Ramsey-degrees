import AllThoseBigRamsey.Pseudotree.SparseTree

/-! Exact critical-node child rules of the actual sparse prefix tree. -/

namespace AllThoseBigRamsey.Pseudotree.Sparse

private theorem rank_injective : Function.Injective rank := by
  intro a b h
  cases a <;> cases b <;> simp_all [rank]

theorem lexLess_common_prefix (p s t : Word) : lexLess (p ++ s) (p ++ t) = lexLess s t := by
  induction p with
  | nil => rfl
  | cons a p ih => simpa only [List.cons_append, lexLess, ↓reduceIte] using ih

/-- Appending tails to different words of the same length cannot change
which word is lexicographically first. -/
theorem lexLess_append_of_ne {s t : Word} (hlen : s.length = t.length) (hne : s ≠ t)
    (a b : Word) : lexLess (s ++ a) (t ++ b) = lexLess s t := by
  induction s generalizing t with
  | nil => cases t <;> simp_all
  | cons c s ih =>
    cases t with
    | nil => simp at hlen
    | cons d t =>
      by_cases hcd : c = d
      · subst d
        have hst : s ≠ t := by intro h; exact hne (h ▸ rfl)
        simpa only [List.cons_append, lexLess, ↓reduceIte] using
          ih (by simpa using hlen) hst
      · have hrank : rank c ≠ rank d := fun h => hcd (rank_injective h)
        simp only [List.cons_append, lexLess, hrank, ↓reduceIte]

def direction (u v : Word) : TernaryLetter := if lexLess v u then .zero else .two

theorem active_head_exists (n : Nat) :
    ∃ u rest, (stage n).active = u :: rest ∧ u.length = 3 * n ∧ u ∉ rest := by
  have hn : (stage n).active ≠ [] := by
    intro h
    have hl := (stage_lengths n).1
    simp [h] at hl
  obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
  exact ⟨u, rest, ha, active_length n u (by simp [ha]),
    (List.nodup_cons.mp (ha ▸ active_nodup n)).1⟩

/-- Within one three-letter stage, the entire prefix tree is determined by
three new slots and the unique padded continuation of every old slot. -/
theorem inTree_slot_tail (n : Nat) (u : Word) (rest : List Word)
    (ha : (stage n).active = u :: rest) (v t : Word)
    (hvlen : v.length = 3 * n) (htlen : t.length ≤ 3) :
    InTree (v ++ t) ↔
      (v = u ∧ (t.IsPrefix [.zero, .zero, .zero] ∨
        t.IsPrefix [.zero, .two, .one] ∨ t.IsPrefix [.two, .two, .two])) ∨
      (v ∈ rest ∧ t.IsPrefix (List.replicate 3 (direction u v))) := by
  have hulen : u.length = 3 * n := active_length n u (by simp [ha])
  rw [inTree_iff_active_prefix (n + 1) (v ++ t) (by simp only [List.length_append]; omega)]
  have hnext : (stage (n + 1)).active = rest.map (pad u) ++ newSlots u := by
    simp [stage, advance, ha]
  constructor
  · rintro ⟨z, hz, hp⟩
    rw [hnext] at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
      have hwlen : w.length = 3 * n := active_length n w (by simp [ha, hw])
      have heq := (List.prefix_append_inj_of_length_eq (hvlen.trans hwlen.symm)).mp hp
      obtain ⟨rfl, hp⟩ := heq
      exact Or.inr ⟨hw, hp⟩
    · simp only [newSlots, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · have heq := (List.prefix_append_inj_of_length_eq (hvlen.trans hulen.symm)).mp hp
        exact Or.inl ⟨heq.1, Or.inl heq.2⟩
      · have heq := (List.prefix_append_inj_of_length_eq (hvlen.trans hulen.symm)).mp hp
        exact Or.inl ⟨heq.1, Or.inr (Or.inl heq.2)⟩
      · have heq := (List.prefix_append_inj_of_length_eq (hvlen.trans hulen.symm)).mp hp
        exact Or.inl ⟨heq.1, Or.inr (Or.inr heq.2)⟩
  · rintro (⟨rfl, hp | hp | hp⟩ | ⟨hv, hp⟩)
    · exact ⟨v ++ [.zero, .zero, .zero], by simp [hnext, newSlots], (List.prefix_append_right_inj v).mpr hp⟩
    · exact ⟨v ++ [.zero, .two, .one], by simp [hnext, newSlots], (List.prefix_append_right_inj v).mpr hp⟩
    · exact ⟨v ++ [.two, .two, .two], by simp [hnext, newSlots], (List.prefix_append_right_inj v).mpr hp⟩
    · exact ⟨pad u v, by rw [hnext]; exact List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩),
        (List.prefix_append_right_inj v).mpr hp⟩

theorem inTree_phase1 (n : Nat) (u : Word) (rest : List Word)
    (ha : (stage n).active = u :: rest) (w : Word) (hwlen : w.length = 3 * n + 1) :
    InTree w ↔ w = u ++ [.zero] ∨ w = u ++ [.two] ∨
      ∃ v ∈ rest, w = v ++ [direction u v] := by
  have hulen : u.length = 3 * n := active_length n u (by simp [ha])
  rw [inTree_iff_active_prefix (n + 1) w (by omega)]
  have hnext : (stage (n + 1)).active = rest.map (pad u) ++ newSlots u := by
    simp [stage, advance, ha]
  constructor
  · rintro ⟨z, hz, hp⟩
    have htake := List.prefix_iff_eq_take.mp hp
    rw [hwlen] at htake
    rw [hnext] at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
      have hvlen := active_length n v (by simp [ha, hv])
      refine Or.inr (Or.inr ⟨v, hv, ?_⟩)
      simpa [pad, ← hvlen, List.take_append, List.take_of_length_le (Nat.le_add_right _ _), direction] using htake
    · simp only [newSlots, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inl (by simpa [← hulen, List.take_append, List.take_of_length_le (Nat.le_add_right _ _)] using htake)
      · exact Or.inl (by simpa [← hulen, List.take_append, List.take_of_length_le (Nat.le_add_right _ _)] using htake)
      · exact Or.inr (Or.inl (by simpa [← hulen, List.take_append, List.take_of_length_le (Nat.le_add_right _ _)] using htake))
  · rintro (rfl | rfl | ⟨v, hv, rfl⟩)
    · exact ⟨u ++ [.zero, .zero, .zero], by simp [hnext, newSlots], by simp⟩
    · exact ⟨u ++ [.two, .two, .two], by simp [hnext, newSlots], by simp⟩
    · refine ⟨pad u v, ?_, ?_⟩
      · rw [hnext]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
      · simp [pad, direction, List.replicate_succ]

theorem inTree_phase2 (n : Nat) (u : Word) (rest : List Word)
    (ha : (stage n).active = u :: rest) (w : Word) (hwlen : w.length = 3 * n + 2) :
    InTree w ↔ w = u ++ [.zero, .zero] ∨ w = u ++ [.zero, .two] ∨
      w = u ++ [.two, .two] ∨ ∃ v ∈ rest, w = v ++ [direction u v, direction u v] := by
  have hulen : u.length = 3 * n := active_length n u (by simp [ha])
  rw [inTree_iff_active_prefix (n + 1) w (by omega)]
  have hnext : (stage (n + 1)).active = rest.map (pad u) ++ newSlots u := by
    simp [stage, advance, ha]
  constructor
  · rintro ⟨z, hz, hp⟩
    have htake := List.prefix_iff_eq_take.mp hp
    rw [hwlen] at htake
    rw [hnext] at hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
      have hvlen := active_length n v (by simp [ha, hv])
      refine Or.inr (Or.inr (Or.inr ⟨v, hv, ?_⟩))
      simpa [pad, ← hvlen, List.take_append, List.take_of_length_le (Nat.le_add_right _ _), direction] using htake
    · simp only [newSlots, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inl (by simpa [← hulen, List.take_append, List.take_of_length_le (Nat.le_add_right _ _)] using htake)
      · exact Or.inr (Or.inl (by simpa [← hulen, List.take_append, List.take_of_length_le (Nat.le_add_right _ _)] using htake))
      · exact Or.inr (Or.inr (Or.inl (by simpa [← hulen, List.take_append, List.take_of_length_le (Nat.le_add_right _ _)] using htake)))
  · rintro (rfl | rfl | rfl | ⟨v, hv, rfl⟩)
    · exact ⟨u ++ [.zero, .zero, .zero], by simp [hnext, newSlots], by simp⟩
    · exact ⟨u ++ [.zero, .two, .one], by simp [hnext, newSlots], by simp⟩
    · exact ⟨u ++ [.two, .two, .two], by simp [hnext, newSlots], by simp⟩
    · refine ⟨pad u v, ?_, ?_⟩
      · rw [hnext]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
      · simp [pad, direction, List.replicate_succ]

/-- The critical node has a split or an upper-cone continuation. Every
other node has exactly the binary successor pointing toward the critical
node in lexicographic order. -/
def CriticalChildren (critical : Word) (continuation : Bool) (w : Word)
    (a : TernaryLetter) : Prop :=
  if w = critical then
    if continuation then a = .one else a = .zero ∨ a = .two
  else a = direction critical w

theorem phase0_children (n : Nat) (u : Word) (rest : List Word)
    (ha : (stage n).active = u :: rest) (w : Word) (hw : InTree w)
    (hwlen : w.length = 3 * n) (a : TernaryLetter) :
    InTree (w ++ [a]) ↔ CriticalChildren u false w a := by
  have hactive := (inTree_stage_level n w hwlen).mp hw
  have hnot : u ∉ rest := (List.nodup_cons.mp (ha ▸ active_nodup n)).1
  rw [inTree_slot_tail n u rest ha w [a] hwlen (by simp)]
  rcases List.mem_cons.mp (ha ▸ hactive) with rfl | hwrest
  · simp [CriticalChildren, hnot]
  · have hne : w ≠ u := by intro h; exact hnot (h ▸ hwrest)
    simp [CriticalChildren, hne, hwrest, List.replicate_succ]

theorem phase1_children (n : Nat) (u : Word) (rest : List Word)
    (ha : (stage n).active = u :: rest) (w : Word) (hw : InTree w)
    (hwlen : w.length = 3 * n + 1) (a : TernaryLetter) :
    InTree (w ++ [a]) ↔ CriticalChildren (u ++ [.zero]) false w a := by
  have hulen : u.length = 3 * n := active_length n u (by simp [ha])
  have hnot : u ∉ rest := (List.nodup_cons.mp (ha ▸ active_nodup n)).1
  rcases (inTree_phase1 n u rest ha w hwlen).mp hw with rfl | rfl | ⟨v, hv, rfl⟩
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [inTree_slot_tail n u rest ha u [.zero, a] hulen (by simp)]
    simp [CriticalChildren, hnot]
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [inTree_slot_tail n u rest ha u [.two, a] hulen (by simp)]
    simp [CriticalChildren, hnot, direction, lexLess_common_prefix, lexLess, rank]
  · have hvlen := active_length n v (by simp [ha, hv])
    have hvu : v ≠ u := by intro h; exact hnot (h ▸ hv)
    have hneq : v ++ [direction u v] ≠ u ++ [.zero] := by
      intro heq
      exact hvu (List.append_inj_left heq (hvlen.trans hulen.symm))
    have hlex := lexLess_append_of_ne (hvlen.trans hulen.symm) hvu
      [direction u v] [.zero]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [inTree_slot_tail n u rest ha v [direction u v, a] hvlen (by simp)]
    have hdir : direction (u ++ [.zero]) (v ++ [direction u v]) = direction u v := by
      change (if lexLess (v ++ [direction u v]) (u ++ [.zero]) then _ else _) = _
      rw [hlex]
      rfl
    simp only [hvu, false_and, false_or, hv, true_and, CriticalChildren, hneq, ↓reduceIte, hdir]
    simp [List.replicate_succ]

theorem phase2_children (n : Nat) (u : Word) (rest : List Word)
    (ha : (stage n).active = u :: rest) (w : Word) (hw : InTree w)
    (hwlen : w.length = 3 * n + 2) (a : TernaryLetter) :
    InTree (w ++ [a]) ↔ CriticalChildren (u ++ [.zero, .two]) true w a := by
  have hulen : u.length = 3 * n := active_length n u (by simp [ha])
  have hnot : u ∉ rest := (List.nodup_cons.mp (ha ▸ active_nodup n)).1
  rcases (inTree_phase2 n u rest ha w hwlen).mp hw with rfl | rfl | rfl | ⟨v, hv, rfl⟩
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [inTree_slot_tail n u rest ha u [.zero, .zero, a] hulen (by simp)]
    simp [CriticalChildren, hnot, direction, lexLess_common_prefix, lexLess, rank]
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [inTree_slot_tail n u rest ha u [.zero, .two, a] hulen (by simp)]
    simp [CriticalChildren, hnot]
  · simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [inTree_slot_tail n u rest ha u [.two, .two, a] hulen (by simp)]
    simp [CriticalChildren, hnot, direction, lexLess_common_prefix, lexLess, rank]
  · have hvlen := active_length n v (by simp [ha, hv])
    have hvu : v ≠ u := by intro h; exact hnot (h ▸ hv)
    have hneq : v ++ [direction u v, direction u v] ≠ u ++ [.zero, .two] := by
      intro heq
      exact hvu (List.append_inj_left heq (hvlen.trans hulen.symm))
    have hlex := lexLess_append_of_ne (hvlen.trans hulen.symm) hvu
      [direction u v, direction u v] [.zero, .two]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [inTree_slot_tail n u rest ha v [direction u v, direction u v, a] hvlen (by simp)]
    have hdir : direction (u ++ [.zero, .two]) (v ++ [direction u v, direction u v]) =
        direction u v := by
      change (if lexLess (v ++ [direction u v, direction u v]) (u ++ [.zero, .two]) then _ else _) = _
      rw [hlex]
      rfl
    simp only [hvu, false_and, false_or, hv, true_and, CriticalChildren, hneq, ↓reduceIte, hdir]
    simp [List.replicate_succ]

/-- The explicit critical node at every ambient level. -/
def critical (j : Nat) : Word :=
  ((stage (j / 3)).active.head!) ++ ([.zero, .two] : Word).take (j % 3)

/-- The unique critical-node rule for every level of the actual infinite
tree. The critical node is a fork at remainders 0 and 1, and an incoming
upper-cone parent at remainder 2. -/
theorem critical_data (j : Nat) :
    InTree (critical j) ∧ (critical j).length = j ∧
      ∀ w, InTree w → w.length = j → ∀ a,
        InTree (w ++ [a]) ↔ CriticalChildren (critical j) (decide (j % 3 = 2)) w a := by
  obtain ⟨u, rest, ha, hulen, _⟩ := active_head_exists (j / 3)
  have hrem : j % 3 < 3 := Nat.mod_lt _ (by decide)
  by_cases h0 : j % 3 = 0
  · have hcrit : critical j = u := by simp [critical, h0, ha, List.head!]
    rw [hcrit]
    refine ⟨active_inTree (j / 3) u (by simp [ha]), by omega, ?_⟩
    intro w hw hlen a
    simpa [h0] using
      phase0_children (j / 3) u rest ha w hw (by omega) a
  · by_cases h1 : j % 3 = 1
    · have hcrit : critical j = u ++ [.zero] := by simp [critical, h1, ha, List.head!]
      rw [hcrit]
      refine ⟨?_, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
      · apply (inTree_phase1 (j / 3) u rest ha _ (by simp [hulen])).mpr
        exact Or.inl rfl
      · intro w hw hlen a
        simpa [h1] using
          phase1_children (j / 3) u rest ha w hw (by omega) a
    · have h2 : j % 3 = 2 := by omega
      have hcrit : critical j = u ++ [.zero, .two] := by simp [critical, h2, ha, List.head!]
      rw [hcrit]
      refine ⟨?_, by simp only [List.length_append, List.length_cons, List.length_nil]; omega, ?_⟩
      · apply (inTree_phase2 (j / 3) u rest ha _ (by simp [hulen])).mpr
        exact Or.inr (Or.inl rfl)
      · intro w hw hlen a
        simpa [h2] using
          phase2_children (j / 3) u rest ha w hw (by omega) a

theorem critical_inTree (j : Nat) : InTree (critical j) := (critical_data j).1

theorem critical_length (j : Nat) : (critical j).length = j := (critical_data j).2.1

theorem critical_children (j : Nat) (w : Word) (hw : InTree w) (hlen : w.length = j)
    (a : TernaryLetter) :
    InTree (w ++ [a]) ↔ CriticalChildren (critical j) (decide (j % 3 = 2)) w a :=
  (critical_data j).2.2 w hw hlen a

theorem critical_code (j : Nat) (hj : j % 3 = 2) : critical j = code (j / 3) := by
  simp [critical, hj, code, newCode]

/-- Coding nodes occur exactly at the critical node of a phase-two level. -/
theorem inSparse_at_level (j : Nat) (w : Word) (hlen : w.length = j) :
    InSparse w ↔ j % 3 = 2 ∧ w = critical j := by
  constructor
  · intro hw
    obtain ⟨n, hn⟩ := (inSparse_iff_code w).mp hw
    have hj : j = 3 * n + 2 := by rw [hn, code_length] at hlen; omega
    have hmod : j % 3 = 2 := by omega
    refine ⟨hmod, ?_⟩
    rw [critical_code j hmod, show j / 3 = n by omega]
    exact hn
  · rintro ⟨hj, rfl⟩
    apply (inSparse_iff_code _).mpr
    exact ⟨j / 3, critical_code j hj⟩

/-- Consequently no level has two distinct forks. -/
theorem fork_unique {s t : Word} (hs0 : InTree (s ++ [.zero])) (hs2 : InTree (s ++ [.two]))
    (ht0 : InTree (t ++ [.zero])) (ht2 : InTree (t ++ [.two])) (hlen : s.length = t.length) :
    s = t := by
  have hs : InTree s := inTree_prefix hs0 (List.prefix_append _ _)
  have ht : InTree t := inTree_prefix ht0 (List.prefix_append _ _)
  have heq (w : Word) (hw : InTree w) (hwl : w.length = s.length)
      (hw0 : InTree (w ++ [.zero])) (hw2 : InTree (w ++ [.two])) : w = critical s.length := by
    have h0 := (critical_children s.length w hw hwl .zero).mp hw0
    have h2 := (critical_children s.length w hw hwl .two).mp hw2
    by_cases h : w = critical s.length
    · exact h
    · simp only [CriticalChildren, h, ↓reduceIte] at h0 h2
      have := h0.trans h2.symm
      contradiction
  exact (heq s hs rfl hs0 hs2).trans (heq t ht hlen.symm ht0 ht2).symm

end AllThoseBigRamsey.Pseudotree.Sparse
