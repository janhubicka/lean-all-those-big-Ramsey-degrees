import AllThoseBigRamsey.Pseudotree.SparseFair

/-! Prefix separation in the sparse coding set. -/

namespace AllThoseBigRamsey.Pseudotree.Sparse

theorem pad_injective {u v w : Word} (h : pad u v = pad u w) : v = w :=
  List.append_inj_left' h (by simp)

theorem newSlots_nodup (u : Word) : (newSlots u).Nodup := by
  simp [newSlots]

/-- Active slots never collide; the queue order need not be lexicographic. -/
theorem active_nodup (n : Nat) : (stage n).active.Nodup := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    have hn : (stage n).active ≠ [] := by
      intro h
      have hl := (stage_lengths n).1
      simp [h] at hl
    obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
    have hnd : u ∉ rest ∧ rest.Nodup := by simpa [ha] using ih
    have hu : u.length = 3 * n := active_length n u (by simp [ha])
    simp only [stage, advance, ha]
    apply List.nodup_append.mpr
    refine ⟨?_, newSlots_nodup u, ?_⟩
    · apply List.pairwise_map.mpr
      exact hnd.2.imp (fun hne heq => hne (pad_injective heq))
    · intro v hv w hw heq
      obtain ⟨v, hvrest, rfl⟩ := List.mem_map.mp hv
      have hvlen : v.length = u.length := (active_length n v (by simp [ha, hvrest])).trans hu.symm
      have hwu : ∃ t, w = u ++ t := by
        simp only [newSlots, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl <;> exact ⟨_, rfl⟩
      obtain ⟨t, rfl⟩ := hwu
      have hequ : v = u := List.append_inj_left heq hvlen
      exact hnd.1 (hequ ▸ hvrest)

theorem old_code_length_lt (n : Nat) {p : Word} (hp : p ∈ (stage n).codes) :
    p.length < 3 * n := by
  obtain ⟨j, hj, rfl⟩ := (mem_stage_codes_iff n p).mp hp
  rw [code_length]
  omega

/-- Below an old coding node, every surviving prefix continuation begins
with `1`. This is the extra prefix case needed in the corrected lexicographic
claim in the sparse-copy lemma. -/
theorem active_code_prefix_one (n : Nat) :
    ∀ p ∈ (stage n).codes, ∀ w ∈ (stage n).active,
      p.IsPrefix w → (p ++ [TernaryLetter.one]).IsPrefix w := by
  induction n with
  | zero => simp [stage]
  | succ n ih =>
    have hn : (stage n).active ≠ [] := by
      intro h
      have hl := (stage_lengths n).1
      simp [h] at hl
    obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hn
    have hu : u ∈ (stage n).active := by simp [ha]
    have hulen := active_length n u hu
    have hnd : u ∉ rest := (List.nodup_cons.mp (ha ▸ active_nodup n)).1
    have hcode : code n = newCode u := by simp [code, ha, List.head!]
    intro p hp w hw hpw
    rw [stage_codes_succ, List.mem_append, List.mem_singleton, hcode] at hp
    have hw' : w ∈ rest.map (pad u) ++ newSlots u := by simpa [stage, advance, ha] using hw
    rcases hp with hp | rfl
    · have hplen := old_code_length_lt n hp
      have source : ∃ v ∈ (stage n).active, v.IsPrefix w := by
        rcases List.mem_append.mp hw' with hw' | hw'
        · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw'
          exact ⟨v, by simp [ha, hv], ⟨_, rfl⟩⟩
        · simp only [newSlots, List.mem_cons, List.not_mem_nil, or_false] at hw'
          rcases hw' with rfl | rfl | rfl <;> exact ⟨u, hu, ⟨_, rfl⟩⟩
      obtain ⟨v, hv, hvw⟩ := source
      have hpv : p.IsPrefix v := List.prefix_of_prefix_length_le hpw hvw
        (by rw [active_length n v hv]; omega)
      exact (ih p hp v hv hpv).trans hvw
    · rcases List.mem_append.mp hw' with hw' | hw'
      · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw'
        have hvlen : u.length = v.length := hulen.trans (active_length n v (by simp [ha, hv])).symm
        have huv : u = v := (List.prefix_append_inj_of_length_eq hvlen).mp hpw |>.1
        exact False.elim (hnd (huv ▸ hv))
      · simp only [newSlots, List.mem_cons, List.not_mem_nil, or_false] at hw'
        rcases hw' with rfl | rfl | rfl
        · simp [newCode] at hpw
        · exact ⟨[], by simp [newCode, List.append_assoc]⟩
        · simp [newCode] at hpw

/-- A proper prefix relation between sparse coding nodes must enter the
upper cone immediately at the shorter coding node. -/
theorem code_prefix_one {n m : Nat} (hpre : (code n).IsPrefix (code m)) (hne : n ≠ m) :
    (code n ++ [TernaryLetter.one]).IsPrefix (code m) := by
  have hnm : n < m := by
    have hl := hpre.length_le
    rw [code_length, code_length] at hl
    omega
  have hm : (stage m).active ≠ [] := by
    intro h
    have hl := (stage_lengths m).1
    simp [h] at hl
  obtain ⟨u, rest, ha⟩ := List.exists_cons_of_ne_nil hm
  have hu : u ∈ (stage m).active := by simp [ha]
  have hcode : code m = u ++ [.zero, .two] := by simp [code, ha, List.head!, newCode]
  have hpu : (code n).IsPrefix u := List.prefix_of_prefix_length_le
    (hcode ▸ hpre) (List.prefix_append u _) (by rw [code_length, active_length m u hu]; omega)
  have hp : code n ∈ (stage m).codes := (mem_stage_codes_iff m (code n)).mpr ⟨n, hnm, rfl⟩
  rw [hcode]
  exact (active_code_prefix_one m (code n) hp u hu hpu).trans (List.prefix_append u _)

end AllThoseBigRamsey.Pseudotree.Sparse
