import PseudotreeValidation.DiaryNormalization

/-! Local prefix and child correspondences for selected-level normalization. -/

namespace AllThoseBigRamsey.Pseudotree.DiaryNormalization

open RayEmbeddings LevelProjection

def RawNode (C : Finset Word) (s : Word) : Prop := ∃ w ∈ C, s.IsPrefix w

theorem inverse_length {C : Finset Word} {v s : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C v) :
    (inverse (C : Set Word) (schedule (selected C v)) s).length =
      schedule (selected C v) s.length := by
  obtain ⟨w, hw, hlen, heq⟩ := (mem_nodes_iff_domain hC).mp hs
  rw [inverse_eq (schedule_strict (selected_nonempty hC v))
    (schedule_covers_essential C v) hw hlen heq, List.length_take, Nat.min_eq_left hlen]

theorem inverse_rawNode {C : Finset Word} {v s : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C v) : RawNode C (inverse (C : Set Word) (schedule (selected C v)) s) := by
  obtain ⟨w, hw, hlen, heq⟩ := (mem_nodes_iff_domain hC).mp hs
  refine ⟨w, hw, ?_⟩
  rw [inverse_eq (schedule_strict (selected_nonempty hC v))
    (schedule_covers_essential C v) hw hlen heq]
  exact List.take_prefix _ _

theorem project_of_rawNode {C : Finset Word} {v w : Word} (hC : C.Nonempty)
    (hw : RawNode C w) {j : Nat} (hlen : w.length = schedule (selected C v) j) :
    project (schedule (selected C v)) w j ∈ nodes C v ∧
      inverse (C : Set Word) (schedule (selected C v))
        (project (schedule (selected C v)) w j) = w := by
  obtain ⟨c, hc, hp⟩ := hw
  have hcj : schedule (selected C v) j ≤ c.length := by
    simpa only [← hlen] using hp.length_le
  have ht : c.take (schedule (selected C v) j) = w := by
    simpa only [hlen] using (List.prefix_iff_eq_take.mp hp).symm
  have heq := project_eq_of_take_eq (schedule_strict (selected_nonempty hC v))
    (s := c) (t := w) (j := j) (by rw [ht, ← hlen, List.take_length])
  constructor
  · rw [← heq]
    exact (mem_nodes_iff_domain hC).mpr (domain_project hc hcj)
  · rw [← heq, inverse_project (schedule_strict (selected_nonempty hC v))
      (schedule_covers_essential C v) hc hcj, ht]

theorem inverse_injective {C : Finset Word} {v s t : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C v) (ht : t ∈ nodes C v)
    (heq : inverse (C : Set Word) (schedule (selected C v)) s =
      inverse (C : Set Word) (schedule (selected C v)) t) : s = t := by
  have hlen := congrArg List.length heq
  rw [inverse_length hC hs, inverse_length hC ht] at hlen
  have hlen' := (schedule_strict (selected_nonempty hC v)).injective hlen
  rw [← project_of_node hC hs, ← project_of_node hC ht, heq, hlen']

theorem code_iff_inverse {C : Finset Word} {v s : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C v) :
    s ∈ codes C v ↔ inverse (C : Set Word) (schedule (selected C v)) s ∈ C := by
  classical
  constructor
  · intro hc
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hc
    rw [← heq, inverse_project (schedule_strict (selected_nonempty hC v))
      (schedule_covers_essential C v) hw
      (schedule_rank (essential_subset_selected C v (length_mem_essential hw))).le,
      schedule_rank (essential_subset_selected C v (length_mem_essential hw)), List.take_length]
    exact hw
  · intro hc
    let w := inverse (C : Set Word) (schedule (selected C v)) s
    have hw : w ∈ C := hc
    have hlen : rank (selected C v) w.length = s.length := by
      apply (schedule_strict (selected_nonempty hC v)).injective
      rw [schedule_rank (essential_subset_selected C v (length_mem_essential hw))]
      exact inverse_length hC hs
    exact Finset.mem_image.mpr ⟨w, hw, by rw [hlen]; exact project_of_node hC hs⟩

/-- Compression retains precisely the actual children of each prefix in the
finite coding tree. Empty stretches have one descendant and add no branch. -/
theorem child_iff_rawChild {C : Finset Word} {v s : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C v) (a : Fin 3) :
    child s a ∈ nodes C v ↔
      RawNode C (child (inverse (C : Set Word) (schedule (selected C v)) s) a) := by
  let K := schedule (selected C v)
  have hK : StrictMono K := schedule_strict (selected_nonempty hC v)
  have hsep := schedule_covers_essential C v
  constructor
  · intro hchild
    obtain ⟨w, hw, hlen, heq⟩ := (mem_nodes_iff_domain hC).mp hchild
    have heq' : project K w (s.length+1) = s ++ [a] := by simpa only [child,
      List.length_append, List.length_singleton] using heq
    have hlen' : K (s.length+1) ≤ w.length := by simpa [K, child] using hlen
    have hj : K s.length < w.length := lt_of_lt_of_le (hK (Nat.lt_succ_self _)) hlen'
    have hp : project K w s.length = s := by
      have h := congrArg (List.take s.length) heq
      simpa only [child, project_take _ _ (by simp : s.length ≤ (s ++ [a]).length),
        List.take_left] using h
    have ha : w[K s.length] = a := by
      have h' : [w[K s.length]] = [a] := List.append_cancel_left (by
        simpa only [child, List.length_append, List.length_singleton, project_succ, hp,
          List.getElem?_eq_getElem hj, Option.getD_some] using heq')
      exact List.singleton_inj.mp h'
    refine ⟨w, hw, ?_⟩
    rw [inverse_eq hK hsep hw hj.le hp]
    change (w.take (K s.length) ++ [a]).IsPrefix w
    rw [← ha, List.take_append_getElem hj]
    exact List.take_prefix _ _
  · rintro ⟨w, hw, tail, htail⟩
    let p := inverse (C : Set Word) K s
    have hplen : p.length = K s.length := inverse_length hC hs
    have htail' : w = p ++ a :: tail := by simpa [p, child] using htail.symm
    have hlength : K s.length < w.length := by
      rw [htail']
      simp only [List.length_append, List.length_cons]
      omega
    have hjrank : s.length < rank (selected C v) w.length := hK.lt_iff_lt.mp (by
      simpa only [K, schedule_rank (essential_subset_selected C v (length_mem_essential hw))]
        using hlength)
    have hnext : K (s.length+1) ≤ w.length := by
      have h := hK.monotone (Nat.succ_le_of_lt hjrank)
      simpa only [K, schedule_rank (essential_subset_selected C v (length_mem_essential hw))] using h
    have htake : w.take (K s.length) = p := by rw [← hplen, htail']; simp
    have hp : project K w s.length = s :=
      (project_eq_of_take_eq hK (by rw [htake, ← hplen, List.take_length])).trans
        (project_of_node hC hs)
    have ha : w[K s.length]?.getD 0 = a := by rw [← hplen, htail']; simp
    apply (mem_nodes_iff_domain hC).mpr
    refine ⟨w, hw, ?_, ?_⟩
    · simpa [child, K] using hnext
    · have heq : project K w (s.length+1) = s ++ [a] := by rw [project_succ, hp, ha]
      simpa only [child, List.length_append, List.length_singleton] using heq

private theorem map_lex_aux (f : RayStrongMap) (s : Word) :
    ∀ t u : Word, s < t → f.map (u ++ s) < f.map (u ++ t) := by
  induction s with
  | nil =>
      intro t u hst
      cases t with
      | nil => exact (lt_irrefl [] hst).elim
      | cons a t =>
          obtain ⟨pad, hp⟩ := f.map_append_cons u a t
          rw [List.append_nil, hp]
          have hlex : List.Lex (fun x y : Fin 3 => x < y)
              (f.map u ++ []) (f.map u ++ a :: pad) :=
            List.Lex.append_left (· < ·) .nil (f.map u)
          change List.Lex (fun x y : Fin 3 => x < y) (f.map u) (f.map u ++ a :: pad)
          simpa only [List.append_nil] using hlex
  | cons a s ih =>
      intro t u hst
      cases t with
      | nil => exact (List.not_lex_nil hst).elim
      | cons b t =>
          rcases List.cons_lt_cons_iff.mp hst with hab | hcons
          · obtain ⟨p, hp⟩ := f.map_append_cons u a s
            obtain ⟨q, hq⟩ := f.map_append_cons u b t
            rw [hp, hq]
            exact List.Lex.append_left (· < ·) (List.Lex.rel hab) (f.map u)
          · obtain ⟨hab, hsmall⟩ := hcons
            subst b
            simpa only [List.append_assoc, List.singleton_append] using ih t (u ++ [a]) hsmall

theorem rayMap_strictMono (f : RayStrongMap) : StrictMono f.map := by
  intro s t hst
  simpa using map_lex_aux f s t [] hst

theorem inverse_lt_iff {C : Finset Word} {v s t : Word} (hC : C.Nonempty)
    (hspine : Spine C v) (hs : s ∈ nodes C v) (ht : t ∈ nodes C v) :
    inverse (C : Set Word) (schedule (selected C v)) s <
      inverse (C : Set Word) (schedule (selected C v)) t ↔ s < t := by
  have hfs : (rayMap hC hspine).map s = inverse (C : Set Word) (schedule (selected C v)) s :=
    PrefixRayMap.completion_agrees _ _ ((mem_nodes_iff_domain hC).mp hs)
  have hft : (rayMap hC hspine).map t = inverse (C : Set Word) (schedule (selected C v)) t :=
    PrefixRayMap.completion_agrees _ _ ((mem_nodes_iff_domain hC).mp ht)
  rw [← hfs, ← hft]
  exact (rayMap_strictMono _).lt_iff_lt

end AllThoseBigRamsey.Pseudotree.DiaryNormalization
