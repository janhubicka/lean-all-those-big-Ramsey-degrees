import PseudotreeValidation.LiteralDiaries

/-! Soundness in the raw finite-set diary axioms and the resulting bijection. -/

namespace AllThoseBigRamsey.Pseudotree

theorem PaperLevel.unique {nodes codes : Finset DiaryWord} {j : Nat}
    {kind kind' : PaperKind} {c c' : DiaryWord}
    (P : PaperLevel nodes codes j kind c) (Q : PaperLevel nodes codes j kind' c') :
    c = c' ∧ kind = kind' := by
  have hcrit : c = c' := by
    by_contra hne
    have h0 := (P.children c P.critical_mem P.critical_length 0).symm.trans
      (Q.children c P.critical_mem P.critical_length 0)
    have h1 := (P.children c P.critical_mem P.critical_length 1).symm.trans
      (Q.children c P.critical_mem P.critical_length 1)
    have h2 := (P.children c P.critical_mem P.critical_length 2).symm.trans
      (Q.children c P.critical_mem P.critical_length 2)
    cases kind <;> by_cases hlt : c < c' <;>
      simp [localChild, PaperKind.special, hne, hlt] at h0 h1 h2
  subst c'
  refine ⟨rfl, ?_⟩
  have hc := (P.coding c P.critical_mem P.critical_length).symm.trans
    (Q.coding c P.critical_mem P.critical_length)
  have h0 := (P.children c P.critical_mem P.critical_length 0).symm.trans
    (Q.children c P.critical_mem P.critical_length 0)
  have h1 := (P.children c P.critical_mem P.critical_length 1).symm.trans
    (Q.children c P.critical_mem P.critical_length 1)
  cases kind <;> cases kind' <;> simp_all [localChild, PaperKind.special, PaperKind.coded]

theorem DiaryEvent.local_data (e : DiaryEvent) (ws : List DiaryWord)
    (he : e.legal ws.length) (hs : ws.Pairwise (fun u v => u < v))
    (hone : e = .code ∨ e = .turn → ∀ w ∈ ws.head?.toList, (2 : Fin 3) ∉ w) :
    ∃ c ∈ ws,
      (∀ w, w ∈ e.coding ws ↔ w = c ∧ e.kind.coded = true) ∧
      (∀ w ∈ ws, ∀ a, child w a ∈ e.next ws ↔ localChild c e.kind.special w a) ∧
      (e.kind.continues = true → (2 : Fin 3) ∉ c) := by
  cases e with
  | split i =>
      have hi : i < ws.length := he
      let c := ws[i]
      have hsplit : ws = ws.take i ++ c :: ws.drop (i + 1) := by
        rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
      have htake : (ws.take i).length = i := by simp [Nat.min_eq_left hi.le]
      refine ⟨c, List.getElem_mem hi, ?_, ?_, ?_⟩
      · intro w; simp [DiaryEvent.coding, DiaryEvent.kind, PaperKind.coded]
      · intro w hw a
        have hs' := hsplit ▸ hs
        have hw' := hsplit ▸ hw
        change child w a ∈ splitFrontier i ws ↔ localChild c (fun a => a = 0 ∨ a = 2) w a
        simpa only [htake, ← hsplit] using splitFrontier_child_local hs' hw' a
      · simp [DiaryEvent.kind, PaperKind.continues]
  | leaf i =>
      have hi : i < ws.length := he
      let c := ws[i]
      have hsplit : ws = ws.take i ++ c :: ws.drop (i + 1) := by
        rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
      have htake : (ws.take i).length = i := by simp [Nat.min_eq_left hi.le]
      refine ⟨c, List.getElem_mem hi, ?_, ?_, ?_⟩
      · intro w
        simp [DiaryEvent.coding, DiaryEvent.kind, PaperKind.coded, List.getElem?_eq_getElem hi, c]
      · intro w hw a
        have hs' := hsplit ▸ hs
        have hw' := hsplit ▸ hw
        change child w a ∈ leafFrontier i ws ↔ localChild c (fun _ => False) w a
        simpa only [htake, ← hsplit] using leafFrontier_child_local hs' hw' a
      · simp [DiaryEvent.kind, PaperKind.continues]
  | code =>
      cases ws with
      | nil => simp [DiaryEvent.legal] at he
      | cons c ws =>
          refine ⟨c, by simp, ?_, ?_, ?_⟩
          · intro w; simp [DiaryEvent.coding, DiaryEvent.kind, PaperKind.coded]
          · exact fun w hw a => continueFrontier_child_local hs hw a
          · exact fun _ => hone (Or.inl rfl) c (by simp)
  | turn =>
      cases ws with
      | nil => simp [DiaryEvent.legal] at he
      | cons c ws =>
          refine ⟨c, by simp, ?_, ?_, ?_⟩
          · intro w; simp [DiaryEvent.coding, DiaryEvent.kind, PaperKind.coded]
          · exact fun w hw a => continueFrontier_child_local hs hw a
          · exact fun _ => hone (Or.inr rfl) c (by simp)

theorem execute_nodes_at_succ (e : DiaryEvent) (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) :
    (execute (e :: es) ws).nodes.filter (fun w => w.length == h + 1) = e.next ws := by
  have hempty : ws.filter (fun w => w.length == h + 1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro w hw
    simp [hws w hw]
  simp only [execute, List.filter_append, hempty, List.nil_append]
  exact execute_nodes_at_start es (e.next_lengths hws)

theorem execute_nodes_mem_start (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) (hw : w.length = h) :
    w ∈ (execute es ws).nodes ↔ w ∈ ws := by
  have hmem : w ∈ (execute es ws).nodes.filter (fun w => w.length == h) ↔ w ∈ ws := by
    rw [execute_nodes_at_start es hws]
  simpa only [List.mem_filter, hw, beq_self_eq_true, and_true] using hmem

theorem execute_codes_mem_start (e : DiaryEvent) (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) (hw : w.length = h) :
    w ∈ (execute (e :: es) ws).codes ↔ w ∈ e.coding ws := by
  have hmem : w ∈ (execute (e :: es) ws).codes.filter (fun w => w.length == h) ↔
      w ∈ e.coding ws := by rw [execute_codes_at_start e es hws]
  simpa only [List.mem_filter, hw, beq_self_eq_true, and_true] using hmem

theorem execute_nodes_mem_succ (e : DiaryEvent) (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) (hw : w.length = h + 1) :
    w ∈ (execute (e :: es) ws).nodes ↔ w ∈ e.next ws := by
  have hmem : w ∈ (execute (e :: es) ws).nodes.filter (fun w => w.length == h + 1) ↔
      w ∈ e.next ws := by rw [execute_nodes_at_succ e es hws]
  simpa only [List.mem_filter, hw, beq_self_eq_true, and_true] using hmem

theorem execute_paperLevel_start (e : DiaryEvent) (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) (hs : ws.Pairwise (fun u v => u < v))
    (he : e.legal ws.length)
    (hone : e = .code ∨ e = .turn → ∀ w ∈ ws.head?.toList, (2 : Fin 3) ∉ w) :
    ∃ c, PaperLevel (execute (e :: es) ws).nodes.toFinset
      (execute (e :: es) ws).codes.toFinset h e.kind c := by
  obtain ⟨c, hc, hcoding, hchildren, horiginal⟩ := e.local_data ws he hs hone
  refine ⟨c, ?_⟩
  constructor
  · exact List.mem_toFinset.mpr (execute_frontier (e :: es) hc)
  · exact hws c hc
  · intro w hw hwlen
    rw [List.mem_toFinset, execute_codes_mem_start e es hws hwlen]
    exact hcoding w
  · intro w hw hwlen a
    have hw' := (execute_nodes_mem_start (e :: es) hws hwlen).mp (List.mem_toFinset.mp hw)
    rw [List.mem_toFinset, execute_nodes_mem_succ e es hws (by simp [child, hwlen])]
    exact hchildren w hw' a
  · exact horiginal

theorem execute_nodes_mem_tail (e : DiaryEvent) (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) (hw : h < w.length) :
    w ∈ (execute (e :: es) ws).nodes ↔ w ∈ (execute es (e.next ws)).nodes := by
  have hnot : w ∉ ws := by intro hmem; have := hws w hmem; omega
  simp only [execute, List.mem_append, hnot, false_or]

theorem execute_codes_mem_tail (e : DiaryEvent) (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) (hw : h < w.length) :
    w ∈ (execute (e :: es) ws).codes ↔ w ∈ (execute es (e.next ws)).codes := by
  have hnot : w ∉ e.coding ws := by
    intro hmem
    have := hws w (e.coding_mem hmem)
    omega
  simp only [execute, List.mem_append, hnot, false_or]

theorem execute_paperLevel_of_tail (e : DiaryEvent) (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) (hj : h < j)
    (P : PaperLevel (execute es (e.next ws)).nodes.toFinset
      (execute es (e.next ws)).codes.toFinset j kind c) :
    PaperLevel (execute (e :: es) ws).nodes.toFinset
      (execute (e :: es) ws).codes.toFinset j kind c := by
  constructor
  · exact List.mem_toFinset.mpr ((execute_nodes_mem_tail e es hws
      (by rw [P.critical_length]; exact hj)).mpr (List.mem_toFinset.mp P.critical_mem))
  · exact P.critical_length
  · intro w hw hwlen
    have hw' := (execute_nodes_mem_tail e es hws (by omega)).mp (List.mem_toFinset.mp hw)
    rw [List.mem_toFinset, execute_codes_mem_tail e es hws (by omega)]
    simpa only [List.mem_toFinset] using P.coding w (List.mem_toFinset.mpr hw') hwlen
  · intro w hw hwlen a
    have hw' := (execute_nodes_mem_tail e es hws (by omega)).mp (List.mem_toFinset.mp hw)
    rw [List.mem_toFinset, execute_nodes_mem_tail e es hws (by simp [child, hwlen]; omega)]
    simpa only [List.mem_toFinset] using P.children w (List.mem_toFinset.mpr hw') hwlen a
  · exact P.original

theorem execute_nodes_length_lt (es : List DiaryEvent)
    (hw : WidthValid ws.length es) (hws : ∀ w ∈ ws, w.length = h)
    (hv : v ∈ (execute es ws).nodes) : v.length < h + es.length := by
  induction es generalizing ws h with
  | nil =>
      have hnil : ws = [] := List.eq_nil_of_length_eq_zero hw
      simp [execute, hnil] at hv
  | cons e es ih =>
      rcases List.mem_append.mp hv with hv | hv
      · have hlen := hws v hv
        simp only [List.length_cons]
        omega
      · have hlen := ih (e.next_width_valid hw) (e.next_lengths hws) hv
        simp only [List.length_cons]
        omega

/-- Every event in the execution induces precisely the paper's raw set
level rules at its actual height. -/
theorem execute_paperLevel (es : List DiaryEvent)
    (hw : WidthValid ws.length es) (hl : LeftValid left es)
    (ho : OriginalFrontier left ws) (hs : ws.Pairwise (fun u v => u < v))
    (hws : ∀ w ∈ ws, w.length = h) (t : Nat) (ht : t < es.length) :
    ∃ c, PaperLevel (execute es ws).nodes.toFinset (execute es ws).codes.toFinset
      (h + t) es[t].kind c := by
  induction es generalizing ws h left t with
  | nil => simp at ht
  | cons e es ih =>
      cases t with
      | zero =>
          have hone : e = .code ∨ e = .turn →
              ∀ w ∈ ws.head?.toList, (2 : Fin 3) ∉ w := by
            intro heq
            rcases heq with rfl | rfl
            · obtain ⟨rfl, _⟩ := hl
              exact fun _ => originalFrontier_head ho
            · obtain ⟨rfl, _⟩ := hl
              exact fun _ => originalFrontier_head ho
          simpa only [Nat.add_zero, List.getElem_cons_zero] using
            execute_paperLevel_start e es hws hs (e.legal_of_width hw) hone
      | succ t =>
          have ht' : t < es.length := by simpa using ht
          obtain ⟨c, P⟩ := ih (e.next_width_valid hw) (e.tail_leftValid hl)
            (e.next_original ho) (e.next_sorted hs hws) (e.next_lengths hws) t ht'
          have P' := execute_paperLevel_of_tail e es hws (j := h + 1 + t) (by omega) P
          refine ⟨c, ?_⟩
          simpa only [List.getElem_cons_succ, show h + (t + 1) = h + 1 + t by omega] using P'

theorem turnsLegal_first_not_turn (ht : TurnsLegal false es) (hp : 0 < es.length) :
    es[0] ≠ .turn := by
  cases es with
  | nil => simp at hp
  | cons e es =>
      intro heq
      have he : e = .turn := heq
      subst e
      simp [TurnsLegal] at ht

theorem turnsLegal_turn_previous (ht : TurnsLegal allowed es) (hj : j + 1 < es.length)
    (he : es[j + 1] = .turn) : es[j].allowsTurn = true := by
  induction es generalizing j allowed with
  | nil => simp at hj
  | cons e es ih =>
      cases j with
      | zero =>
          cases es with
          | nil => simp at hj
          | cons f fs =>
              have hf : f = .turn := he
              subst f
              cases e <;> simp_all [TurnsLegal, DiaryEvent.allowsTurn]
      | succ j =>
          have hj' : j + 1 < es.length := by simpa using hj
          have he' : es[j + 1] = .turn := by simpa using he
          exact ih (e.tail_turnsLegal ht) hj' he'

@[simp] theorem DiaryEvent.kind_eq_turn (e : DiaryEvent) : e.kind = .turn ↔ e = .turn := by
  cases e <;> simp [DiaryEvent.kind]

theorem widthValid_trace_pos (hw : WidthValid k es) (hk : 0 < k) : 0 < es.length := by
  cases es with
  | nil => simp [WidthValid] at hw; omega
  | cons => simp

/-- Every grammar diary satisfies exactly the raw finite-set axioms. Together
with `PaperDiary.represented`, this closes the unordered-tree bridge. -/
theorem Diary.paper_axioms (d : Diary true n 1) :
    PaperTreeAxioms d.toTree.nodes.toFinset d.toTree.codes.toFinset d.events.length := by
  have hw : WidthValid ([[]] : List DiaryWord).length d.events := by simpa using d.width_valid
  have hp := widthValid_trace_pos hw (by simp)
  have hlevels (j : Nat) (hj : j < d.events.length) :
      ∃ c, PaperLevel d.toTree.nodes.toFinset d.toTree.codes.toFinset j d.events[j].kind c := by
    simpa only [Nat.zero_add, Diary.toTree] using execute_paperLevel d.events hw d.left_valid
      (by simp [OriginalFrontier]) (by simp) (h := 0) (by simp) j hj
  refine ⟨hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw'
    have hb := execute_nodes_length_lt d.events hw (h := 0) (by simp) (List.mem_toFinset.mp hw')
    simpa only [Nat.zero_add] using hb
  · intro w hw' j hj
    exact List.mem_toFinset.mpr (d.toTree_prefix_closed (List.mem_toFinset.mp hw') hj)
  · intro w hw'
    exact List.mem_toFinset.mpr (execute_codes_nodes d.events (List.mem_toFinset.mp hw'))
  · intro j hj
    obtain ⟨c, P⟩ := hlevels j hj
    exact ⟨d.events[j].kind, c, P⟩
  · intro c P
    obtain ⟨c', Q⟩ := hlevels 0 hp
    have he := (DiaryEvent.kind_eq_turn _).mp (Q.unique P).2
    exact turnsLegal_first_not_turn (d.turns_legal false) hp he
  · intro j c kind previous P Q
    have hb := execute_nodes_length_lt d.events hw (h := 0) (by simp)
      (List.mem_toFinset.mp P.critical_mem)
    have hj : j + 1 < d.events.length := by simpa only [Nat.zero_add, P.critical_length] using hb
    have hj' : j < d.events.length := by omega
    obtain ⟨c', P'⟩ := hlevels (j + 1) hj
    obtain ⟨previous', Q'⟩ := hlevels j hj'
    have he := (DiaryEvent.kind_eq_turn _).mp (P'.unique P).2
    have hprev := turnsLegal_turn_previous (d.turns_legal false) hj he
    rw [← DiaryEvent.kind_allowsTurn, (Q'.unique Q).2] at hprev
    exact hprev

/-- The actual finite SET diary associated with a grammar object. -/
def Diary.toPaper (d : Diary true n 1) : PaperDiary n where
  nodes := d.toTree.nodes.toFinset
  codes := d.toTree.codes.toFinset
  axioms := ⟨d.events.length, d.paper_axioms⟩
  size := by rw [List.toFinset_card_of_nodup d.toTree_codes_nodup]; exact d.toTree_coding_count

@[ext] theorem PaperDiary.ext {D E : PaperDiary n} (hnodes : D.nodes = E.nodes)
    (hcodes : D.codes = E.codes) : D = E := by
  cases D
  cases E
  cases hnodes
  cases hcodes
  rfl

theorem Diary.toPaper_injective (d e : Diary true n 1) (h : d.toPaper = e.toPaper) : d = e := by
  apply d.toTree_codes_ext_injective e
  intro w
  have hc := congrArg PaperDiary.codes h
  have hmem : w ∈ d.toPaper.codes ↔ w ∈ e.toPaper.codes := by rw [hc]
  simpa only [Diary.toPaper, List.mem_toFinset] using hmem

theorem Diary.toPaper_surjective (D : PaperDiary n) : ∃ d : Diary true n 1, d.toPaper = D := by
  obtain ⟨d, hn, hc⟩ := D.represented
  refine ⟨d, PaperDiary.ext ?_ ?_⟩
  · ext w
    exact (List.mem_toFinset).trans (hn w)
  · ext w
    exact (List.mem_toFinset).trans (hc w)

def paperDiaryEnum (n : Nat) : List (PaperDiary n) := (diaryEnum true n 1).map Diary.toPaper

theorem paperDiaryEnum_complete (D : PaperDiary n) : D ∈ paperDiaryEnum n := by
  obtain ⟨d, rfl⟩ := Diary.toPaper_surjective D
  exact List.mem_map.mpr ⟨d, diaryEnum_complete d, rfl⟩

theorem paperDiaryEnum_nodup (n : Nat) : (paperDiaryEnum n).Nodup :=
  diaryMap_nodup _ _ (diaryEnum_nodup true n 1) Diary.toPaper_injective

theorem paperDiaryEnum_length (n : Nat) : (paperDiaryEnum n).length = diaryCount true n 1 := by
  simp only [paperDiaryEnum, List.length_map, diaryEnum_length]

noncomputable instance paperDiaryFintype (n : Nat) : Fintype (PaperDiary n) := by
  classical
  exact ⟨(paperDiaryEnum n).toFinset, fun D => List.mem_toFinset.mpr (paperDiaryEnum_complete D)⟩

/-- The manuscript's raw-set diary class has exactly the recurrence value,
for every n. The bijection and both local-rule translations are proved. -/
theorem paperDiary_card (n : Nat) : Fintype.card (PaperDiary n) = diaryCount true n 1 := by
  classical
  change (paperDiaryEnum n).toFinset.card = diaryCount true n 1
  rw [List.toFinset_card_of_nodup (paperDiaryEnum_nodup n), paperDiaryEnum_length]

end AllThoseBigRamsey.Pseudotree
