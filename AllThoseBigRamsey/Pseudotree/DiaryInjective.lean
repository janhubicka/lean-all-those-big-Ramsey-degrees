import AllThoseBigRamsey.Pseudotree.DiaryTrees

/-!
# Recovering diary events from literal ternary trees

The lemmas here reconstruct each event from the next literal frontier and
the current coding mark. They establish injectivity of literal execution;
no injectivity or inverse bridge is included as an assumption.
-/

namespace AllThoseBigRamsey.Pseudotree

/-- Count the nodes on the next level whose last letter is zero. -/
def zeroEnds (ws : List DiaryWord) : Nat :=
  (ws.filter (fun w => w.getLast? == some 0)).length

@[simp] theorem zeroEnds_map_two (ws : List DiaryWord) :
    zeroEnds (ws.map (fun w => child w 2)) = 0 := by
  induction ws <;> simp_all [zeroEnds, child]

theorem splitFrontier_zeroEnds (h : i < ws.length) :
    zeroEnds (splitFrontier i ws) = i + 1 := by
  induction ws generalizing i with
  | nil => simp at h
  | cons w ws ih =>
      cases i with
      | zero => simp [splitFrontier, zeroEnds, child]
      | succ i =>
          have hi : i < ws.length := by simpa using h
          simpa [splitFrontier, zeroEnds, child] using congrArg Nat.succ (ih hi)

theorem leafFrontier_zeroEnds (h : i < ws.length) :
    zeroEnds (leafFrontier i ws) = i := by
  induction ws generalizing i with
  | nil => simp at h
  | cons w ws ih =>
      cases i with
      | zero => exact zeroEnds_map_two ws
      | succ i =>
          have hi : i < ws.length := by simpa using h
          simpa [leafFrontier, zeroEnds, child] using congrArg Nat.succ (ih hi)

/-- Exactly the local part of width validity. -/
def DiaryEvent.legal (k : Nat) : DiaryEvent → Prop
  | .split i | .leaf i => i < k
  | .code | .turn => 0 < k

theorem DiaryEvent.legal_of_width (h : WidthValid k (e :: es)) : e.legal k := by
  cases e <;> exact h.1

/-- At a nonempty frontier, its successor and coding mark uniquely determine
the event and the addressed branch. -/
theorem DiaryEvent.step_metrics_injective (e f : DiaryEvent) (ws : List DiaryWord)
    (he : e.legal ws.length) (hf : f.legal ws.length)
    (hlength : (e.next ws).length = (f.next ws).length)
    (hzeros : zeroEnds (e.next ws) = zeroEnds (f.next ws))
    (hcodes : (e.coding ws).length = (f.coding ws).length) : e = f := by
  cases e with
  | split i =>
      cases f with
      | split j =>
          have hi := splitFrontier_zeroEnds he
          have hj := splitFrontier_zeroEnds hf
          simp only [DiaryEvent.next, hi, hj] at hzeros
          congr
          omega
      | leaf j =>
          simp only [DiaryEvent.next, splitFrontier_length he, leafFrontier_length hf] at hlength
          omega
      | code =>
          simp only [DiaryEvent.next, splitFrontier_length he, continueFrontier_length] at hlength
          omega
      | turn =>
          simp only [DiaryEvent.next, splitFrontier_length he, continueFrontier_length] at hlength
          omega
  | leaf i =>
      cases f with
      | split j =>
          simp only [DiaryEvent.next, leafFrontier_length he, splitFrontier_length hf] at hlength
          omega
      | leaf j =>
          have hi := leafFrontier_zeroEnds he
          have hj := leafFrontier_zeroEnds hf
          simp only [DiaryEvent.next, hi, hj] at hzeros
          congr
      | code =>
          simp only [DiaryEvent.next, leafFrontier_length he, continueFrontier_length] at hlength
          have hp : 0 < ws.length := hf
          omega
      | turn =>
          simp only [DiaryEvent.next, leafFrontier_length he, continueFrontier_length] at hlength
          have hp : 0 < ws.length := hf
          omega
  | code =>
      cases f with
      | split j =>
          simp only [DiaryEvent.next, continueFrontier_length, splitFrontier_length hf] at hlength
          omega
      | leaf j =>
          simp only [DiaryEvent.next, continueFrontier_length, leafFrontier_length hf] at hlength
          have hp : 0 < ws.length := he
          omega
      | code => rfl
      | turn =>
          cases ws with
          | nil => simp [DiaryEvent.legal] at he
          | cons w ws => simp [DiaryEvent.coding] at hcodes
  | turn =>
      cases f with
      | split j =>
          simp only [DiaryEvent.next, continueFrontier_length, splitFrontier_length hf] at hlength
          omega
      | leaf j =>
          simp only [DiaryEvent.next, continueFrontier_length, leafFrontier_length hf] at hlength
          have hp : 0 < ws.length := he
          omega
      | code =>
          cases ws with
          | nil => simp [DiaryEvent.legal] at hf
          | cons w ws => simp [DiaryEvent.coding] at hcodes
      | turn => rfl

theorem DiaryEvent.step_injective (e f : DiaryEvent) (ws : List DiaryWord)
    (he : e.legal ws.length) (hf : f.legal ws.length)
    (hnext : e.next ws = f.next ws) (hcode : e.coding ws = f.coding ws) : e = f :=
  e.step_metrics_injective f ws he hf (congrArg List.length hnext)
    (congrArg zeroEnds hnext) (congrArg List.length hcode)

theorem DiaryEvent.step_perm_injective (e f : DiaryEvent) (ws : List DiaryWord)
    (he : e.legal ws.length) (hf : f.legal ws.length)
    (hnext : (e.next ws).Perm (f.next ws))
    (hcode : (e.coding ws).Perm (f.coding ws)) : e = f :=
  e.step_metrics_injective f ws he hf hnext.length_eq
    ((hnext.filter (fun w : DiaryWord => w.getLast? == some 0)).length_eq) hcode.length_eq

/-- Filtering the executed node list at the input height recovers precisely
the input frontier, independently of the later events. -/
theorem execute_nodes_at_start (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) :
    (execute es ws).nodes.filter (fun w => w.length == h) = ws := by
  have hfilter : ws.filter (fun w => w.length == h) = ws :=
    List.filter_eq_self.mpr (fun w hw => by simp [hws w hw])
  cases es with
  | nil => exact hfilter
  | cons e es =>
      have hrest : (execute es (e.next ws)).nodes.filter (fun w => w.length == h) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro w hw heq
        have hlen := execute_length_ge es (e.next_lengths hws) hw
        simp only [beq_iff_eq] at heq
        omega
      simp only [execute, List.filter_append, hfilter, hrest, List.append_nil]

/-- Filtering coding nodes at the input height recovers the coding mark of
the first event. -/
theorem execute_codes_at_start (e : DiaryEvent) (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) :
    (execute (e :: es) ws).codes.filter (fun w => w.length == h) = e.coding ws := by
  have hfilter : (e.coding ws).filter (fun w => w.length == h) = e.coding ws :=
    List.filter_eq_self.mpr (fun w hw => by simp [hws w (e.coding_mem hw)])
  have hrest : (execute es (e.next ws)).codes.filter (fun w => w.length == h) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro w hw heq
    have hlen := execute_length_ge es (e.next_lengths hws) (execute_codes_nodes es hw)
    simp only [beq_iff_eq] at heq
    omega
  simp only [execute, List.filter_append, hfilter, hrest, List.append_nil]

theorem widthValid_zero (hv : WidthValid 0 es) : es = [] := by
  cases es with
  | nil => rfl
  | cons e es => cases e <;> simp [WidthValid] at hv

/-- A valid event sequence can be reconstructed uniquely from its actual
literal nodes and coding nodes. This holds at every uniform input level. -/
theorem execute_injective (es fs : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h)
    (he : WidthValid ws.length es) (hf : WidthValid ws.length fs)
    (hnodes : (execute es ws).nodes = (execute fs ws).nodes)
    (hcodes : (execute es ws).codes = (execute fs ws).codes) : es = fs := by
  induction es generalizing fs ws h with
  | nil =>
      have hz : ws.length = 0 := he
      exact (widthValid_zero (hz ▸ hf)).symm
  | cons e es ih =>
      cases fs with
      | nil =>
          have hz : ws.length = 0 := hf
          have he' := widthValid_zero (hz ▸ he)
          contradiction
      | cons f fs =>
          have hrest : (execute es (e.next ws)).nodes = (execute fs (f.next ws)).nodes :=
            List.append_cancel_left hnodes
          have hnext := congrArg (List.filter (fun w : DiaryWord => w.length == h + 1)) hrest
          rw [execute_nodes_at_start es (e.next_lengths hws),
            execute_nodes_at_start fs (f.next_lengths hws)] at hnext
          have hcode := congrArg (List.filter (fun w : DiaryWord => w.length == h)) hcodes
          rw [execute_codes_at_start e es hws, execute_codes_at_start f fs hws] at hcode
          have hef := e.step_injective f ws (e.legal_of_width he) (f.legal_of_width hf) hnext hcode
          subst f
          have htail : (execute es (e.next ws)).codes = (execute fs (e.next ws)).codes :=
            List.append_cancel_left hcodes
          exact congrArg (List.cons e) (ih fs (e.next_lengths hws)
            (e.next_width_valid he) (e.next_width_valid hf) hrest htail)

/-- Reordering the recorded nodes and codes also loses no event information.
The local event is recovered from permutation-invariant level statistics. -/
theorem execute_perm_injective (es fs : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h)
    (he : WidthValid ws.length es) (hf : WidthValid ws.length fs)
    (hnodes : (execute es ws).nodes.Perm (execute fs ws).nodes)
    (hcodes : (execute es ws).codes.Perm (execute fs ws).codes) : es = fs := by
  induction es generalizing fs ws h with
  | nil =>
      have hz : ws.length = 0 := he
      exact (widthValid_zero (hz ▸ hf)).symm
  | cons e es ih =>
      cases fs with
      | nil =>
          have hz : ws.length = 0 := hf
          have he' := widthValid_zero (hz ▸ he)
          contradiction
      | cons f fs =>
          have hrest : (execute es (e.next ws)).nodes.Perm (execute fs (f.next ws)).nodes :=
            (List.perm_append_left_iff ws).mp hnodes
          have hnext := hrest.filter (fun w : DiaryWord => w.length == h + 1)
          rw [execute_nodes_at_start es (e.next_lengths hws),
            execute_nodes_at_start fs (f.next_lengths hws)] at hnext
          have hcode := hcodes.filter (fun w : DiaryWord => w.length == h)
          rw [execute_codes_at_start e es hws, execute_codes_at_start f fs hws] at hcode
          have hef := e.step_perm_injective f ws
            (e.legal_of_width he) (f.legal_of_width hf) hnext hcode
          subst f
          have htail : (execute es (e.next ws)).codes.Perm (execute fs (e.next ws)).codes :=
            (List.perm_append_left_iff (e.coding ws)).mp hcodes
          exact congrArg (List.cons e) (ih fs (e.next_lengths hws)
            (e.next_width_valid he) (e.next_width_valid hf) hrest htail)

/-- Packaged grammar states never begin with a free type-(d) event. -/
theorem Diary.events_ne_turn (d : Diary left m k) (es : List DiaryEvent) :
    d.events ≠ .turn :: es := by
  intro h
  have ht := d.turns_legal false
  rw [h] at ht
  simp [TurnsLegal] at ht

theorem Diary.optional_turn_injective (d e : Diary left m k) (b c : Bool)
    (he : (if b then [.turn] else []) ++ d.events =
      (if c then [.turn] else []) ++ e.events) : b = c ∧ d.events = e.events := by
  cases b <;> cases c
  · exact ⟨rfl, he⟩
  · exact False.elim (d.events_ne_turn e.events he)
  · exact False.elim (e.events_ne_turn d.events he.symm)
  · exact ⟨rfl, (List.cons.inj he).2⟩

/-- Expanding the optional type-(d) event loses no grammar information. -/
theorem Diary.events_injective (d e : Diary left m k) (he : d.events = e.events) : d = e := by
  induction d with
  | done left => cases e <;> simp_all [events]
  | splitClosed i d ih =>
      cases e <;> simp_all [events]
      exact ⟨Fin.ext he.1, ih _ rfl⟩
  | leafClosed i d ih =>
      cases e <;> simp_all [events]
      exact ⟨Fin.ext he.1, ih _ rfl⟩
  | splitOpen i turn d ih =>
      cases e <;> simp_all [events]
      obtain ⟨hb, ht⟩ := optional_turn_injective d _ turn _ he.2
      exact ⟨Fin.ext he.1, hb, ih _ ht⟩
  | endLeft d ih =>
      cases e <;> simp_all [events]
      exact ih _ rfl
  | leafRight i turn d ih =>
      cases e <;> simp_all [events]
      obtain ⟨hb, ht⟩ := optional_turn_injective d _ turn _ he.2
      exact ⟨Fin.ext he.1, hb, ih _ ht⟩
  | continueLeft d ih =>
      cases e <;> simp_all [events]
      exact ih _ rfl

/-- A literal ternary tree and coding-node set determine their event diary
uniquely, for every size. Both equalities are extensional set equalities. -/
theorem Diary.toTree_ext_injective (d e : Diary true n 1)
    (hnodes : ∀ w, w ∈ d.toTree.nodes ↔ w ∈ e.toTree.nodes)
    (hcodes : ∀ w, w ∈ d.toTree.codes ↔ w ∈ e.toTree.codes) : d = e := by
  apply d.events_injective e
  exact execute_perm_injective d.events e.events (h := 0) (by simp)
    (by simpa using d.width_valid) (by simpa using e.width_valid)
    ((List.perm_ext_iff_of_nodup d.toTree_nodes_nodup e.toTree_nodes_nodup).mpr hnodes)
    ((List.perm_ext_iff_of_nodup d.toTree_codes_nodup e.toTree_codes_nodup).mpr hcodes)

/-- Coding sets alone determine the entire diary: the literal node set is
their prefix closure, already proved independently in `DiaryTrees`. -/
theorem Diary.toTree_codes_ext_injective (d e : Diary true n 1)
    (hcodes : ∀ w, w ∈ d.toTree.codes ↔ w ∈ e.toTree.codes) : d = e := by
  apply d.toTree_ext_injective e _ hcodes
  intro w
  rw [d.toTree_nodes_iff_prefix_code, e.toTree_nodes_iff_prefix_code]
  constructor <;> rintro ⟨c, hc, tail, ht⟩
  · exact ⟨c, (hcodes c).mp hc, tail, ht⟩
  · exact ⟨c, (hcodes c).mpr hc, tail, ht⟩

theorem Diary.toTree_codes_injective (d e : Diary true n 1)
    (hcodes : d.toTree.codes = e.toTree.codes) : d = e :=
  d.toTree_codes_ext_injective e (by intro w; rw [hcodes])

theorem Diary.toTree_injective (d e : Diary true n 1) (h : d.toTree = e.toTree) : d = e :=
  d.toTree_codes_injective e (congrArg DiaryTree.codes h)

/-- All sizes, rather than a bounded computation: distinct grammar diaries
give distinct actual coding-node lists. -/
theorem literalCodes_nodup (n : Nat) :
    ((diaryEnum true n 1).map (fun d => d.toTree.codes)).Nodup :=
  diaryMap_nodup _ _ (diaryEnum_nodup true n 1) Diary.toTree_codes_injective

/-- The recurrence counts pairwise distinct literal outputs, for every n.
Surjectivity onto an independently specified literal-tree class is a
separate statement and is not asserted by this theorem. -/
theorem literalCodes_length (n : Nat) :
    ((diaryEnum true n 1).map (fun d => d.toTree.codes)).length = diaryCount true n 1 := by
  simp only [List.length_map, diaryEnum_length]

end AllThoseBigRamsey.Pseudotree
