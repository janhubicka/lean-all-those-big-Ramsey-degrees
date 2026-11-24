import AllThoseBigRamsey.Pseudotree.DiaryCounts

/-!
# Executing event diaries as finite ternary trees

The grammar in `DiaryCounts` is interpreted here as literal finite words over
`Fin 3`, with a node list and a coding-node list. The implementation follows
the manuscript's left-to-right rule: noncritical branches receive 0 before
the critical branch and 2 after it. This file proves structural properties
of this interpretation; it does not identify arbitrary literal paper diaries
with the grammar by assuming a bijection.
-/
namespace AllThoseBigRamsey.Pseudotree

abbrev DiaryWord := List (Fin 3)

inductive DiaryEvent
  | split (index : Nat)
  | leaf (index : Nat)
  | code
  | turn
  deriving DecidableEq, Repr

/-- The actual single-level events, with packaged type-(d) levels expanded. -/
def Diary.events : Diary left m k → List DiaryEvent
  | .done _ => []
  | .splitClosed i d => .split i.val :: d.events
  | .leafClosed i d => .leaf i.val :: d.events
  | .splitOpen i turn d => .split i.val :: (if turn then [.turn] else []) ++ d.events
  | .endLeft d => .leaf 0 :: d.events
  | .leafRight i turn d => .leaf (i.val + 1) :: (if turn then [.turn] else []) ++ d.events
  | .continueLeft d => .code :: d.events

/-- Exactly the coding events. -/
def DiaryEvent.isCode : DiaryEvent → Bool
  | .leaf _ | .code => true
  | .split _ | .turn => false

/-- The expanded trace has exactly the claimed number of levels. -/
theorem Diary.events_length (d : Diary left m k) : d.events.length = d.levels := by
  induction d <;> simp_all [events, levels] <;> split <;> simp_all <;> omega

/-- Exactly `m` coding levels occur in an event diary. -/
theorem Diary.events_codes (d : Diary left m k) :
    (d.events.filter DiaryEvent.isCode).length = m := by
  induction d <;> simp_all [events, List.filter_cons, DiaryEvent.isCode] <;> split <;> simp_all

/-- Turn legality from the immediately preceding level: a turn is permitted
only after a split or leaf. In particular it is forbidden initially. -/
def TurnsLegal (allowed : Bool) : List DiaryEvent → Prop
  | [] => True
  | .split _ :: es | .leaf _ :: es => TurnsLegal true es
  | .code :: es => TurnsLegal false es
  | .turn :: es => allowed = true ∧ TurnsLegal false es

/-- Type-(d) levels are never initial and never follow type-(c) or type-(d). -/
theorem Diary.turns_legal (d : Diary left m k) (allowed : Bool) :
    TurnsLegal allowed d.events := by
  induction d generalizing allowed <;> simp_all [events, TurnsLegal] <;>
    split <;> simp_all [TurnsLegal]

/-- Width and legal-index conditions for a completely executed event trace. -/
def WidthValid (k : Nat) : List DiaryEvent → Prop
  | [] => k = 0
  | .split i :: es => i < k ∧ WidthValid (k + 1) es
  | .leaf i :: es => i < k ∧ WidthValid (k - 1) es
  | .code :: es | .turn :: es => 0 < k ∧ WidthValid k es

/-- Every event addresses an existing branch, and execution ends with no branch. -/
theorem Diary.width_valid (d : Diary left m k) : WidthValid k d.events := by
  induction d with
  | done => simp [events, WidthValid]
  | splitClosed i d ih => simp [events, WidthValid, i.isLt, ih]
  | leafClosed i d ih => simp [events, WidthValid, i.isLt, ih]
  | splitOpen i turn d ih =>
      cases turn <;> simp [events, WidthValid, i.isLt, ih]
  | endLeft d ih => simp [events, WidthValid, ih]
  | leafRight i turn d ih =>
      have hi := i.isLt
      have hk : 0 < _ := Nat.zero_lt_of_lt hi
      cases turn <;> simp [events, WidthValid, ih] <;> omega
  | continueLeft d ih => simp [events, WidthValid, ih]

/-- Append one actual ternary letter. -/
def child (w : DiaryWord) (a : Fin 3) : DiaryWord := w ++ [a]

/-- At a splitting level, preceding branches take 0 and following branches take 2. -/
def splitFrontier : Nat → List DiaryWord → List DiaryWord
  | _, [] => []
  | 0, w :: ws => child w 0 :: child w 2 :: ws.map (fun v => child v 2)
  | i + 1, w :: ws => child w 0 :: splitFrontier i ws

/-- At a coding leaf, remove the critical branch. -/
def leafFrontier : Nat → List DiaryWord → List DiaryWord
  | _, [] => []
  | 0, _ :: ws => ws.map (fun v => child v 2)
  | i + 1, w :: ws => child w 0 :: leafFrontier i ws

/-- Both continuation types act on the original leftmost active branch. -/
def continueFrontier : List DiaryWord → List DiaryWord
  | [] => []
  | w :: ws => child w 1 :: ws.map (fun v => child v 2)

def DiaryEvent.next : DiaryEvent → List DiaryWord → List DiaryWord
  | .split i, ws => splitFrontier i ws
  | .leaf i, ws => leafFrontier i ws
  | .code, ws | .turn, ws => continueFrontier ws

def DiaryEvent.coding : DiaryEvent → List DiaryWord → List DiaryWord
  | .leaf i, ws => (ws[i]?).toList
  | .code, ws => ws.head?.toList
  | .split _, _ | .turn, _ => []

structure DiaryTree where
  nodes : List DiaryWord
  codes : List DiaryWord
  deriving Repr

/-- Literal execution; all words on every level are retained. -/
def execute : List DiaryEvent → List DiaryWord → DiaryTree
  | [], ws => ⟨ws, []⟩
  | e :: es, ws =>
      let rest := execute es (e.next ws)
      ⟨ws ++ rest.nodes, e.coding ws ++ rest.codes⟩

/-- The finite ternary tree and coding set associated with an event diary. -/
def Diary.toTree (d : Diary true n 1) : DiaryTree := execute d.events [[]]

@[simp] theorem splitFrontier_length (h : i < ws.length) :
    (splitFrontier i ws).length = ws.length + 1 := by
  induction ws generalizing i with
  | nil => simp at h
  | cons w ws ih =>
      cases i with
      | zero => simp [splitFrontier]
      | succ i =>
          have hi : i < ws.length := by simpa using h
          simp [splitFrontier, ih hi]

@[simp] theorem leafFrontier_length (h : i < ws.length) :
    (leafFrontier i ws).length = ws.length - 1 := by
  induction ws generalizing i with
  | nil => simp at h
  | cons w ws ih =>
      cases i with
      | zero => simp [leafFrontier]
      | succ i =>
          have hi : i < ws.length := by simpa using h
          simp [leafFrontier, ih hi]
          omega

@[simp] theorem continueFrontier_length (ws : List DiaryWord) :
    (continueFrontier ws).length = ws.length := by cases ws <;> simp [continueFrontier]

/-- Every successor word is obtained by adding one letter to a current word. -/
theorem splitFrontier_parent (v : DiaryWord) (hv : v ∈ splitFrontier i ws) :
    ∃ w ∈ ws, ∃ a : Fin 3, v = child w a := by
  induction ws generalizing i with
  | nil => simp [splitFrontier] at hv
  | cons w ws ih =>
      cases i with
      | zero =>
          simp only [splitFrontier, List.mem_cons] at hv
          rcases hv with rfl | rfl | hv
          · exact ⟨w, by simp, 0, rfl⟩
          · exact ⟨w, by simp, 2, rfl⟩
          · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
            exact ⟨u, by simp [hu], 2, rfl⟩
      | succ i =>
          simp only [splitFrontier, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact ⟨w, by simp, 0, rfl⟩
          · obtain ⟨u, hu, a, ha⟩ := ih hv
            exact ⟨u, by simp [hu], a, ha⟩

theorem leafFrontier_parent (v : DiaryWord) (hv : v ∈ leafFrontier i ws) :
    ∃ w ∈ ws, ∃ a : Fin 3, v = child w a := by
  induction ws generalizing i with
  | nil => simp [leafFrontier] at hv
  | cons w ws ih =>
      cases i with
      | zero =>
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
          exact ⟨u, by simp [hu], 2, rfl⟩
      | succ i =>
          simp only [leafFrontier, List.mem_cons] at hv
          rcases hv with rfl | hv
          · exact ⟨w, by simp, 0, rfl⟩
          · obtain ⟨u, hu, a, ha⟩ := ih hv
            exact ⟨u, by simp [hu], a, ha⟩

theorem continueFrontier_parent (v : DiaryWord) (hv : v ∈ continueFrontier ws) :
    ∃ w ∈ ws, ∃ a : Fin 3, v = child w a := by
  cases ws with
  | nil => simp [continueFrontier] at hv
  | cons w ws =>
      simp only [continueFrontier, List.mem_cons] at hv
      rcases hv with rfl | hv
      · exact ⟨w, by simp, 1, rfl⟩
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
        exact ⟨u, by simp [hu], 2, rfl⟩

theorem DiaryEvent.next_parent (e : DiaryEvent) (hv : v ∈ e.next ws) :
    ∃ w ∈ ws, ∃ a : Fin 3, v = child w a := by
  cases e with
  | split i => exact splitFrontier_parent _ hv
  | leaf i => exact leafFrontier_parent _ hv
  | code => exact continueFrontier_parent _ hv
  | turn => exact continueFrontier_parent _ hv

/-- Current frontier words occur in the executed node list. -/
theorem execute_frontier (es : List DiaryEvent) (hw : w ∈ ws) :
    w ∈ (execute es ws).nodes := by cases es <;> simp [execute, hw]

/-- Coding nodes are always actual nodes on the current frontier. -/
theorem DiaryEvent.coding_mem (e : DiaryEvent) (hw : w ∈ e.coding ws) : w ∈ ws := by
  cases e with
  | split => simp [coding] at hw
  | turn => simp [coding] at hw
  | leaf i => exact List.mem_of_getElem? (by simpa [coding] using hw)
  | code => exact List.mem_of_head? (by simpa [coding] using hw)

/-- Every coding node belongs to the constructed literal ternary tree. -/
theorem execute_codes_nodes (es : List DiaryEvent) (hw : w ∈ (execute es ws).codes) :
    w ∈ (execute es ws).nodes := by
  induction es generalizing ws with
  | nil => simp [execute] at hw
  | cons e es ih =>
      simp only [execute, List.mem_append] at hw ⊢
      rcases hw with hw | hw
      · exact Or.inl (e.coding_mem hw)
      · exact Or.inr (ih hw)

/-- Every constructed node extends an input frontier word. -/
theorem execute_ancestor (es : List DiaryEvent) (hv : v ∈ (execute es ws).nodes) :
    ∃ w ∈ ws, ∃ tail, v = w ++ tail := by
  induction es generalizing ws with
  | nil => exact ⟨v, hv, [], by simp⟩
  | cons e es ih =>
      simp only [execute, List.mem_append] at hv
      rcases hv with hv | hv
      · exact ⟨v, hv, [], by simp⟩
      · obtain ⟨u, hu, tail, rfl⟩ := ih hv
        obtain ⟨w, hw, a, rfl⟩ := e.next_parent hu
        exact ⟨w, hw, [a] ++ tail, by simp [child, List.append_assoc]⟩

theorem DiaryEvent.next_lengths (e : DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) :
    ∀ v ∈ e.next ws, v.length = h + 1 := by
  intro v hv
  obtain ⟨w, hw, a, rfl⟩ := e.next_parent hv
  simp [child, hws w hw]

/-- The execution cannot introduce a node shorter than the input frontier. -/
theorem execute_length_ge (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) (hv : v ∈ (execute es ws).nodes) :
    h ≤ v.length := by
  obtain ⟨w, hw, tail, rfl⟩ := execute_ancestor es hv
  simp [hws w hw]

/-- All prefixes down to the input level occur in the executed node list. -/
theorem execute_prefix (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) (hv : v ∈ (execute es ws).nodes)
    (hlo : h ≤ j) (hhi : j ≤ v.length) : v.take j ∈ (execute es ws).nodes := by
  induction es generalizing ws h with
  | nil =>
      have heq : j = v.length := by have := hws v hv; omega
      simpa [heq] using hv
  | cons e es ih =>
      by_cases hj : j = h
      · obtain ⟨w, hw, tail, rfl⟩ := execute_ancestor (e :: es) hv
        have hp : (w ++ tail).take j = w := by
          rw [hj, ← hws w hw]
          simp
        rw [hp]
        exact execute_frontier (e :: es) hw
      · simp only [execute, List.mem_append] at hv ⊢
        rcases hv with hv | hv
        · have := hws v hv
          omega
        · exact Or.inr (ih (e.next_lengths hws) hv (by omega))

/-- Literal prefix closure of every interpreted size-`n` diary. -/
theorem Diary.toTree_prefix_closed (d : Diary true n 1)
    (hv : v ∈ d.toTree.nodes) (hj : j ≤ v.length) : v.take j ∈ d.toTree.nodes := by
  exact execute_prefix d.events (by simp) hv (Nat.zero_le j) hj

/-- Recover the parent and final letter from a child word. -/
theorem child_injective {w u : DiaryWord} {a b : Fin 3} :
    child w a = child u b ↔ w = u ∧ a = b := by
  constructor
  · intro h
    have hr := congrArg List.reverse h
    simp [child] at hr
    exact ⟨hr.2, hr.1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem splitFrontier_nodup (hws : ws.Nodup) : (splitFrontier i ws).Nodup := by
  induction ws generalizing i with
  | nil => simp [splitFrontier]
  | cons w ws ih =>
      obtain ⟨hn, ht⟩ := List.nodup_cons.mp hws
      cases i with
      | zero =>
          have hm := diaryMap_nodup ws (fun v => child v 2) ht
            (by intro a b h; exact (child_injective.mp h).1)
          simp only [splitFrontier, List.nodup_cons, hm, and_true, List.mem_cons]
          simp [child_injective, List.mem_map]
          grind
      | succ i =>
          simp only [splitFrontier, List.nodup_cons, ih ht, and_true]
          intro hw
          obtain ⟨u, hu, a, ha⟩ := splitFrontier_parent _ hw
          have heq := (child_injective.mp ha).1
          exact hn (heq ▸ hu)

theorem leafFrontier_nodup (hws : ws.Nodup) : (leafFrontier i ws).Nodup := by
  induction ws generalizing i with
  | nil => simp [leafFrontier]
  | cons w ws ih =>
      obtain ⟨hn, ht⟩ := List.nodup_cons.mp hws
      cases i with
      | zero =>
          exact diaryMap_nodup ws (fun v => child v 2) ht
            (by intro a b h; exact (child_injective.mp h).1)
      | succ i =>
          simp only [leafFrontier, List.nodup_cons, ih ht, and_true]
          intro hw
          obtain ⟨u, hu, a, ha⟩ := leafFrontier_parent _ hw
          have heq := (child_injective.mp ha).1
          exact hn (heq ▸ hu)

theorem continueFrontier_nodup (hws : ws.Nodup) : (continueFrontier ws).Nodup := by
  cases ws with
  | nil => simp [continueFrontier]
  | cons w ws =>
      obtain ⟨hn, ht⟩ := List.nodup_cons.mp hws
      have hm := diaryMap_nodup ws (fun v => child v 2) ht
        (by intro a b h; exact (child_injective.mp h).1)
      simp only [continueFrontier, List.nodup_cons, hm, and_true]
      simp [List.mem_map, child_injective]

theorem DiaryEvent.next_nodup (e : DiaryEvent) (hws : ws.Nodup) :
    (e.next ws).Nodup := by
  cases e with
  | split => exact splitFrontier_nodup hws
  | leaf => exact leafFrontier_nodup hws
  | code => exact continueFrontier_nodup hws
  | turn => exact continueFrontier_nodup hws

/-- Distinct levels and injective child coding prevent duplicate tree nodes. -/
theorem execute_nodes_nodup (es : List DiaryEvent) (hn : ws.Nodup)
    (hws : ∀ w ∈ ws, w.length = h) : (execute es ws).nodes.Nodup := by
  induction es generalizing ws h with
  | nil => exact hn
  | cons e es ih =>
      apply List.nodup_append.mpr
      refine ⟨hn, ih (e.next_nodup hn) (e.next_lengths hws), ?_⟩
      intro a ha b hb heq
      have hla := hws a ha
      have hlb := execute_length_ge es (e.next_lengths hws) hb
      subst b
      omega

/-- The literal node list is a genuine finite set (with no repetitions). -/
theorem Diary.toTree_nodes_nodup (d : Diary true n 1) : d.toTree.nodes.Nodup :=
  execute_nodes_nodup (h := 0) d.events (by simp) (by simp)

theorem DiaryEvent.coding_nodup (e : DiaryEvent) (ws : List DiaryWord) :
    (e.coding ws).Nodup := by
  have option_nodup (o : Option DiaryWord) : o.toList.Nodup := by cases o <;> simp
  cases e with
  | split => simp [coding]
  | turn => simp [coding]
  | leaf i => exact option_nodup (ws[i]?)
  | code => exact option_nodup ws.head?

/-- Coding levels are distinct, so their node list also has no repetitions. -/
theorem execute_codes_nodup (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) : (execute es ws).codes.Nodup := by
  induction es generalizing ws h with
  | nil => simp [execute]
  | cons e es ih =>
      apply List.nodup_append.mpr
      refine ⟨e.coding_nodup ws, ih (e.next_lengths hws), ?_⟩
      intro a ha b hb heq
      have hla := hws a (e.coding_mem ha)
      have hlb := execute_length_ge es (e.next_lengths hws) (execute_codes_nodes es hb)
      subst b
      omega

theorem Diary.toTree_codes_nodup (d : Diary true n 1) : d.toTree.codes.Nodup :=
  execute_codes_nodup (h := 0) d.events (by simp)

/-- Executing a valid trace creates one coding node for each coding event. -/
theorem execute_code_count (es : List DiaryEvent) (hv : WidthValid ws.length es) :
    (execute es ws).codes.length = (es.filter DiaryEvent.isCode).length := by
  induction es generalizing ws with
  | nil => simp [execute]
  | cons e es ih =>
      cases e with
      | split i =>
          obtain ⟨hi, ht⟩ := hv
          have hnext : WidthValid ((DiaryEvent.split i).next ws).length es := by
            simpa [DiaryEvent.next, splitFrontier_length hi] using ht
          simp [execute, DiaryEvent.coding, DiaryEvent.isCode, ih hnext]
      | leaf i =>
          obtain ⟨hi, ht⟩ := hv
          have hnext : WidthValid ((DiaryEvent.leaf i).next ws).length es := by
            simpa [DiaryEvent.next, leafFrontier_length hi] using ht
          simp [execute, DiaryEvent.coding, List.filter_cons, DiaryEvent.isCode,
            List.getElem?_eq_getElem hi, ih hnext]
      | code =>
          cases ws with
          | nil => simp [WidthValid] at hv
          | cons w ws =>
              have hnext : WidthValid ((DiaryEvent.code).next (w :: ws)).length es := by
                simpa [DiaryEvent.next] using hv.2
              simp [execute, DiaryEvent.coding, List.filter_cons, DiaryEvent.isCode, ih hnext]
      | turn =>
          have hnext : WidthValid ((DiaryEvent.turn).next ws).length es := by
            simpa [DiaryEvent.next] using hv.2
          simp [execute, DiaryEvent.coding, DiaryEvent.isCode, ih hnext]

/-- The constructed literal tree has exactly `n` distinct coding nodes. -/
theorem Diary.toTree_coding_count (d : Diary true n 1) : d.toTree.codes.length = n := by
  rw [toTree, execute_code_count d.events (by simpa using d.width_valid), d.events_codes]

/-- No split level introduces a 1-edge. -/
theorem splitFrontier_no_one (w : DiaryWord) : child w 1 ∉ splitFrontier i ws := by
  induction ws generalizing i with
  | nil => simp [splitFrontier]
  | cons u ws ih =>
      cases i <;> simp [splitFrontier, List.mem_map, child_injective, ih]

/-- No leaf level introduces a 1-edge. -/
theorem leafFrontier_no_one (w : DiaryWord) : child w 1 ∉ leafFrontier i ws := by
  induction ws generalizing i with
  | nil => simp [leafFrontier]
  | cons u ws ih =>
      cases i <;> simp [leafFrontier, List.mem_map, child_injective, ih]

/-- A continuation introduces exactly the 1-edge from its first branch. -/
theorem continueFrontier_one (w : DiaryWord) :
    child w 1 ∈ continueFrontier ws ↔ ws.head? = some w := by
  cases ws <;> simp [continueFrontier, List.mem_map, child_injective, eq_comm]

/-- At most one branch takes the letter 1 at any transition. -/
theorem DiaryEvent.next_one (e : DiaryEvent)
    (ha : child a 1 ∈ e.next ws) (hb : child b 1 ∈ e.next ws) : a = b := by
  cases e with
  | split i => exact False.elim (splitFrontier_no_one a ha)
  | leaf i => exact False.elim (leafFrontier_no_one a ha)
  | code =>
      have ha' := continueFrontier_one a |>.mp ha
      have hb' := continueFrontier_one b |>.mp hb
      exact Option.some.inj (ha'.symm.trans hb')
  | turn =>
      have ha' := continueFrontier_one a |>.mp ha
      have hb' := continueFrontier_one b |>.mp hb
      exact Option.some.inj (ha'.symm.trans hb')

/-- The restricted Milliken shape condition, propagated through execution. -/
theorem execute_one_per_level (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h)
    (hone : ∀ a b, child a 1 ∈ ws → child b 1 ∈ ws → a = b)
    (ha : child a 1 ∈ (execute es ws).nodes)
    (hb : child b 1 ∈ (execute es ws).nodes)
    (hlen : a.length = b.length) : a = b := by
  induction es generalizing ws h with
  | nil => exact hone a b ha hb
  | cons e es ih =>
      simp only [execute, List.mem_append] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact hone a b ha hb
      · have hla := hws _ ha
        have hlb := execute_length_ge es (e.next_lengths hws) hb
        simp only [child, List.length_append, List.length_singleton] at hla hlb
        omega
      · have hla := execute_length_ge es (e.next_lengths hws) ha
        have hlb := hws _ hb
        simp only [child, List.length_append, List.length_singleton] at hla hlb
        omega
      · exact ih (e.next_lengths hws) (fun _ _ => e.next_one) ha hb

/-- The interpreted tree has at most one word ending in 1 at every level. -/
theorem Diary.toTree_one_per_level (d : Diary true n 1)
    (ha : child a 1 ∈ d.toTree.nodes) (hb : child b 1 ∈ d.toTree.nodes)
    (hlen : a.length = b.length) : a = b := by
  exact execute_one_per_level (h := 0) d.events (by simp)
    (by intro a b ha; simp [child] at ha) ha hb hlen

/-- The live original branch is removed by precisely a leaf at index zero. -/
def LeftValid (left : Bool) : List DiaryEvent → Prop
  | [] => True
  | .split _ :: es => LeftValid left es
  | .leaf i :: es => LeftValid (if i = 0 then false else left) es
  | .code :: es | .turn :: es => left = true ∧ LeftValid left es

/-- Continuation events occur only while the original leftmost branch is live. -/
theorem Diary.left_valid (d : Diary left m k) : LeftValid left d.events := by
  induction d with
  | done => simp [events, LeftValid]
  | splitClosed i d ih => simpa [events, LeftValid] using ih
  | leafClosed i d ih => simpa [events, LeftValid] using ih
  | splitOpen i turn d ih => cases turn <;> simp [events, LeftValid, ih]
  | endLeft d ih => simpa [events, LeftValid] using ih
  | leafRight i turn d ih => cases turn <;> simp [events, LeftValid, ih]
  | continueLeft d ih => simp [events, LeftValid, ih]

/-- Every branch at a split has a successor. -/
theorem splitFrontier_covers (hw : w ∈ ws) :
    ∃ a : Fin 3, child w a ∈ splitFrontier i ws := by
  induction ws generalizing i with
  | nil => simp at hw
  | cons u ws ih =>
      rcases List.mem_cons.mp hw with rfl | hw
      · cases i <;> exact ⟨0, by simp [splitFrontier]⟩
      · cases i with
        | zero => exact ⟨2, by simp [splitFrontier, List.mem_map, child_injective, hw]⟩
        | succ i =>
            obtain ⟨a, ha⟩ := ih (i := i) hw
            exact ⟨a, by simp [splitFrontier, ha]⟩

/-- At a leaf, exactly the deleted branch is recorded as a coding node. -/
theorem leafFrontier_covers (hw : w ∈ ws) :
    w ∈ (ws[i]?).toList ∨ ∃ a : Fin 3, child w a ∈ leafFrontier i ws := by
  induction ws generalizing i with
  | nil => simp at hw
  | cons u ws ih =>
      rcases List.mem_cons.mp hw with rfl | hw
      · cases i with
        | zero => exact Or.inl (by simp)
        | succ i => exact Or.inr ⟨0, by simp [leafFrontier]⟩
      · cases i with
        | zero => exact Or.inr ⟨2, by simp [leafFrontier, List.mem_map, child_injective, hw]⟩
        | succ i =>
            rcases ih (i := i) hw with hc | ⟨a, ha⟩
            · exact Or.inl (by simpa using hc)
            · exact Or.inr ⟨a, by simp [leafFrontier, ha]⟩

theorem continueFrontier_covers (hw : w ∈ ws) :
    ∃ a : Fin 3, child w a ∈ continueFrontier ws := by
  cases ws with
  | nil => simp at hw
  | cons u ws =>
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨1, by simp [continueFrontier]⟩
      · exact ⟨2, by simp [continueFrontier, List.mem_map, child_injective, hw]⟩

/-- No branch disappears without being made a coding node. -/
theorem DiaryEvent.covers (e : DiaryEvent) (hw : w ∈ ws) :
    w ∈ e.coding ws ∨ ∃ a : Fin 3, child w a ∈ e.next ws := by
  cases e with
  | split i => exact Or.inr (splitFrontier_covers hw)
  | leaf i => exact leafFrontier_covers hw
  | code => exact Or.inr (continueFrontier_covers hw)
  | turn => exact Or.inr (continueFrontier_covers hw)

theorem DiaryEvent.next_width_valid (e : DiaryEvent)
    (hv : WidthValid ws.length (e :: es)) : WidthValid (e.next ws).length es := by
  cases e with
  | split i => simpa [next, splitFrontier_length hv.1] using hv.2
  | leaf i => simpa [next, leafFrontier_length hv.1] using hv.2
  | code => simpa [next] using hv.2
  | turn => simpa [next] using hv.2

/-- Every initial branch has a later coding descendant. -/
theorem execute_frontier_coded (es : List DiaryEvent)
    (hv : WidthValid ws.length es) (hw : w ∈ ws) :
    ∃ c ∈ (execute es ws).codes, ∃ tail, c = w ++ tail := by
  induction es generalizing ws w with
  | nil =>
      have he : ws = [] := List.eq_nil_of_length_eq_zero hv
      simp [he] at hw
  | cons e es ih =>
      rcases e.covers hw with hc | ⟨a, ha⟩
      · exact ⟨w, by simp [execute, hc], [], by simp⟩
      · obtain ⟨c, hc, tail, htail⟩ := ih (e.next_width_valid hv) ha
        exact ⟨c, by simp [execute, hc], [a] ++ tail,
          by simpa [child, List.append_assoc] using htail⟩

/-- Every constructed node is a prefix of one of its coding nodes. -/
theorem execute_nodes_coded (es : List DiaryEvent)
    (hv : WidthValid ws.length es) (hw : w ∈ (execute es ws).nodes) :
    ∃ c ∈ (execute es ws).codes, ∃ tail, c = w ++ tail := by
  induction es generalizing ws with
  | nil => exact execute_frontier_coded [] hv hw
  | cons e es ih =>
      simp only [execute, List.mem_append] at hw
      rcases hw with hw | hw
      · exact execute_frontier_coded (e :: es) hv hw
      · obtain ⟨c, hc, tail, ht⟩ := ih (e.next_width_valid hv) hw
        exact ⟨c, by simp [execute, hc], tail, ht⟩

/-- The actual node set is precisely the prefix closure of the coding set. -/
theorem Diary.toTree_nodes_iff_prefix_code (d : Diary true n 1) (w : DiaryWord) :
    w ∈ d.toTree.nodes ↔ ∃ c ∈ d.toTree.codes, ∃ tail, c = w ++ tail := by
  constructor
  · exact execute_nodes_coded d.events (by simpa using d.width_valid)
  · rintro ⟨c, hc, tail, rfl⟩
    have hp := d.toTree_prefix_closed (v := w ++ tail)
      (execute_codes_nodes d.events hc) (j := w.length) (by simp)
    simpa using hp

/-- Only the original leftmost branch has never taken the letter 2. -/
def OriginalFrontier (left : Bool) : List DiaryWord → Prop
  | [] => True
  | w :: ws => (2 ∉ w ↔ left = true) ∧ OriginalFrontier false ws

@[simp] theorem originalFrontier_map_two (ws : List DiaryWord) :
    OriginalFrontier false (ws.map (fun w => child w 2)) := by
  induction ws <;> simp_all [OriginalFrontier, child]

theorem splitFrontier_original (ho : OriginalFrontier left ws) :
    OriginalFrontier left (splitFrontier i ws) := by
  induction ws generalizing i left with
  | nil => simp [splitFrontier, OriginalFrontier]
  | cons w ws ih =>
      obtain ⟨hw, ht⟩ := ho
      cases i with
      | zero =>
          simp [splitFrontier, OriginalFrontier, child, hw]
          simpa [child] using originalFrontier_map_two ws
      | succ i =>
          simp only [splitFrontier, OriginalFrontier, child, List.mem_append,
            List.mem_singleton, or_false, show (2 : Fin 3) ≠ 0 by decide]
          exact ⟨hw, ih ht⟩

theorem leafFrontier_original (ho : OriginalFrontier left ws) :
    OriginalFrontier (if i = 0 then false else left) (leafFrontier i ws) := by
  induction ws generalizing i left with
  | nil => simp [leafFrontier, OriginalFrontier]
  | cons w ws ih =>
      obtain ⟨hw, ht⟩ := ho
      cases i with
      | zero => exact originalFrontier_map_two ws
      | succ i =>
          simp only [Nat.succ_ne_zero, ↓reduceIte,
            leafFrontier, OriginalFrontier, child, List.mem_append, List.mem_singleton,
            show (2 : Fin 3) ≠ 0 by decide, or_false]
          refine ⟨hw, ?_⟩
          simpa using ih (i := i) ht

theorem continueFrontier_original (ho : OriginalFrontier left ws) :
    OriginalFrontier left (continueFrontier ws) := by
  cases ws with
  | nil => simp [continueFrontier, OriginalFrontier]
  | cons w ws =>
      obtain ⟨hw, _⟩ := ho
      simp [continueFrontier, OriginalFrontier, child, hw]
      simpa [child] using originalFrontier_map_two ws

def DiaryEvent.nextLeft (left : Bool) : DiaryEvent → Bool
  | .leaf i => if i = 0 then false else left
  | _ => left

theorem DiaryEvent.next_original (e : DiaryEvent) (ho : OriginalFrontier left ws) :
    OriginalFrontier (e.nextLeft left) (e.next ws) := by
  cases e with
  | split => exact splitFrontier_original ho
  | leaf => exact leafFrontier_original ho
  | code => exact continueFrontier_original ho
  | turn => exact continueFrontier_original ho

/-- Critical nodes of the two continuation types. -/
def continuationNodes : List DiaryEvent → List DiaryWord → List DiaryWord
  | [], _ => []
  | e :: es, ws =>
      (match e with
        | .code | .turn => ws.head?.toList
        | _ => []) ++ continuationNodes es (e.next ws)

theorem originalFrontier_head (ho : OriginalFrontier true ws) (hw : w ∈ ws.head?.toList) :
    2 ∉ w := by
  cases ws with
  | nil => simp at hw
  | cons u ws =>
      have he : w = u := by simpa using hw
      subst w
      exact ho.1.mpr rfl

/-- Continuation critical nodes are literal words over {0,1}. -/
theorem continuationNodes_original (es : List DiaryEvent)
    (hl : LeftValid left es) (ho : OriginalFrontier left ws)
    (hw : w ∈ continuationNodes es ws) : 2 ∉ w := by
  induction es generalizing left ws with
  | nil => simp [continuationNodes] at hw
  | cons e es ih =>
      cases e with
      | split i =>
          exact ih hl (splitFrontier_original ho) hw
      | leaf i =>
          exact ih hl (leafFrontier_original ho) hw
      | code =>
          obtain ⟨rfl, ht⟩ := hl
          simp only [continuationNodes, List.mem_append] at hw
          rcases hw with hw | hw
          · exact originalFrontier_head ho hw
          · exact ih ht (continueFrontier_original ho) hw
      | turn =>
          obtain ⟨rfl, ht⟩ := hl
          simp only [continuationNodes, List.mem_append] at hw
          rcases hw with hw | hw
          · exact originalFrontier_head ho hw
          · exact ih ht (continueFrontier_original ho) hw

/-- Every 1-edge introduced by execution comes from a continuation event. -/
theorem execute_one_continuation (es : List DiaryEvent)
    (hv : child v 1 ∈ (execute es ws).nodes) :
    child v 1 ∈ ws ∨ v ∈ continuationNodes es ws := by
  induction es generalizing ws with
  | nil => exact Or.inl hv
  | cons e es ih =>
      simp only [execute, List.mem_append] at hv
      rcases hv with hv | hv
      · exact Or.inl hv
      · rcases ih hv with hv | hv
        · cases e with
          | split => exact False.elim (splitFrontier_no_one v hv)
          | leaf => exact False.elim (leafFrontier_no_one v hv)
          | code =>
              have hh := continueFrontier_one v |>.mp hv
              exact Or.inr (by simp [continuationNodes, hh])
          | turn =>
              have hh := continueFrontier_one v |>.mp hv
              exact Or.inr (by simp [continuationNodes, hh])
        · exact Or.inr (List.mem_append_right _ hv)

/-- Both continuation types lie on the manuscript's original leftmost branch. -/
theorem Diary.toTree_one_original (d : Diary true n 1)
    (hv : child v 1 ∈ d.toTree.nodes) : 2 ∉ v := by
  rcases execute_one_continuation d.events hv with hv | hv
  · simp [child] at hv
  · exact continuationNodes_original d.events d.left_valid
      (by simp [OriginalFrontier]) hv

/-- The coding-node list is in strictly increasing order of word length. -/
theorem execute_codes_increasing (es : List DiaryEvent)
    (hws : ∀ w ∈ ws, w.length = h) :
    (execute es ws).codes.Pairwise (fun a b => a.length < b.length) := by
  induction es generalizing ws h with
  | nil => simp [execute]
  | cons e es ih =>
      apply List.pairwise_append.mpr
      have hcurrent : (e.coding ws).Pairwise (fun a b => a.length < b.length) := by
        have hopen (o : Option DiaryWord) :
            o.toList.Pairwise (fun a b => a.length < b.length) := by cases o <;> simp
        cases e with
        | split => simp [DiaryEvent.coding]
        | leaf i => exact hopen (ws[i]?)
        | code => exact hopen ws.head?
        | turn => simp [DiaryEvent.coding]
      refine ⟨hcurrent, ih (e.next_lengths hws), ?_⟩
      intro a ha b hb
      have hla := hws a (e.coding_mem ha)
      have hlb := execute_length_ge es (e.next_lengths hws) (execute_codes_nodes es hb)
      omega

theorem Diary.toTree_codes_increasing (d : Diary true n 1) :
    d.toTree.codes.Pairwise (fun a b => a.length < b.length) :=
  execute_codes_increasing (h := 0) d.events (by simp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- A bounded kernel check of the literal-tree representation: for sizes 1,2,3,
none of the 1,7,157 event diaries collapse to the same coding-node list.
The arbitrary-size injectivity/converse is not inferred from this check. -/
theorem literalCodes_distinct_first_three : ∀ n : Fin 3,
    ((diaryEnum true (n.val + 1) 1).map (fun d => d.toTree.codes)).Nodup := by
  decide +kernel

end AllThoseBigRamsey.Pseudotree
