import PseudotreeValidation.DiaryLex

/-! Finite-set literal diary axioms and canonical ordered frontiers. -/

namespace AllThoseBigRamsey.Pseudotree

inductive PaperKind
  | split | leaf | code | turn
  deriving DecidableEq, Repr

def PaperKind.special : PaperKind → Fin 3 → Prop
  | .split, a => a = 0 ∨ a = 2
  | .leaf, _ => False
  | .code, a | .turn, a => a = 1

def PaperKind.coded : PaperKind → Bool
  | .leaf | .code => true
  | .split | .turn => false

def PaperKind.continues : PaperKind → Bool
  | .code | .turn => true
  | .split | .leaf => false

def PaperKind.allowsTurn : PaperKind → Bool
  | .split | .leaf => true
  | .code | .turn => false

def DiaryEvent.kind : DiaryEvent → PaperKind
  | .split _ => .split
  | .leaf _ => .leaf
  | .code => .code
  | .turn => .turn

@[simp] theorem DiaryEvent.kind_allowsTurn (e : DiaryEvent) :
    e.kind.allowsTurn = e.allowsTurn := by cases e <;> rfl

/-- The manuscript's four rules at one level, stated directly on finite
SETS of words, with lexicographic comparison and an actual critical word. -/
structure PaperLevel (nodes codes : Finset DiaryWord) (j : Nat)
    (kind : PaperKind) (critical : DiaryWord) : Prop where
  critical_mem : critical ∈ nodes
  critical_length : critical.length = j
  coding : ∀ w ∈ nodes, w.length = j → (w ∈ codes ↔ w = critical ∧ kind.coded = true)
  children : ∀ w ∈ nodes, w.length = j → ∀ a : Fin 3,
    child w a ∈ nodes ↔ localChild critical kind.special w a
  original : kind.continues = true → (2 : Fin 3) ∉ critical

/-- Raw finite-set formulation. Height is a bound with a critical node at
each smaller level, so trailing empty levels are excluded. -/
structure PaperTreeAxioms (nodes codes : Finset DiaryWord) (height : Nat) : Prop where
  height_pos : 0 < height
  bounded : ∀ w ∈ nodes, w.length < height
  prefix_closed : ∀ w ∈ nodes, ∀ j ≤ w.length, w.take j ∈ nodes
  code_subset : codes ⊆ nodes
  level : ∀ j < height, ∃ kind critical, PaperLevel nodes codes j kind critical
  initial : ∀ critical, ¬PaperLevel nodes codes 0 .turn critical
  following : ∀ j critical kind previous,
    PaperLevel nodes codes (j + 1) .turn critical →
    PaperLevel nodes codes j kind previous → kind.allowsTurn = true

structure PaperDiary (n : Nat) where
  nodes : Finset DiaryWord
  codes : Finset DiaryWord
  axioms : ∃ height, PaperTreeAxioms nodes codes height
  size : codes.card = n

/-- Canonical lexicographic enumeration of a finite level. -/
def sortedLevel (nodes : Finset DiaryWord) (j : Nat) : List DiaryWord :=
  (nodes.filter (fun w => w.length = j)).sort (· ≤ ·)

@[simp] theorem mem_sortedLevel (nodes : Finset DiaryWord) (j : Nat) (w : DiaryWord) :
    w ∈ sortedLevel nodes j ↔ w ∈ nodes ∧ w.length = j := by
  simp [sortedLevel]

theorem sortedLevel_sorted (nodes : Finset DiaryWord) (j : Nat) :
    (sortedLevel nodes j).Pairwise (fun u v => u < v) :=
  (Finset.sortedLT_sort _).pairwise

theorem sortedLevel_lengths (nodes : Finset DiaryWord) (j : Nat) :
    ∀ w ∈ sortedLevel nodes j, w.length = j := fun _ hw => (mem_sortedLevel _ _ _).mp hw |>.2

theorem sortedLevel_nodup (nodes : Finset DiaryWord) (j : Nat) :
    (sortedLevel nodes j).Nodup := Finset.sort_nodup _ _

/-- Reconstructing one local event from a raw set-level specification. -/
theorem PaperLevel.event {nodes codes : Finset DiaryWord} {j : Nat} {kind : PaperKind}
    {critical : DiaryWord} (P : PaperLevel nodes codes j kind critical)
    (hprefix : ∀ w ∈ nodes, ∀ i ≤ w.length, w.take i ∈ nodes)
    (hcodes : codes ⊆ nodes)
    (ho : OriginalFrontier left (sortedLevel nodes j)) :
    ∃ e : DiaryEvent, e.legal (sortedLevel nodes j).length ∧ e.kind = kind ∧
      e.next (sortedLevel nodes j) = sortedLevel nodes (j + 1) ∧
      e.coding (sortedLevel nodes j) = sortedLevel codes j ∧
      (e = .code ∨ e = .turn →
        ∀ w ∈ (sortedLevel nodes j).head?.toList, (2 : Fin 3) ∉ w) := by
  let ws := sortedLevel nodes j
  have hs : ws.Pairwise (fun u v => u < v) := sortedLevel_sorted nodes j
  have hlen : ∀ w ∈ ws, w.length = j := sortedLevel_lengths nodes j
  change OriginalFrontier left ws at ho
  have hc : critical ∈ ws := (mem_sortedLevel _ _ _).mpr ⟨P.critical_mem, P.critical_length⟩
  obtain ⟨before, after, hws⟩ := List.append_of_mem hc
  have hindex : before.length < ws.length := by rw [hws]; simp
  have hchild (e : DiaryEvent)
      (hlocal : ∀ w ∈ ws, ∀ a : Fin 3,
        child w a ∈ e.next ws ↔ localChild critical kind.special w a) :
      e.next ws = sortedLevel nodes (j + 1) := by
    apply sorted_list_eq_of_mem (e.next_sorted hs hlen) (sortedLevel_sorted _ _)
    intro v
    constructor
    · intro hv
      obtain ⟨w, hw, a, rfl⟩ := e.next_parent hv
      have hwm := (mem_sortedLevel _ _ _).mp hw
      refine (mem_sortedLevel _ _ _).mpr ⟨?_, by simp [child, hwm.2]⟩
      exact (P.children w hwm.1 hwm.2 a).mpr ((hlocal w hw a).mp hv)
    · intro hv
      obtain ⟨hv, hvlen⟩ := (mem_sortedLevel _ _ _).mp hv
      have hvne : v ≠ [] := by intro h; simp [h] at hvlen
      obtain ⟨a, w, hrev⟩ := List.exists_cons_of_ne_nil (l := v.reverse) (by simpa using hvne)
      have hvform : v = child w.reverse a := by
        have h := congrArg List.reverse hrev
        simpa [child] using h
      rw [hvform] at hv hvlen ⊢
      have hwlen : w.reverse.length = j := by
        simpa only [child, List.length_append, List.length_singleton, Nat.add_right_cancel_iff]
          using hvlen
      have hwn : w.reverse ∈ nodes := by
        have hp := hprefix _ hv j (by simp [child, hwlen])
        simpa [child, ← hwlen] using hp
      have hwm : w.reverse ∈ ws := (mem_sortedLevel _ _ _).mpr ⟨hwn, hwlen⟩
      exact (hlocal _ hwm a).mpr ((P.children _ hwn hwlen a).mp hv)
  have hcode (e : DiaryEvent) (he : e.coding ws =
      if kind.coded then [critical] else []) : e.coding ws = sortedLevel codes j := by
    rw [he]
    apply sorted_list_eq_of_mem
    · cases h : kind.coded <;> simp
    · exact sortedLevel_sorted _ _
    · intro w
      have hwm : w ∈ codes ∧ w.length = j ↔ w = critical ∧ kind.coded = true := by
        constructor
        · rintro ⟨hw, hwlen⟩
          exact (P.coding w (hcodes hw) hwlen).mp hw
        · rintro ⟨heq, hk⟩
          subst w
          exact ⟨(P.coding critical P.critical_mem P.critical_length).mpr ⟨rfl, hk⟩,
            P.critical_length⟩
      rw [mem_sortedLevel, hwm]
      cases h : kind.coded <;> simp
  cases kind with
  | split =>
      let e := DiaryEvent.split before.length
      refine ⟨e, hindex, rfl, hchild e ?_, hcode e rfl, ?_⟩
      · intro w hw a
        rw [hws] at hs hw ⊢
        exact splitFrontier_child_local hs hw a
      · intro heq
        simp [e] at heq
  | leaf =>
      let e := DiaryEvent.leaf before.length
      refine ⟨e, hindex, rfl, hchild e ?_, hcode e ?_, ?_⟩
      · intro w hw a
        rw [hws] at hs hw ⊢
        exact leafFrontier_child_local hs hw a
      · simp [e, DiaryEvent.coding, hws, PaperKind.coded]
      · intro heq
        simp [e] at heq
  | code =>
      have hone : (2 : Fin 3) ∉ critical := P.original rfl
      have hhead := (originalFrontier_unique ho hc hone).1
      obtain ⟨tail, hws'⟩ := List.head?_eq_some_iff.mp hhead
      have hpos : 0 < ws.length := by rw [hws']; simp
      refine ⟨.code, hpos, rfl, hchild .code ?_, hcode .code ?_, ?_⟩
      · intro w hw a
        rw [hws'] at hs hw ⊢
        exact continueFrontier_child_local hs hw a
      · simp [DiaryEvent.coding, hhead, PaperKind.coded]
      · intro _ w hw
        change w ∈ ws.head?.toList at hw
        have : w = critical := by simpa [hhead] using hw
        simpa [this] using hone
  | turn =>
      have hone : (2 : Fin 3) ∉ critical := P.original rfl
      have hhead := (originalFrontier_unique ho hc hone).1
      obtain ⟨tail, hws'⟩ := List.head?_eq_some_iff.mp hhead
      have hpos : 0 < ws.length := by rw [hws']; simp
      refine ⟨.turn, hpos, rfl, hchild .turn ?_, hcode .turn rfl, ?_⟩
      · intro w hw a
        rw [hws'] at hs hw ⊢
        exact continueFrontier_child_local hs hw a
      · intro _ w hw
        change w ∈ ws.head?.toList at hw
        have : w = critical := by simpa [hhead] using hw
        simpa [this] using hone

def flattenedLevels (S : Finset DiaryWord) (j : Nat) : Nat → List DiaryWord
  | 0 => []
  | count + 1 => sortedLevel S j ++ flattenedLevels S (j + 1) count

theorem mem_flattenedLevels (S : Finset DiaryWord) (j count : Nat) (w : DiaryWord) :
    w ∈ flattenedLevels S j count ↔ w ∈ S ∧ j ≤ w.length ∧ w.length < j + count := by
  induction count generalizing j with
  | zero => simp [flattenedLevels]
  | succ count ih =>
      simp only [flattenedLevels, List.mem_append, mem_sortedLevel, ih]
      constructor
      · rintro (⟨hw, hlen⟩ | ⟨hw, hlo, hhi⟩)
        · exact ⟨hw, by omega, by omega⟩
        · exact ⟨hw, by omega, by omega⟩
      · rintro ⟨hw, hlo, hhi⟩
        by_cases hlen : w.length = j
        · exact Or.inl ⟨hw, hlen⟩
        · exact Or.inr ⟨hw, by omega, by omega⟩

theorem flattenedLevels_nodup (S : Finset DiaryWord) (j count : Nat) :
    (flattenedLevels S j count).Nodup := by
  induction count generalizing j with
  | zero => simp [flattenedLevels]
  | succ count ih =>
      apply List.nodup_append.mpr
      refine ⟨sortedLevel_nodup S j, ih (j + 1), ?_⟩
      intro a ha b hb heq
      have hla := (mem_sortedLevel _ _ _).mp ha |>.2
      have hlb := (mem_flattenedLevels _ _ _ _).mp hb |>.2.1
      subst b
      omega

theorem flattenedLevels_toFinset (S : Finset DiaryWord) (height : Nat)
    (hbound : ∀ w ∈ S, w.length < height) : (flattenedLevels S 0 height).toFinset = S := by
  ext w
  simp only [List.mem_toFinset, mem_flattenedLevels, Nat.zero_le, true_and, Nat.zero_add]
  exact ⟨And.left, fun hw => ⟨hw, hbound w hw⟩⟩

theorem flattenedLevels_length (S : Finset DiaryWord) (height : Nat)
    (hbound : ∀ w ∈ S, w.length < height) : (flattenedLevels S 0 height).length = S.card := by
  have hc := List.toFinset_card_of_nodup (flattenedLevels_nodup S 0 height)
  rw [flattenedLevels_toFinset S height hbound] at hc
  exact hc.symm

def canonicalFrames (nodes codes : Finset DiaryWord) (j : Nat) : Nat → List LiteralLevel
  | 0 => []
  | count + 1 => ⟨sortedLevel nodes j, sortedLevel codes j⟩ ::
      canonicalFrames nodes codes (j + 1) count

@[simp] theorem canonicalFrames_codes (nodes codes : Finset DiaryWord) (j count : Nat) :
    (canonicalFrames nodes codes j count).flatMap LiteralLevel.codes = flattenedLevels codes j count := by
  induction count generalizing j <;> simp_all [canonicalFrames, flattenedLevels]

@[simp] theorem canonicalFrames_nodes (nodes codes : Finset DiaryWord) (j count : Nat) :
    (canonicalFrames nodes codes j count).flatMap LiteralLevel.frontier = flattenedLevels nodes j count := by
  induction count generalizing j <;> simp_all [canonicalFrames, flattenedLevels]

theorem PaperTreeAxioms.sorted_root {nodes codes : Finset DiaryWord} {height : Nat}
    (T : PaperTreeAxioms nodes codes height) : sortedLevel nodes 0 = [[]] := by
  obtain ⟨kind, c, P⟩ := T.level 0 T.height_pos
  have hroot : [] ∈ nodes := by
    simpa using T.prefix_closed c P.critical_mem 0 (Nat.zero_le _)
  apply sorted_list_eq_of_mem (sortedLevel_sorted _ _) (by simp)
  intro w
  simp only [mem_sortedLevel, List.length_eq_zero_iff, List.mem_singleton]
  exact ⟨And.right, fun hw => ⟨hw ▸ hroot, hw⟩⟩

/-- Canonical sorting of ANY raw finite-set diary satisfies the independent
literal-level axioms. The type-(d) restriction is transferred from the raw
previous-level rule; original-branch state is recovered from actual words. -/
theorem PaperTreeAxioms.canonical_legal {nodes codes : Finset DiaryWord} {height : Nat}
    (T : PaperTreeAxioms nodes codes height) (j count : Nat) (hend : j + count = height)
    (ho : OriginalFrontier left (sortedLevel nodes j))
    (hturn : ∀ c, PaperLevel nodes codes j .turn c → allowed = true) :
    LiteralLevels allowed (sortedLevel nodes j) (canonicalFrames nodes codes j count) := by
  induction count generalizing j left allowed with
  | zero =>
      have hnil : sortedLevel nodes j = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro w hw
        obtain ⟨hw, hlen⟩ := (mem_sortedLevel _ _ _).mp hw
        have hb := T.bounded w hw
        omega
      rw [hnil]
      exact LiteralLevels.done allowed
  | succ count ih =>
      have hj : j < height := by omega
      obtain ⟨kind, c, P⟩ := T.level j hj
      obtain ⟨e, he, hk, hn, hc, hone⟩ := P.event T.prefix_closed T.code_subset ho
      have ho' : OriginalFrontier (e.nextLeft left) (sortedLevel nodes (j + 1)) := by
        rw [← hn]
        exact e.next_original ho
      have ht' : ∀ c', PaperLevel nodes codes (j + 1) .turn c' → e.allowsTurn = true := by
        intro c' P'
        rw [← e.kind_allowsTurn, hk]
        exact T.following j c' kind c P' P
      have htail := ih (j + 1) (by omega) ho' ht'
      have heturn : e = .turn → allowed = true := by
        intro heq
        have hkind : kind = .turn := by rw [heq] at hk; exact hk.symm
        apply hturn c
        simpa only [hkind] using P
      have htail' : LiteralLevels e.allowsTurn (e.next (sortedLevel nodes j))
          (canonicalFrames nodes codes (j + 1) count) := by rw [hn]; exact htail
      have hstep := LiteralLevels.step e he hone heturn htail'
      simpa only [canonicalFrames, hc] using hstep

/-- The raw finite SETS in the manuscript reconstruct a grammar diary.
Both node and code equalities here are extensional membership equivalences. -/
theorem PaperDiary.represented (D : PaperDiary n) :
    ∃ d : Diary true n 1,
      (∀ w, w ∈ d.toTree.nodes ↔ w ∈ D.nodes) ∧
      (∀ w, w ∈ d.toTree.codes ↔ w ∈ D.codes) := by
  obtain ⟨height, T⟩ := D.axioms
  have hroot := T.sorted_root
  have hlegal := T.canonical_legal 0 height (by simp)
    (left := true) (by rw [hroot]; simp [OriginalFrontier])
    (allowed := false) (fun c hc => (T.initial c hc).elim)
  have hcBound : ∀ w ∈ D.codes, w.length < height := fun w hw => T.bounded w (T.code_subset hw)
  let L : LiteralDiary n := ⟨canonicalFrames D.nodes D.codes 0 height,
    by simpa only [hroot] using hlegal,
    by rw [canonicalFrames_codes, flattenedLevels_length _ _ hcBound]; exact D.size⟩
  obtain ⟨d, hd⟩ := Diary.toLiteral_surjective L
  have htree : d.toTree = L.tree := by rw [← d.toLiteral_tree, hd]
  refine ⟨d, ?_, ?_⟩
  · intro w
    rw [htree]
    change w ∈ (canonicalFrames D.nodes D.codes 0 height).flatMap LiteralLevel.frontier ↔ w ∈ D.nodes
    rw [canonicalFrames_nodes, ← List.mem_toFinset, flattenedLevels_toFinset _ _ T.bounded]
  · intro w
    rw [htree]
    change w ∈ (canonicalFrames D.nodes D.codes 0 height).flatMap LiteralLevel.codes ↔ w ∈ D.codes
    rw [canonicalFrames_codes, ← List.mem_toFinset, flattenedLevels_toFinset _ _ hcBound]

end AllThoseBigRamsey.Pseudotree
