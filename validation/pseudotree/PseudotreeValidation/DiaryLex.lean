import AllThoseBigRamsey.Pseudotree.DiaryLiteral
import Mathlib.Data.List.Lex
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-! Lexicographic frontier lemmas for the unordered literal-tree bridge. -/

namespace AllThoseBigRamsey.Pseudotree

variable {ws xs ys before after : List DiaryWord} {c : DiaryWord} {h i : Nat}

theorem child_lt_child_of_lt {u v : DiaryWord} (huv : u < v)
    (hlen : u.length = v.length) (a b : Fin 3) : child u a < child v b := by
  induction u generalizing v with
  | nil =>
      have hv : v = [] := List.length_eq_zero_iff.mp hlen.symm
      subst v
      exact (lt_irrefl [] huv).elim
  | cons x u ih =>
      cases v with
      | nil => simp at hlen
      | cons y v =>
          have hlex : List.Lex (· < ·) (x :: u) (y :: v) := huv
          cases hlex with
          | rel hxy => exact List.Lex.rel hxy
          | cons htail => exact List.Lex.cons (ih htail (by simpa using hlen))

theorem child_lt_same (w : DiaryWord) {a b : Fin 3} (hab : a < b) : child w a < child w b :=
  List.Lex.append_left (· < ·) (List.Lex.rel hab) w

theorem map_child_sorted (hs : ws.Pairwise (fun u v : DiaryWord => u < v))
    (hws : ∀ w ∈ ws, w.length = h) (a : Fin 3) :
    (ws.map (fun w => child w a)).Pairwise (fun u v => u < v) := by
  rw [List.pairwise_map]
  apply hs.imp_of_mem
  intro u v hu hv huv
  exact child_lt_child_of_lt huv ((hws u hu).trans (hws v hv).symm) a a

theorem splitFrontier_sorted (hs : ws.Pairwise (fun u v : DiaryWord => u < v))
    (hws : ∀ w ∈ ws, w.length = h) :
    (splitFrontier i ws).Pairwise (fun u v => u < v) := by
  induction ws generalizing i with
  | nil => simp [splitFrontier]
  | cons w ws ih =>
      obtain ⟨hwlt, hs⟩ := List.pairwise_cons.mp hs
      have hwlen := hws w (by simp)
      have htail : ∀ v ∈ ws, v.length = h := fun v hv => hws v (by simp [hv])
      cases i with
      | zero =>
          apply List.pairwise_cons.mpr
          refine ⟨?_, ?_⟩
          · intro v hv
            rcases List.mem_cons.mp hv with rfl | hv
            · exact child_lt_same w (by decide)
            · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
              exact child_lt_child_of_lt (hwlt u hu) (hwlen.trans (htail u hu).symm) 0 2
          · apply List.pairwise_cons.mpr
            refine ⟨?_, map_child_sorted hs htail 2⟩
            intro v hv
            obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
            exact child_lt_child_of_lt (hwlt u hu) (hwlen.trans (htail u hu).symm) 2 2
      | succ i =>
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih hs htail⟩
          intro v hv
          obtain ⟨u, hu, a, rfl⟩ := splitFrontier_parent _ hv
          exact child_lt_child_of_lt (hwlt u hu) (hwlen.trans (htail u hu).symm) 0 a

theorem leafFrontier_sorted (hs : ws.Pairwise (fun u v : DiaryWord => u < v))
    (hws : ∀ w ∈ ws, w.length = h) :
    (leafFrontier i ws).Pairwise (fun u v => u < v) := by
  induction ws generalizing i with
  | nil => simp [leafFrontier]
  | cons w ws ih =>
      obtain ⟨hwlt, hs⟩ := List.pairwise_cons.mp hs
      have hwlen := hws w (by simp)
      have htail : ∀ v ∈ ws, v.length = h := fun v hv => hws v (by simp [hv])
      cases i with
      | zero => exact map_child_sorted hs htail 2
      | succ i =>
          apply List.pairwise_cons.mpr
          refine ⟨?_, ih hs htail⟩
          intro v hv
          obtain ⟨u, hu, a, rfl⟩ := leafFrontier_parent _ hv
          exact child_lt_child_of_lt (hwlt u hu) (hwlen.trans (htail u hu).symm) 0 a

theorem continueFrontier_sorted (hs : ws.Pairwise (fun u v : DiaryWord => u < v))
    (hws : ∀ w ∈ ws, w.length = h) :
    (continueFrontier ws).Pairwise (fun u v => u < v) := by
  cases ws with
  | nil => simp [continueFrontier]
  | cons w ws =>
      obtain ⟨hwlt, hs⟩ := List.pairwise_cons.mp hs
      have hwlen := hws w (by simp)
      have htail : ∀ v ∈ ws, v.length = h := fun v hv => hws v (by simp [hv])
      apply List.pairwise_cons.mpr
      refine ⟨?_, map_child_sorted hs htail 2⟩
      intro v hv
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
      exact child_lt_child_of_lt (hwlt u hu) (hwlen.trans (htail u hu).symm) 1 2

theorem DiaryEvent.next_sorted (e : DiaryEvent)
    (hs : ws.Pairwise (fun u v : DiaryWord => u < v)) (hws : ∀ w ∈ ws, w.length = h) :
    (e.next ws).Pairwise (fun u v => u < v) := by
  cases e with
  | split => exact splitFrontier_sorted hs hws
  | leaf => exact leafFrontier_sorted hs hws
  | code => exact continueFrontier_sorted hs hws
  | turn => exact continueFrontier_sorted hs hws

theorem splitFrontier_at (before after : List DiaryWord) (c : DiaryWord) :
    splitFrontier before.length (before ++ c :: after) =
      before.map (fun w => child w 0) ++ child c 0 :: child c 2 ::
        after.map (fun w => child w 2) := by
  induction before <;> simp_all [splitFrontier]

theorem leafFrontier_at (before after : List DiaryWord) (c : DiaryWord) :
    leafFrontier before.length (before ++ c :: after) =
      before.map (fun w => child w 0) ++ after.map (fun w => child w 2) := by
  induction before <;> simp_all [leafFrontier]

/-- The position before or after the critical word agrees exactly with lex
order in a canonically sorted frontier. -/
theorem frontier_before_iff (hs : (before ++ c :: after).Pairwise
    (fun u v : DiaryWord => u < v)) {w : DiaryWord} (hw : w ∈ before ++ c :: after) :
    w ∈ before ↔ w < c := by
  obtain ⟨hb, hca, hcross⟩ := List.pairwise_append.mp hs
  obtain ⟨hafter, _⟩ := List.pairwise_cons.mp hca
  constructor
  · intro hwb
    exact hcross w hwb c (by simp)
  · intro hwc
    rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact (lt_irrefl _ hwc).elim
      · exact (lt_asymm hwc (hafter w hw)).elim

theorem frontier_after_iff (hs : (before ++ c :: after).Pairwise
    (fun u v : DiaryWord => u < v)) {w : DiaryWord} (hw : w ∈ before ++ c :: after) :
    w ∈ after ↔ c < w := by
  obtain ⟨hb, hca, hcross⟩ := List.pairwise_append.mp hs
  obtain ⟨hafter, _⟩ := List.pairwise_cons.mp hca
  constructor
  · exact fun hw => hafter w hw
  · intro hcw
    rcases List.mem_append.mp hw with hw | hw
    · exact (lt_asymm (hcross w hw c (by simp)) hcw).elim
    · rcases List.mem_cons.mp hw with rfl | hw
      · exact (lt_irrefl _ hcw).elim
      · exact hw

def localChild (critical : DiaryWord) (special : Fin 3 → Prop)
    (w : DiaryWord) (a : Fin 3) : Prop :=
  if w = critical then special a else if w < critical then a = 0 else a = 2

@[simp] theorem child_mem_map (ws : List DiaryWord) (w : DiaryWord) (a b : Fin 3) :
    child w a ∈ ws.map (fun u => child u b) ↔ w ∈ ws ∧ a = b := by
  simp only [List.mem_map, child_injective]
  aesop

theorem splitFrontier_child_local
    (hs : (before ++ c :: after).Pairwise (fun u v : DiaryWord => u < v))
    {w : DiaryWord} (hw : w ∈ before ++ c :: after) (a : Fin 3) :
    child w a ∈ splitFrontier before.length (before ++ c :: after) ↔
      localChild c (fun a => a = 0 ∨ a = 2) w a := by
  have hb := frontier_before_iff hs hw
  have ha := frontier_after_iff hs hw
  rw [splitFrontier_at]
  simp only [List.mem_append, List.mem_cons, child_mem_map, child_injective]
  rw [hb, ha]
  unfold localChild
  by_cases heq : w = c
  · subst w
    simp
  · by_cases hlt : w < c
    · simp [heq, hlt, not_lt_of_ge hlt.le]
    · have hgt : c < w := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      simp [heq, hlt, hgt]

theorem leafFrontier_child_local
    (hs : (before ++ c :: after).Pairwise (fun u v : DiaryWord => u < v))
    {w : DiaryWord} (hw : w ∈ before ++ c :: after) (a : Fin 3) :
    child w a ∈ leafFrontier before.length (before ++ c :: after) ↔
      localChild c (fun _ => False) w a := by
  have hb := frontier_before_iff hs hw
  have ha := frontier_after_iff hs hw
  rw [leafFrontier_at]
  simp only [List.mem_append, child_mem_map]
  rw [hb, ha]
  unfold localChild
  by_cases heq : w = c
  · subst w
    simp
  · by_cases hlt : w < c
    · simp [heq, hlt, not_lt_of_ge hlt.le]
    · have hgt : c < w := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      simp [heq, hlt, hgt]

theorem continueFrontier_child_local
    (hs : (c :: after).Pairwise (fun u v : DiaryWord => u < v))
    {w : DiaryWord} (hw : w ∈ c :: after) (a : Fin 3) :
    child w a ∈ continueFrontier (c :: after) ↔ localChild c (fun a => a = 1) w a := by
  have hb := frontier_before_iff (before := []) hs hw
  have ha := frontier_after_iff (before := []) hs hw
  simp at hb
  simp only [continueFrontier, List.mem_cons, child_mem_map, child_injective]
  rw [ha]
  unfold localChild
  by_cases heq : w = c
  · subst w
    simp
  · have hgt : c < w := lt_of_le_of_ne hb (Ne.symm heq)
    simp [heq, not_lt_of_ge hb, hgt]

/-- The unique word avoiding 2, when it exists, is literally the first
frontier word. This derives the continuation index from the paper's
word-based original-branch restriction. -/
theorem originalFrontier_unique (ho : OriginalFrontier left ws)
    (hw : w ∈ ws) (hone : (2 : Fin 3) ∉ w) : ws.head? = some w ∧ left = true := by
  induction ws generalizing left with
  | nil => simp at hw
  | cons c ws ih =>
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ⟨rfl, ho.1.mp hone⟩
      · have hfalse := (ih ho.2 hw).2
        contradiction

theorem sorted_list_eq_of_mem (hs : xs.Pairwise (fun u v : DiaryWord => u < v))
    (ht : ys.Pairwise (fun u v : DiaryWord => u < v))
    (hmem : ∀ w, w ∈ xs ↔ w ∈ ys) : xs = ys := by
  have hx : xs.Nodup := hs.imp (fun h => ne_of_lt h)
  have hy : ys.Nodup := ht.imp (fun h => ne_of_lt h)
  exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => (lt_asymm hab hba).elim)
    hs ht ((List.perm_ext_iff_of_nodup hx hy).mpr hmem)

end AllThoseBigRamsey.Pseudotree
