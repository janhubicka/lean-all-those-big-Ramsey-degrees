import PseudotreeValidation.NormalizationLocal
import PseudotreeValidation.SparseChainGeometry
import PseudotreeValidation.SparseLeftmost
import PseudotreeValidation.DiarySoundness

/-! Extracting a literal diary from an actual chain in the sparse copy. -/

namespace AllThoseBigRamsey.Pseudotree.SparseNormalization

open RayEmbeddings RayMapModel LevelProjection DiaryNormalization

abbrev Tree (w : DiaryWord) : Prop := Sparse.InTree (w.map toLetter)
abbrev Point (w : DiaryWord) : Prop := Sparse.InSparse (w.map toLetter)

def critical (j : Nat) : DiaryWord := (Sparse.critical j).map toFin

@[simp] theorem critical_map (j : Nat) : (critical j).map toLetter = Sparse.critical j := by
  simp [critical, List.map_map, Function.comp_def]

@[simp] theorem critical_length (j : Nat) : (critical j).length = j := by
  simp [critical, Sparse.critical_length]

theorem toLetter_injective : Function.Injective toLetter := by
  intro a b heq
  simpa only [toFin_toLetter] using congrArg toFin heq

@[simp] theorem toLetter_eq {a b : Fin 3} : toLetter a = toLetter b ↔ a = b :=
  toLetter_injective.eq_iff

@[simp] theorem map_toLetter_eq {s t : DiaryWord} :
    s.map toLetter = t.map toLetter ↔ s = t := by
  constructor
  · intro h
    simpa [List.map_map, Function.comp_def] using congrArg (List.map toFin) h
  · rintro rfl
    rfl

@[simp] theorem rank_letter (a : Fin 3) : Sparse.rank (toLetter a) = a.val := by
  fin_cases a <;> rfl

theorem lexLess_map (s t : DiaryWord) :
    Sparse.lexLess (s.map toLetter) (t.map toLetter) = decide (s < t) := by
  induction s generalizing t with
  | nil => cases t <;> simp [Sparse.lexLess]
  | cons a s ih =>
      cases t with
      | nil => simp [Sparse.lexLess]
      | cons b t =>
          by_cases hab : a = b
          · subst b
            simp [Sparse.lexLess, ih, List.cons_lt_cons_iff]
          · have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
            simp [Sparse.lexLess, hv, List.cons_lt_cons_iff, hab]

theorem tree_prefix {s t : DiaryWord} (ht : Tree t) (hp : s.IsPrefix t) : Tree s :=
  Sparse.inTree_prefix ht (hp.map toLetter)

theorem point_tree {w : DiaryWord} (hw : Point w) : Tree w := by
  obtain ⟨n, hn⟩ := (Sparse.inSparse_iff_code _).mp hw
  exact ⟨n, by rw [hn]⟩

theorem rawNode_tree {C : Finset DiaryWord} (hC : ∀ w ∈ C, Point w) {s : DiaryWord}
    (hs : RawNode C s) : Tree s := by
  obtain ⟨w, hw, hp⟩ := hs
  exact tree_prefix (point_tree (hC w hw)) hp

theorem point_at_level {w : DiaryWord} {j : Nat} (hlen : w.length = j) :
    Point w ↔ j % 3 = 2 ∧ w = critical j := by
  have h := Sparse.inSparse_at_level j (w.map toLetter) (by simpa using hlen)
  rw [← critical_map j, map_toLetter_eq] at h
  exact h

theorem tree_children (j : Nat) (w : DiaryWord) (hw : Tree w) (hlen : w.length = j)
    (a : Fin 3) :
    Tree (child w a) ↔
      if w = critical j then (if j % 3 = 2 then a = 1 else a = 0 ∨ a = 2)
      else (if w < critical j then a = 0 else a = 2) := by
  have h := Sparse.critical_children j (w.map toLetter) hw (by simpa using hlen) (toLetter a)
  have heq : w.map toLetter = Sparse.critical j ↔ w = critical j := by
    rw [← critical_map j, map_toLetter_eq]
  have hlex : Sparse.lexLess (w.map toLetter) (Sparse.critical j) = decide (w < critical j) := by
    rw [← critical_map j, lexLess_map]
  have h0 : toLetter (0 : Fin 3) = TernaryLetter.zero := rfl
  have h1 : toLetter (1 : Fin 3) = TernaryLetter.one := rfl
  have h2 : toLetter (2 : Fin 3) = TernaryLetter.two := rfl
  by_cases hc : w = critical j <;> by_cases hp : j % 3 = 2 <;> by_cases hl : w < critical j <;>
    simpa [Tree, child, Sparse.CriticalChildren, Sparse.direction, heq, hlex,
      hc, hp, hl, ← h0, ← h1, ← h2] using h

theorem spine {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : Point v)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v) : Spine C v := by
  intro w hw k hk
  obtain ⟨hkw, hletter⟩ := List.getElem?_eq_some_iff.mp hk
  have heq : w = w.take k ++ 1 :: w.drop (k+1) := by
    simpa only [List.drop_eq_getElem_cons hkw, hletter] using (List.take_append_drop k w).symm
  have hp := Sparse.fin_one_prefix_on_spine (hC w hw) hv (hmax w hw) heq
  have hlength : (w.take k ++ [(1 : Fin 3)]).length = k+1 := by simp [hkw.le]
  rw [List.take_succ_eq_append_getElem hkw, hletter]
  simpa only [hlength] using List.prefix_iff_eq_take.mp hp

theorem raw_child_at {C : Finset DiaryWord} {w : DiaryWord} (hw : w ∈ C)
    {j : Nat} (hj : j < w.length) : RawNode C (child (w.take j) w[j]) := by
  refine ⟨w, hw, ?_⟩
  change (w.take j ++ [w[j]]).IsPrefix w
  rw [List.take_append_getElem hj]
  exact List.take_prefix _ _

theorem raw_has_child {C : Finset DiaryWord} {w : DiaryWord}
    (hw : RawNode C w) (hcode : w ∉ C) : ∃ a, RawNode C (child w a) := by
  obtain ⟨c, hc, tail, htail⟩ := hw
  cases tail with
  | nil =>
      have heq : w = c := by simpa using htail
      exact (hcode (heq.symm ▸ hc)).elim
  | cons a t =>
      exact ⟨a, c, hc, t, by simpa [child, List.append_assoc] using htail⟩

theorem point_unique_length {s t : DiaryWord} (hs : Point s) (ht : Point t)
    (hlen : s.length = t.length) : s = t := by
  have hs' := (point_at_level (j := t.length) hlen).mp hs
  have ht' := (point_at_level (j := t.length) rfl).mp ht
  exact hs'.2.trans ht'.2.symm

theorem raw_noncritical_children {C : Finset DiaryWord} (hC : ∀ w ∈ C, Point w)
    {j : Nat} {w : DiaryWord} (hw : RawNode C w) (hlen : w.length = j)
    (hne : w ≠ critical j) (a : Fin 3) :
    RawNode C (child w a) ↔ if w < critical j then a = 0 else a = 2 := by
  have htree := tree_children j w (rawNode_tree hC hw) hlen
  have hncode : w ∉ C := by
    intro hmem
    exact hne ((point_at_level hlen).mp (hC w hmem)).2
  constructor
  · intro hwa
    simpa only [hne, ite_false] using (htree a).mp (rawNode_tree hC hwa)
  · intro ha
    obtain ⟨b, hb⟩ := raw_has_child hw hncode
    have hb' := (htree b).mp (rawNode_tree hC hb)
    have hab : a = b := by
      by_cases hl : w < critical j <;> simp_all
    simpa only [hab] using hb

theorem fork_critical {C : Finset DiaryWord} (hC : ∀ w ∈ C, Point w)
    {j : Nat} (hj : ForkAt C j) :
    j % 3 ≠ 2 ∧ RawNode C (critical j) ∧
      RawNode C (child (critical j) 0) ∧ RawNode C (child (critical j) 2) := by
  obtain ⟨s, hs, t, ht, hjs, hjt, hpre, hneq⟩ := hj
  have hsa := raw_child_at hs hjs
  have htb := raw_child_at ht hjt
  rw [← hpre] at htb
  have hnode : RawNode C (s.take j) := ⟨s, hs, List.take_prefix _ _⟩
  have hlen : (s.take j).length = j := by simp [hjs.le]
  have hne : s[j] ≠ t[j] := by
    intro heq
    exact hneq (by simpa [hjs, hjt] using congrArg some heq)
  have hc : s.take j = critical j := by
    by_contra hh
    have ha := (raw_noncritical_children hC hnode hlen hh _).mp hsa
    have hb := (raw_noncritical_children hC hnode hlen hh _).mp htb
    by_cases hl : s.take j < critical j
    · simp only [hl, ite_true] at ha hb
      exact hne (ha.trans hb.symm)
    · simp only [hl, ite_false] at ha hb
      exact hne (ha.trans hb.symm)
  have htree := tree_children j (s.take j) (rawNode_tree hC hnode) hlen
  have ha := (htree s[j]).mp (rawNode_tree hC hsa)
  have hb := (htree t[j]).mp (rawNode_tree hC htb)
  have hphase : j % 3 ≠ 2 := by
    intro hphase
    simp only [hc, ite_true, hphase] at ha hb
    exact hne (ha.trans hb.symm)
  simp only [hc, ite_true, hphase, ite_false] at ha hb
  refine ⟨hphase, hc ▸ hnode, ?_, ?_⟩
  · rcases ha with ha | ha
    · simpa only [hc, ha] using hsa
    · have hb0 : t[j] = 0 := by rcases hb with hb | hb; exact hb; exact (hne (ha.trans hb.symm)).elim
      simpa only [hc, hb0] using htb
  · rcases ha with ha | ha
    · have hb2 : t[j] = 2 := by rcases hb with hb | hb; exact (hne (ha.trans hb.symm)).elim; exact hb
      simpa only [hc, hb2] using htb
    · simpa only [hc, ha] using hsa

theorem one_critical {C : Finset DiaryWord} (hC : ∀ w ∈ C, Point w)
    {j : Nat} {w : DiaryWord} (hw : RawNode C (child w 1)) (hlen : w.length = j) :
    w = critical j ∧ j % 3 = 2 := by
  have hnode : RawNode C w := by
    obtain ⟨c, hc, hp⟩ := hw
    exact ⟨c, hc, (List.prefix_append w [1]).trans hp⟩
  have h := (tree_children j w (rawNode_tree hC hnode) hlen 1).mp (rawNode_tree hC hw)
  by_cases heq : w = critical j <;> by_cases hphase : j % 3 = 2 <;>
    by_cases hlt : w < critical j <;> simp_all

theorem selected_critical {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C) {j : Nat} (hj : j ∈ selected C v) :
    RawNode C (critical j) := by
  rcases mem_selected_iff.mp hj with he | hturn
  · rcases mem_essential_iff.mp he with ⟨w, hw, hlen⟩ | hfork
    · have heq := ((point_at_level hlen).mp (hC w hw)).2
      exact ⟨w, hw, by rw [← heq]⟩
    · exact (fork_critical hC hfork).2.1
  · obtain ⟨p, hp, hpj, he, hvp, hvj, hfirst⟩ := hturn
    obtain ⟨hjv, hletter⟩ := List.getElem?_eq_some_iff.mp hvj
    have hchild := raw_child_at hv hjv
    rw [hletter] at hchild
    have heq := (one_critical (j := j) hC hchild (by simp [hjv.le])).1
    exact ⟨v, hv, by rw [← heq]; exact List.take_prefix _ _⟩

theorem turn_child {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C) {j : Nat} (hj : TurnAt C v j) :
    RawNode C (child (critical j) 1) := by
  obtain ⟨p, hp, hpj, he, hvp, hvj, hfirst⟩ := hj
  obtain ⟨hjv, hletter⟩ := List.getElem?_eq_some_iff.mp hvj
  have hchild := raw_child_at hv hjv
  rw [hletter] at hchild
  have heq := (one_critical (j := j) hC hchild (by simp [hjv.le])).1
  simpa only [heq] using hchild

noncomputable def kind (C : Finset DiaryWord) (j : Nat) : PaperKind := by
  classical
  exact if critical j ∈ C then
    if RawNode C (child (critical j) 1) then .code else .leaf
  else if ForkAt C j then .split else .turn

theorem kind_coded {C : Finset DiaryWord} {j : Nat} :
    (kind C j).coded = true ↔ critical j ∈ C := by
  classical
  unfold kind
  split <;> split <;> simp_all [PaperKind.coded]

theorem essential_of_critical_mem {C : Finset DiaryWord} {j : Nat}
    (hj : critical j ∈ C) : j ∈ essential C := by
  simpa only [critical_length] using length_mem_essential hj

theorem essential_cases {C : Finset DiaryWord} (hC : ∀ w ∈ C, Point w)
    {j : Nat} (hj : j ∈ essential C) : critical j ∈ C ∨ ForkAt C j := by
  rcases mem_essential_iff.mp hj with ⟨w, hw, hlen⟩ | hf
  · exact Or.inl (((point_at_level hlen).mp (hC w hw)).2 ▸ hw)
  · exact Or.inr hf

theorem kind_turn_iff {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) {j : Nat} (hj : j ∈ selected C v) :
    kind C j = .turn ↔ TurnAt C v j := by
  classical
  constructor
  · intro hk
    have hnc : critical j ∉ C := by
      intro hc
      simp only [kind, hc, ite_true] at hk
      split at hk <;> cases hk
    have hnf : ¬ ForkAt C j := by
      intro hf
      simp only [kind, hnc, hf, ite_false, ite_true] at hk
      cases hk
    have hnot : j ∉ essential C := by
      intro he
      exact (essential_cases hC he).elim hnc hnf
    exact (mem_selected_iff.mp hj).resolve_left hnot
  · intro ht
    have hn := turn_not_essential ht
    have hnc : critical j ∉ C := fun hc => hn (essential_of_critical_mem hc)
    have hnf : ¬ ForkAt C j := fun hf => hn (fork_mem_essential hf)
    simp [kind, hnc, hnf]

theorem raw_critical_children {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C) {j : Nat} (hj : j ∈ selected C v)
    (a : Fin 3) :
    RawNode C (child (critical j) a) ↔ (kind C j).special a := by
  classical
  have hr := selected_critical hC hv hj
  have htree := tree_children j (critical j) (rawNode_tree hC hr) (critical_length j)
  by_cases hc : critical j ∈ C
  · have hphase := ((point_at_level (critical_length j)).mp (hC _ hc)).1
    have hallowed (b : Fin 3) (hb : RawNode C (child (critical j) b)) : b = 1 := by
      simpa [hphase] using (htree b).mp (rawNode_tree hC hb)
    by_cases h1 : RawNode C (child (critical j) 1)
    · simp only [kind, hc, h1, ↓reduceIte, PaperKind.special]
      exact ⟨hallowed a, fun h => h ▸ h1⟩
    · simp only [kind, hc, h1, ↓reduceIte, PaperKind.special, iff_false]
      exact fun ha => h1 (hallowed a ha ▸ ha)
  · by_cases hf : ForkAt C j
    · obtain ⟨hphase, _, h0, h2⟩ := fork_critical hC hf
      simp only [kind, hc, hf, ↓reduceIte, PaperKind.special]
      constructor
      · intro ha
        simpa [hphase] using (htree a).mp (rawNode_tree hC ha)
      · rintro (rfl | rfl)
        · exact h0
        · exact h2
    · have ht : TurnAt C v j := (kind_turn_iff hC hj).mp (by simp [kind, hc, hf])
      have h1 := turn_child hC hv ht
      have hphase := (one_critical hC h1 (critical_length j)).2
      simp only [kind, hc, hf, ↓reduceIte, PaperKind.special]
      constructor
      · intro ha
        simpa [hphase] using (htree a).mp (rawNode_tree hC ha)
      · rintro rfl
        exact h1

theorem raw_coding {C : Finset DiaryWord} (hC : ∀ w ∈ C, Point w)
    {j : Nat} {w : DiaryWord} (hlen : w.length = j) :
    w ∈ C ↔ w = critical j ∧ (kind C j).coded = true := by
  rw [kind_coded]
  constructor
  · intro hw
    have heq := ((point_at_level hlen).mp (hC w hw)).2
    exact ⟨heq, heq ▸ hw⟩
  · rintro ⟨rfl, hc⟩
    exact hc

theorem raw_children {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C) {j : Nat} (hj : j ∈ selected C v)
    {w : DiaryWord} (hw : RawNode C w) (hlen : w.length = j) (a : Fin 3) :
    RawNode C (child w a) ↔ localChild (critical j) (kind C j).special w a := by
  by_cases heq : w = critical j
  · subst w
    simpa [localChild] using raw_critical_children hC hv hj a
  · simpa only [localChild, heq, ite_false] using raw_noncritical_children hC hw hlen heq a

theorem continues_child {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C) {j : Nat} (hj : j ∈ selected C v)
    (hc : (kind C j).continues = true) : RawNode C (child (critical j) 1) := by
  apply (raw_critical_children hC hv hj 1).mpr
  cases hk : kind C j <;> simp_all [PaperKind.continues, PaperKind.special]

noncomputable def normalizedCritical (C : Finset DiaryWord) (v : DiaryWord) (i : Nat) : DiaryWord :=
  project (schedule (selected C v)) (critical (schedule (selected C v) i)) i

theorem normalized_critical {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C) {i : Nat} (hi : i < (selected C v).card) :
    normalizedCritical C v i ∈ nodes C v ∧
      inverse (C : Set Word) (schedule (selected C v)) (normalizedCritical C v i) =
        critical (schedule (selected C v) i) :=
  project_of_rawNode ⟨v, hv⟩ (selected_critical hC hv (schedule_mem hi)) (critical_length _)

@[simp] theorem normalizedCritical_length (C : Finset DiaryWord) (v : DiaryWord) (i : Nat) :
    (normalizedCritical C v i).length = i := project_length _ _ _

theorem normalized_level_data {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v)
    {i : Nat} (hi : i < (selected C v).card)
    {s : DiaryWord} (hs : s ∈ nodes C v) (hlen : s.length = i) :
    (s ∈ codes C v ↔ s = normalizedCritical C v i ∧
      (kind C (schedule (selected C v) i)).coded = true) ∧
    (∀ a, child s a ∈ nodes C v ↔
      localChild (normalizedCritical C v i) (kind C (schedule (selected C v) i)).special s a) := by
  have hne : C.Nonempty := ⟨v, hv⟩
  have hsp := spine hC (hC v hv) hmax
  obtain ⟨hq, hinvq⟩ := normalized_critical hC hv hi
  have hraw := inverse_rawNode hne hs
  have hrawlen : (inverse (C : Set Word) (schedule (selected C v)) s).length =
      schedule (selected C v) i := by rw [inverse_length hne hs, hlen]
  have heq : inverse (C : Set Word) (schedule (selected C v)) s =
      critical (schedule (selected C v) i) ↔ s = normalizedCritical C v i := by
    rw [← hinvq]
    exact ⟨inverse_injective hne hs hq, congrArg _⟩
  have hlt : inverse (C : Set Word) (schedule (selected C v)) s <
      critical (schedule (selected C v) i) ↔ s < normalizedCritical C v i := by
    rw [← hinvq]
    exact inverse_lt_iff hne hsp hs hq
  constructor
  · rw [code_iff_inverse hne hs, raw_coding hC hrawlen, heq]
  · intro a
    rw [child_iff_rawChild hne hs, raw_children hC hv (schedule_mem hi) hraw hrawlen]
    simp only [localChild, heq, hlt]

theorem raw_one_on_spine {C : Finset DiaryWord} {v p : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v)
    (hp : RawNode C (child p 1)) : (child p 1).IsPrefix v := by
  obtain ⟨w, hw, tail, htail⟩ := hp
  apply Sparse.fin_one_prefix_on_spine (hC w hw) (hC v hv) (hmax w hw)
  simpa only [child, List.append_assoc, List.singleton_append] using htail.symm

theorem raw_one_letter {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v)
    {j : Nat} (hchild : RawNode C (child (critical j) 1)) : v[j]? = some 1 := by
  obtain ⟨tail, htail⟩ := raw_one_on_spine hC hv hmax hchild
  rw [← htail]
  have hlookup : ((critical j) ++ 1 :: tail)[(critical j).length]? = some 1 := by simp
  simpa only [child, List.append_assoc, List.singleton_append, critical_length] using hlookup

theorem kind_initial_not_turn {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C) :
    kind C (schedule (selected C v) 0) ≠ .turn := by
  have hL := selected_nonempty ⟨v, hv⟩ v
  have hi : 0 < (selected C v).card := Finset.card_pos.mpr hL
  intro ht
  obtain ⟨p, hp, hpj, _, _⟩ := turn_previous ((kind_turn_iff hC (schedule_mem hi)).mp ht)
  have hpL := essential_subset_selected C v hp
  have hlt : rank (selected C v) p < 0 := (schedule_strict hL).lt_iff_lt.mp (by
    simpa only [schedule_rank hpL] using hpj)
  omega

theorem kind_allows_of_essential {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v)
    {j : Nat} (hj : j ∈ essential C) (hvj : v[j]? ≠ some 1) :
    (kind C j).allowsTurn = true := by
  classical
  by_cases hc : critical j ∈ C
  · have hn1 : ¬ RawNode C (child (critical j) 1) :=
      fun h1 => hvj (raw_one_letter hC hv hmax h1)
    simp [kind, hc, hn1, PaperKind.allowsTurn]
  · have hf : ForkAt C j := (essential_cases hC hj).resolve_left hc
    simp [kind, hc, hf, PaperKind.allowsTurn]

theorem kind_following {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v)
    {i : Nat} (hi : i+1 < (selected C v).card)
    (ht : kind C (schedule (selected C v) (i+1)) = .turn) :
    (kind C (schedule (selected C v) i)).allowsTurn = true := by
  have hL := selected_nonempty ⟨v, hv⟩ v
  obtain ⟨p, hp, hpj, hvp, hprev⟩ := turn_previous ((kind_turn_iff hC (schedule_mem hi)).mp ht)
  have hpL := essential_subset_selected C v hp
  have hpi : p = schedule (selected C v) i := by
    rcases lt_trichotomy p (schedule (selected C v) i) with hp0 | hp0 | hp0
    · exact (hprev _ (schedule_mem (by omega : i < (selected C v).card)) hp0
        (schedule_strict hL (Nat.lt_succ_self i))).elim
    · exact hp0
    · exact (schedule_no_between hL hpL hp0 hpj).elim
  apply kind_allows_of_essential hC hv hmax
  · exact hpi ▸ hp
  · exact hpi ▸ hvp

theorem raw_leftmost {C : Finset DiaryWord} {v p : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v)
    (hp : RawNode C p) (hlen : p.length ≤ v.length) : v.take p.length ≤ p := by
  obtain ⟨w, hw, hpre⟩ := hp
  have h := Sparse.fin_prefix_leftmost (hC w hw) (hC v hv) (hmax w hw)
    p.length hpre.length_le hlen
  simpa only [← List.prefix_iff_eq_take.mp hpre] using h

theorem selected_letter_not_two {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v)
    {j : Nat} (hj : j ∈ selected C v) (hjv : j < v.length) : v[j] ≠ 2 := by
  have hcrit := selected_critical hC hv hj
  have hmin : v.take j ≤ critical j := by
    simpa only [critical_length] using raw_leftmost hC hv hmax hcrit
      (by simpa only [critical_length] using hjv.le)
  have hnode : RawNode C (v.take j) := ⟨v, hv, List.take_prefix _ _⟩
  have hchild := raw_child_at hv hjv
  have hallowed := (tree_children j (v.take j) (rawNode_tree hC hnode)
    (by simp [hjv.le]) v[j]).mp (rawNode_tree hC hchild)
  by_cases heq : v.take j = critical j
  · rcases mem_selected_iff.mp hj with he | ht
    · rcases essential_cases hC he with hc | hf
      · have hphase := ((point_at_level (critical_length j)).mp (hC _ hc)).1
        have hOne : v[j] = 1 := by simpa only [heq, hphase, ite_true] using hallowed
        simp [hOne]
      · have h0 := (fork_critical hC hf).2.2.1
        have hmin0 := raw_leftmost hC hv hmax h0 (by simp [child, critical_length]; omega)
        intro htwo
        have hvnext : v.take (j+1) = child (critical j) 2 := by
          rw [List.take_succ_eq_append_getElem hjv, heq, htwo]
          rfl
        have hle : child (critical j) 2 ≤ child (critical j) 0 := by
          simpa only [child, List.length_append, List.length_singleton, critical_length, hvnext]
            using hmin0
        exact not_le_of_gt (child_lt_same (critical j) (by decide : (0 : Fin 3) < 2)) hle
    · obtain ⟨p, hp, hpj, he, hvp, hvj, hfirst⟩ := ht
      have hOne : v[j] = 1 := (List.getElem?_eq_some_iff.mp hvj).2
      simp [hOne]
  · have hlt : v.take j < critical j := lt_of_le_of_ne hmin heq
    have hzero : v[j] = 0 := by simpa only [heq, hlt, ite_false, ite_true] using hallowed
    simp [hzero]

theorem project_spine_original {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v)
    {i : Nat} (hi : i < (selected C v).card)
    (hlen : schedule (selected C v) i ≤ v.length) :
    (2 : Fin 3) ∉ project (schedule (selected C v)) v i := by
  intro hmem
  obtain ⟨k, hk, hget⟩ := List.mem_iff_getElem.mp hmem
  have hki : k < i := by simpa using hk
  have hkv : schedule (selected C v) k < v.length :=
    lt_of_lt_of_le (schedule_strict (selected_nonempty ⟨v, hv⟩ v) hki) hlen
  have htwo : v[schedule (selected C v) k] = 2 := by
    simpa only [project_get _ _ hki, List.getElem?_eq_getElem hkv, Option.getD_some] using hget
  exact selected_letter_not_two hC hv hmax (schedule_mem (lt_trans hki hi)) hkv htwo

theorem normalized_original {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v)
    {i : Nat} (hi : i < (selected C v).card)
    (hc : (kind C (schedule (selected C v) i)).continues = true) :
    (2 : Fin 3) ∉ normalizedCritical C v i := by
  have hchild := continues_child hC hv (schedule_mem hi) hc
  have hpre := raw_one_on_spine hC hv hmax hchild
  have hparent : (critical (schedule (selected C v) i)).IsPrefix v :=
    (List.prefix_append _ [1]).trans hpre
  have hlen : schedule (selected C v) i ≤ v.length := by
    simpa only [critical_length] using hparent.length_le
  have htake : (critical (schedule (selected C v) i)).take (schedule (selected C v) i) =
      v.take (schedule (selected C v) i) := by
    have h := List.prefix_iff_eq_take.mp hparent
    rw [List.take_of_length_le (by simp only [critical_length]; exact le_rfl)]
    simpa only [critical_length] using h
  have hproj := project_eq_of_take_eq (schedule_strict (selected_nonempty ⟨v, hv⟩ v)) htake
  change (2 : Fin 3) ∉ project (schedule (selected C v)) (critical (schedule (selected C v) i)) i
  rw [hproj]
  exact project_spine_original hC hv hmax hi hlen

theorem normalized_level {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v)
    {i : Nat} (hi : i < (selected C v).card) :
    PaperLevel (nodes C v) (codes C v) i (kind C (schedule (selected C v) i))
      (normalizedCritical C v i) where
  critical_mem := (normalized_critical hC hv hi).1
  critical_length := normalizedCritical_length C v i
  coding := fun _ hs hlen => (normalized_level_data hC hv hmax hi hs hlen).1
  children := fun _ hs hlen => (normalized_level_data hC hv hmax hi hs hlen).2
  original := normalized_original hC hv hmax hi

/-- All raw finite-set diary axioms follow for the explicit selected-level
projection of a finite chain in the actual sparse set. -/
theorem normalized_axioms {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v) :
    PaperTreeAxioms (nodes C v) (codes C v) (selected C v).card where
  height_pos := Finset.card_pos.mpr (selected_nonempty ⟨v, hv⟩ v)
  bounded := fun _ hw => nodes_bounded hw
  prefix_closed := fun _ hw _ hj => nodes_prefix_closed hw hj
  code_subset := codes_subset_nodes C v
  level := fun i hi => ⟨_, _, normalized_level hC hv hmax hi⟩
  initial := by
    intro c P
    have hpos := Finset.card_pos.mpr (selected_nonempty ⟨v, hv⟩ v)
    have heq := (PaperLevel.unique (normalized_level hC hv hmax hpos) P).2
    exact kind_initial_not_turn hC hv heq
  following := by
    intro i c pk p P Q
    have hi : i+1 < (selected C v).card := by
      simpa only [P.critical_length] using nodes_bounded P.critical_mem
    have ht := (PaperLevel.unique (normalized_level hC hv hmax hi) P).2
    have hprev := (PaperLevel.unique Q (normalized_level hC hv hmax (by omega))).2
    rw [hprev]
    exact kind_following hC hv hmax hi ht

/-- The sparse-chain diary is an explicitly defined finite pair of word
sets, whose axioms have been proved above. -/
noncomputable def normalize {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v) : PaperDiary C.card where
  nodes := nodes C v
  codes := codes C v
  axioms := ⟨_, normalized_axioms hC hv hmax⟩
  size := codes_card ⟨v, hv⟩

@[simp] theorem normalize_nodes {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v) :
    (normalize hC hv hmax).nodes = nodes C v := rfl

@[simp] theorem normalize_codes {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v) :
    (normalize hC hv hmax).codes = codes C v := rfl

/-- Actual extraction with a total ray-preserving realization. The total
map is the explicit prefix inverse completed by zero padding. -/
theorem extraction {C : Finset DiaryWord} {v : DiaryWord}
    (hC : ∀ w ∈ C, Point w) (hv : v ∈ C)
    (hmax : ∀ w ∈ C, DiaryChains.model w ≤ DiaryChains.model v) :
    ∃ f : RayStrongMap, (normalize hC hv hmax).codes.image f.map = C := by
  classical
  exact ⟨rayMap ⟨v, hv⟩ (spine hC (hC v hv) hmax), rayMap_codes ⟨v, hv⟩ (spine hC (hC v hv) hmax)⟩

end AllThoseBigRamsey.Pseudotree.SparseNormalization
