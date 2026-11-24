import PseudotreeValidation.DiaryRecoveryMaximum

/-!
# Canonical diaries are fixed by explicit normalization

Every level in the paper's raw diary is either an essential coding/fork
level, or the uniquely retained turn immediately following one. Thus the
explicit normalization retains every coordinate of an already normalized
diary. The distinguished word is its actual pseudotree maximum.
-/

namespace AllThoseBigRamsey.Pseudotree.DiaryRecovery

open RayEmbeddings DiaryNormalization LevelProjection

private theorem code_child_mem {D : PaperDiary n} {height : Nat}
    (T : PaperTreeAxioms D.nodes D.codes height) {w : Word} (hw : w ∈ D.codes)
    {j : Nat} (hj : j < w.length) : child (w.take j) w[j] ∈ D.nodes := by
  have hp := T.prefix_closed w (T.code_subset hw) (j+1) (by omega)
  simpa only [child, List.take_add_one, List.getElem?_eq_getElem hj,
    Option.toList_some] using hp

private theorem prefix_child_get {c w : Word} {a : Fin 3}
    (h : (child c a).IsPrefix w) : w[c.length]? = some a := by
  obtain ⟨tail, rfl⟩ := h
  simp [child]

/-- A split in the raw tree is witnessed by two actual coding descendants. -/
theorem split_essential {D : PaperDiary n} {height j : Nat} {c : Word}
    (_T : PaperTreeAxioms D.nodes D.codes height)
    (P : PaperLevel D.nodes D.codes j .split c) : j ∈ essential D.codes := by
  have h0 : child c 0 ∈ D.nodes :=
    (P.children c P.critical_mem P.critical_length 0).mpr (by
      simp [localChild, PaperKind.special])
  have h2 : child c 2 ∈ D.nodes :=
    (P.children c P.critical_mem P.critical_length 2).mpr (by
      simp [localChild, PaperKind.special])
  obtain ⟨s, hs, hcs⟩ := (D.nodes_iff_prefix_code _).mp h0
  obtain ⟨t, ht, hct⟩ := (D.nodes_iff_prefix_code _).mp h2
  have hjs : j < s.length := by
    have := hcs.length_le
    simp only [child, List.length_append, List.length_singleton, P.critical_length] at this
    omega
  have hjt : j < t.length := by
    have := hct.length_le
    simp only [child, List.length_append, List.length_singleton, P.critical_length] at this
    omega
  have hpreS : s.take j = c := by
    have hc : c.IsPrefix s := (List.prefix_append c [0]).trans hcs
    simpa only [P.critical_length] using (List.prefix_iff_eq_take.mp hc).symm
  have hpreT : t.take j = c := by
    have hc : c.IsPrefix t := (List.prefix_append c [2]).trans hct
    simpa only [P.critical_length] using (List.prefix_iff_eq_take.mp hc).symm
  apply fork_mem_essential
  refine ⟨s, hs, t, ht, hjs, hjt, hpreS.trans hpreT.symm, ?_⟩
  have hsget := prefix_child_get hcs
  have htget := prefix_child_get hct
  rw [P.critical_length] at hsget htget
  simp only [hsget, htget, ne_eq, Option.some.injEq]
  decide

theorem nonturn_essential {D : PaperDiary n} {height j : Nat} {c : Word}
    {kind : PaperKind} (T : PaperTreeAxioms D.nodes D.codes height)
    (P : PaperLevel D.nodes D.codes j kind c) (hk : kind ≠ .turn) :
    j ∈ essential D.codes := by
  cases kind with
  | split => exact split_essential T P
  | leaf =>
    have hc := (P.coding c P.critical_mem P.critical_length).mpr ⟨rfl, rfl⟩
    simpa only [P.critical_length] using length_mem_essential hc
  | code =>
    have hc := (P.coding c P.critical_mem P.critical_length).mpr ⟨rfl, rfl⟩
    simpa only [P.critical_length] using length_mem_essential hc
  | turn => exact (hk rfl).elim

/-- A turn has neither a coding node nor a fork at its level. -/
theorem turn_not_essential_source {D : PaperDiary n} {height j : Nat} {c : Word}
    (T : PaperTreeAxioms D.nodes D.codes height)
    (P : PaperLevel D.nodes D.codes j .turn c) : j ∉ essential D.codes := by
  intro he
  rcases mem_essential_iff.mp he with ⟨w, hw, hlen⟩ | hfork
  · have hc := (P.coding w (T.code_subset hw) hlen).mp hw
    simp [PaperKind.coded] at hc
  · obtain ⟨s, hs, t, ht, hjs, hjt, hpre, hne⟩ := hfork
    have hsnode : s.take j ∈ D.nodes := T.prefix_closed s (T.code_subset hs) j hjs.le
    have htchild := code_child_mem T ht hjt
    rw [← hpre] at htchild
    have ha := (P.children (s.take j) hsnode (by simp [hjs.le]) s[j]).mp
      (code_child_mem T hs hjs)
    have hb := (P.children (s.take j) hsnode (by simp [hjs.le]) t[j]).mp htchild
    have hab : s[j] = t[j] := by
      by_cases heq : s.take j = c
      · simp only [localChild, ite_eq_left heq, PaperKind.special] at ha hb
        exact ha.trans hb.symm
      · by_cases hlt : s.take j < c
        · simp only [localChild, ite_eq_right heq, ite_eq_left hlt] at ha hb
          exact ha.trans hb.symm
        · simp only [localChild, ite_eq_right heq, ite_eq_right hlt] at ha hb
          exact ha.trans hb.symm
    exact hne (by simp only [List.getElem?_eq_getElem hjs,
      List.getElem?_eq_getElem hjt, hab])

/-- A split or leaf level has no outgoing 1-edge anywhere in its frontier. -/
theorem allowsTurn_no_one {D : PaperDiary n} {height j : Nat} {c w : Word}
    {kind : PaperKind} (T : PaperTreeAxioms D.nodes D.codes height)
    (P : PaperLevel D.nodes D.codes j kind c) (hk : kind.allowsTurn = true)
    (hw : w ∈ D.codes) : w[j]? ≠ some 1 := by
  intro hget
  have hj := (List.getElem?_eq_some_iff.mp hget).1
  have hval : w[j] = 1 := by
    simpa only [List.getElem?_eq_getElem hj, Option.some.injEq] using hget
  have hnode := T.prefix_closed w (T.code_subset hw) j hj.le
  have hchild := code_child_mem T hw hj
  rw [hval] at hchild
  have ha := (P.children (w.take j) hnode (by simp [hj.le]) 1).mp hchild
  cases kind <;> by_cases heq : w.take j = c <;> by_cases hlt : w.take j < c <;>
    simp_all [PaperKind.allowsTurn, localChild, PaperKind.special]

/-- The maximum follows the 1-child of every turn, because that child has
a coding descendant below the maximum in the actual pseudotree order. -/
theorem turn_maximum_one {D : PaperDiary n} {j : Nat} {c v : Word}
    (P : PaperLevel D.nodes D.codes j .turn c) (hv : IsMaximum D.codes v) :
    v[j]? = some 1 := by
  have hchild : child c 1 ∈ D.nodes :=
    (P.children c P.critical_mem P.critical_length 1).mpr (by
      simp [localChild, PaperKind.special])
  obtain ⟨w, hw, hcw⟩ := (D.nodes_iff_prefix_code _).mp hchild
  have hget := prefix_child_get hcw
  rw [P.critical_length] at hget
  have heq := spine_of_maximum hv w hw j hget
  have hlast := congrArg (fun s : Word => s[j]?) heq
  simpa only [List.getElem?_take, Nat.lt_succ_self, ite_true, hget] using hlast.symm

theorem source_turnAt {D : PaperDiary n} {height j : Nat} {c v : Word}
    (T : PaperTreeAxioms D.nodes D.codes height)
    (P : PaperLevel D.nodes D.codes j .turn c) (hv : IsMaximum D.codes v) :
    TurnAt D.codes v j := by
  have hjpos : 0 < j := by
    by_contra h
    have hz : j = 0 := by omega
    subst j
    exact T.initial c P
  have hj : j < height := by simpa only [P.critical_length] using T.bounded c P.critical_mem
  obtain ⟨kind, previous, Q⟩ := T.level (j-1) (by omega)
  have hp : j-1+1 = j := by omega
  have hk : kind.allowsTurn = true := T.following (j-1) c kind previous (hp ▸ P) Q
  have hkind : kind ≠ .turn := by intro h; simp [h, PaperKind.allowsTurn] at hk
  refine ⟨j-1, nonturn_essential T Q hkind, by omega, ?_,
    allowsTurn_no_one T Q hk hv.1, turn_maximum_one P hv, ?_⟩
  · intro k hke hpk
    have hne : k ≠ j := by intro heq; subst k; exact turn_not_essential_source T P hke
    omega
  · intro k hpk hkj
    omega

/-- No coordinate is removed from an already normalized raw diary. -/
theorem selected_source {D : PaperDiary n} {height : Nat} {v : Word}
    (T : PaperTreeAxioms D.nodes D.codes height) (hv : IsMaximum D.codes v) :
    selected D.codes v = Finset.range height := by
  ext j
  rw [mem_selected_iff, Finset.mem_range]
  constructor
  · rintro (he | ht)
    · rcases mem_essential_iff.mp he with ⟨w, hw, rfl⟩ | ⟨w, hw, _, _, hj, _⟩
      · exact T.bounded w (T.code_subset hw)
      · exact lt_trans hj (T.bounded w (T.code_subset hw))
    · obtain ⟨_, _, _, _, _, hget, _⟩ := ht
      exact lt_trans (List.getElem?_eq_some_iff.mp hget).1 (T.bounded v (T.code_subset hv.1))
  · intro hj
    obtain ⟨kind, c, P⟩ := T.level j hj
    by_cases hk : kind = .turn
    · subst kind
      exact Or.inr (source_turnAt T P hv)
    · exact Or.inl (nonturn_essential T P hk)

theorem schedule_range {height i : Nat} (hi : i < height) :
    schedule (Finset.range height) i = i := by
  rw [schedule_at (by simpa using hi), Finset.orderEmbOfFin_apply]
  simp

theorem rank_range {height j : Nat} (hj : j < height) :
    rank (Finset.range height) j = j := by
  have hmem : j ∈ Finset.range height := Finset.mem_range.mpr hj
  have hr := rank_lt hmem
  have hs := schedule_rank hmem
  simpa only [schedule_range (by simpa using hr)] using hs

theorem project_source {D : PaperDiary n} {height : Nat} {v w : Word}
    (T : PaperTreeAxioms D.nodes D.codes height) (hv : IsMaximum D.codes v)
    (hw : w ∈ D.codes) :
    project (schedule (selected D.codes v)) w (rank (selected D.codes v) w.length) = w := by
  have hlen := T.bounded w (T.code_subset hw)
  rw [selected_source T hv, rank_range hlen]
  apply List.ext_getElem
  · simp only [project_length]
  · intro i hi hi'
    have hil : i < w.length := by simpa only [project_length] using hi
    rw [project_get _ _ hil, schedule_range (lt_trans hil hlen)]
    simp only [List.getElem?_eq_getElem hil, Option.getD_some]

/-- Explicit normalization is the identity on the paper's independently
specified finite-set diaries, using their actual pseudotree maximum. -/
theorem codes_source (D : PaperDiary n) (v : Word) (hv : IsMaximum D.codes v) :
    codes D.codes v = D.codes := by
  obtain ⟨height, T⟩ := D.axioms
  classical
  unfold codes
  ext w
  constructor
  · intro hw
    obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hw
    rw [project_source T hv hu] at heq
    exact heq ▸ hu
  · intro hw
    exact Finset.mem_image.mpr ⟨w, hw, project_source T hv hw⟩

/-- The normalized prefix tree is the original raw diary tree as well. -/
theorem nodes_source (D : PaperDiary n) (v : Word) (hv : IsMaximum D.codes v) :
    nodes D.codes v = D.nodes := by
  classical
  unfold nodes
  rw [codes_source D v hv]
  ext w
  rw [D.nodes_iff_prefix_code]
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨c, hc, j, hj, rfl⟩
    exact ⟨c, hc, List.take_prefix _ _⟩
  · rintro ⟨c, hc, hpre⟩
    exact ⟨c, hc, w.length, by have := hpre.length_le; omega,
      (List.prefix_iff_eq_take.mp hpre).symm⟩

end AllThoseBigRamsey.Pseudotree.DiaryRecovery
