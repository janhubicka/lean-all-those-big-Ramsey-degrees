import PseudotreeValidation.LevelProjection

/-!
# The explicit normalization levels of a finite coding set

Essential levels are coding endpoints and first disagreements. Between
successive essential levels we retain the first 1 on the distinguished
branch, precisely when that interval did not start with 1. The definitions
are finite-set operations, not a choice of a pre-existing diary.
-/

namespace AllThoseBigRamsey.Pseudotree.DiaryNormalization

open RayEmbeddings LevelProjection

/-- A genuine fork of the prefix closure of the coding set. -/
def ForkAt (C : Finset Word) (k : Nat) : Prop :=
  ∃ s ∈ C, ∃ t ∈ C, k < s.length ∧ k < t.length ∧
    s.take k = t.take k ∧ s[k]? ≠ t[k]?

noncomputable def essential (C : Finset Word) : Finset Nat := by
  classical
  exact C.image List.length ∪ (Finset.range (C.sup List.length)).filter (ForkAt C)

theorem length_mem_essential {C : Finset Word} {w : Word} (hw : w ∈ C) :
    w.length ∈ essential C := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨w, hw, rfl⟩)

theorem fork_mem_essential {C : Finset Word} {k : Nat} (hk : ForkAt C k) :
    k ∈ essential C := by
  classical
  have hfork := hk
  obtain ⟨s, hs, _, _, hks, _⟩ := hk
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (lt_of_lt_of_le hks (Finset.le_sup hs)), hfork⟩)

theorem mem_essential_iff {C : Finset Word} {k : Nat} :
    k ∈ essential C ↔ (∃ w ∈ C, w.length = k) ∨ ForkAt C k := by
  classical
  constructor
  · intro hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact Or.inl (Finset.mem_image.mp hk)
    · exact Or.inr (Finset.mem_filter.mp hk).2
  · rintro (⟨w, hw, rfl⟩ | hk)
    · exact length_mem_essential hw
    · exact fork_mem_essential hk

theorem essential_nonempty {C : Finset Word} (hC : C.Nonempty) : (essential C).Nonempty := by
  obtain ⟨w, hw⟩ := hC
  exact ⟨w.length, length_mem_essential hw⟩

theorem essential_le {C : Finset Word} {k : Nat} (hk : k ∈ essential C) :
    k ≤ C.sup List.length := by
  rcases mem_essential_iff.mp hk with ⟨w, hw, rfl⟩ | hk
  · exact Finset.le_sup hw
  · obtain ⟨w, hw, _, _, hkw, _⟩ := hk
    exact le_trans hkw.le (Finset.le_sup hw)

/-- The unique possible extra level in an essential interval. The explicit
witness `p` is its immediately preceding essential level. -/
def TurnAt (C : Finset Word) (v : Word) (j : Nat) : Prop :=
  ∃ p ∈ essential C, p < j ∧
    (∀ k ∈ essential C, p < k → j < k) ∧
    v[p]? ≠ some 1 ∧ v[j]? = some 1 ∧
    (∀ k, p < k → k < j → v[k]? ≠ some 1)

noncomputable def selected (C : Finset Word) (v : Word) : Finset Nat := by
  classical
  exact essential C ∪ (Finset.range v.length).filter (TurnAt C v)

theorem essential_subset_selected (C : Finset Word) (v : Word) :
    essential C ⊆ selected C v := Finset.subset_union_left

theorem turn_mem_selected {C : Finset Word} {v : Word} {j : Nat} (hj : TurnAt C v j) :
    j ∈ selected C v := by
  classical
  have hlen : j < v.length := by
    obtain ⟨p, hp, hpj, he, hvp, hvj, hmin⟩ := hj
    exact List.getElem?_eq_some_iff.mp hvj |>.1
  exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hj⟩)

theorem mem_selected_iff {C : Finset Word} {v : Word} {j : Nat} :
    j ∈ selected C v ↔ j ∈ essential C ∨ TurnAt C v j := by
  classical
  constructor
  · intro hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact Or.inl hj
    · exact Or.inr (Finset.mem_filter.mp hj).2
  · rintro (hj | hj)
    · exact essential_subset_selected C v hj
    · exact turn_mem_selected hj

theorem selected_nonempty {C : Finset Word} (hC : C.Nonempty) (v : Word) :
    (selected C v).Nonempty := (essential_nonempty hC).mono (essential_subset_selected C v)

theorem essential_before_selected {C : Finset Word} {v : Word} {j : Nat}
    (hj : j ∈ selected C v) : ∃ p ∈ essential C, p ≤ j := by
  rcases mem_selected_iff.mp hj with hj | ⟨p, hp, hpj, _⟩
  · exact ⟨j, hj, le_rfl⟩
  · exact ⟨p, hp, hpj.le⟩

def levelAt (L : Finset Nat) (i : Nat) : Nat :=
  if hi : i < L.card then L.orderEmbOfFin rfl ⟨i, hi⟩ else 0

/-- The finite increasing list, extended linearly beyond its last entry.
Only values at selected nodes are used by normalization. -/
def schedule (L : Finset Nat) : Nat → Nat :=
  extendLevels L.card (levelAt L)

theorem schedule_at {L : Finset Nat} {i : Nat} (hi : i < L.card) :
    schedule L i = L.orderEmbOfFin rfl ⟨i, hi⟩ := by
  simp [schedule, extendLevels_agrees _ hi, levelAt, hi]

theorem schedule_mem {L : Finset Nat} {i : Nat} (hi : i < L.card) :
    schedule L i ∈ L := by
  rw [schedule_at hi]
  exact L.orderEmbOfFin_mem _ _

theorem schedule_strict {L : Finset Nat} (hL : L.Nonempty) : StrictMono (schedule L) := by
  apply extendLevels_strict (Finset.card_pos.mpr hL)
  intro i j hij hj
  have hi : i < L.card := lt_trans hij hj
  simp only [levelAt, hi, hj, dite_eq_left]
  exact (L.orderEmbOfFin rfl).strictMono hij

/-- A total rank function; membership lemmas ensure its relevant values are
valid indices in the selected set. -/
def rank (L : Finset Nat) (j : Nat) : Nat := (L.sort (· ≤ ·)).idxOf j

theorem rank_lt {L : Finset Nat} {j : Nat} (hj : j ∈ L) : rank L j < L.card := by
  simpa only [rank, Finset.length_sort] using List.idxOf_lt_length_iff.mpr
    ((Finset.mem_sort (· ≤ ·)).mpr hj)

theorem schedule_rank {L : Finset Nat} {j : Nat} (hj : j ∈ L) :
    schedule L (rank L j) = j := by
  rw [schedule_at (rank_lt hj), Finset.orderEmbOfFin_apply]
  exact List.getElem_idxOf (by simpa only [Finset.length_sort, rank] using rank_lt hj)

theorem schedule_covers_essential (C : Finset Word) (v : Word) :
    Separates (C : Set Word) (schedule (selected C v)) := by
  intro s hs t ht k hks hkt hpre hne
  have hk : k ∈ selected C v := essential_subset_selected C v
    (fork_mem_essential ⟨s, hs, t, ht, hks, hkt, hpre, hne⟩)
  exact ⟨rank (selected C v) k, schedule_rank hk⟩

/-- The literal projected coding set. Its definition requires no proof that
it is a diary. -/
noncomputable def codes (C : Finset Word) (v : Word) : Finset Word := by
  classical
  exact C.image (fun w => project (schedule (selected C v)) w (rank (selected C v) w.length))

theorem schedule_index_le {L : Finset Nat} (hL : L.Nonempty) {i j : Nat}
    (hj : j ∈ L) (hij : schedule L i ≤ j) : i ≤ rank L j := by
  apply (schedule_strict hL).le_iff_le.mp
  simpa only [schedule_rank hj] using hij

theorem schedule_index_lt {L : Finset Nat} (hL : L.Nonempty) {i j : Nat}
    (hj : j ∈ L) (hij : schedule L i ≤ j) : i < L.card :=
  lt_of_le_of_lt (schedule_index_le hL hj hij) (rank_lt hj)

theorem schedule_no_between {L : Finset Nat} (hL : L.Nonempty) {i j : Nat}
    (hj : j ∈ L) (hlo : schedule L i < j) (hhi : j < schedule L (i+1)) : False := by
  have hlo' : i < rank L j := (schedule_strict hL).lt_iff_lt.mp (by
    simpa only [schedule_rank hj] using hlo)
  have hhi' : rank L j < i+1 := (schedule_strict hL).lt_iff_lt.mp (by
    simpa only [schedule_rank hj] using hhi)
  omega

/-- An omitted 1 forces the selected edge to begin with 1. All later 1s in
that same gap are therefore legal padding after a 1-edge. -/
theorem selected_gap_one {C : Finset Word} {v : Word} {p q j : Nat}
    (hp : p ∈ selected C v)
    (hgap : ∀ k ∈ selected C v, p < k → k < q → False)
    (hpj : p < j) (hjq : j < q) (hvj : v[j]? = some 1) : v[p]? = some 1 := by
  classical
  rcases mem_selected_iff.mp hp with hp | ⟨r, hr, hrp, he, hvr, hvp, hmin⟩
  · by_contra hvp
    have hex : ∃ k, p < k ∧ k < q ∧ v[k]? = some 1 := ⟨j, hpj, hjq, hvj⟩
    let m := Nat.find hex
    have hm := Nat.find_spec hex
    have hturn : TurnAt C v m := by
      refine ⟨p, hp, hm.1, ?_, hvp, hm.2.2, ?_⟩
      · intro k hk hpk
        by_contra hmk
        have hkq : k < q := lt_of_le_of_lt (Nat.le_of_not_gt hmk) hm.2.1
        exact hgap k (essential_subset_selected C v hk) hpk hkq
      · intro k hpk hkm hvk
        exact Nat.find_min hex hkm ⟨hpk, lt_trans hkm hm.2.1, hvk⟩
    exact hgap m (turn_mem_selected hturn) hm.1 hm.2.1
  · exact hvp

/-- Every 1 in a coding word is on the distinguished branch. This word
property is proved from the sparse-chain geometry, rather than assumed as
a diary or extraction property. -/
def Spine (C : Finset Word) (v : Word) : Prop :=
  ∀ w ∈ C, ∀ k, w[k]? = some 1 → w.take (k+1) = v.take (k+1)

theorem binaryGaps_of_spine {C : Finset Word} {v : Word} (hC : C.Nonempty)
    (hspine : Spine C v) : BinaryGaps (C : Set Word) (schedule (selected C v)) := by
  intro w hw i hlen hstart k hik hki hwk
  have hL := selected_nonempty hC v
  have hend : w.length ∈ selected C v :=
    essential_subset_selected C v (length_mem_essential hw)
  have hii : i < (selected C v).card :=
    lt_trans (Nat.lt_succ_self i) (schedule_index_lt hL hend hlen)
  have hp : schedule (selected C v) i ∈ selected C v := schedule_mem hii
  have hpre := hspine w hw k hwk
  have hvk : v[k]? = some 1 := by
    have h := congrArg (fun t : Word => t[k]?) hpre
    simpa [List.getElem?_take, Nat.lt_succ_self k, hwk] using h.symm
  have hvp := selected_gap_one hp
    (fun l hl hlo hhi => schedule_no_between hL hl hlo hhi) hik hki hvk
  have hwp := congrArg (fun t : Word => t[schedule (selected C v) i]?) hpre
  have hsmall : schedule (selected C v) i < k+1 := by omega
  have heq : w[schedule (selected C v) i]? = v[schedule (selected C v) i]? := by
    simpa [List.getElem?_take, hsmall] using hwp
  exact hstart (heq.trans hvp)

theorem root_bound {C : Finset Word} {v : Word} (hC : C.Nonempty) {w : Word} (hw : w ∈ C) :
    schedule (selected C v) 0 ≤ w.length := by
  have hm := (schedule_strict (selected_nonempty hC v)).monotone
    (Nat.zero_le (rank (selected C v) w.length))
  simpa only [schedule_rank (essential_subset_selected C v (length_mem_essential hw))] using hm

noncomputable def rayMap {C : Finset Word} {v : Word} (hC : C.Nonempty)
    (hspine : Spine C v) : RayStrongMap :=
  (prefixRayMap (schedule_strict (selected_nonempty hC v)) (schedule_covers_essential C v)
    (binaryGaps_of_spine hC hspine)
    (by obtain ⟨w, hw⟩ := hC; exact ⟨w, hw, root_bound ⟨w, hw⟩ hw⟩)).completion

theorem rayMap_code {C : Finset Word} {v : Word} (hC : C.Nonempty)
    (hspine : Spine C v) {w : Word} (hw : w ∈ C) :
    (rayMap hC hspine).map
      (project (schedule (selected C v)) w (rank (selected C v) w.length)) = w := by
  apply completion_project
  · exact hw
  · exact schedule_rank (essential_subset_selected C v (length_mem_essential hw))

/-- Projection does not lose coding nodes. This uses only fork/end-level
selection, so it precedes the sparse and diary arguments. -/
theorem code_projection_injective {C : Finset Word} {v : Word} (hC : C.Nonempty) :
    Set.InjOn (fun w => project (schedule (selected C v)) w (rank (selected C v) w.length))
      (C : Set Word) := by
  intro s hs t ht heq
  have hK := schedule_strict (selected_nonempty hC v)
  have hsep := schedule_covers_essential C v
  have hslen := schedule_rank (essential_subset_selected C v (length_mem_essential hs))
  have htlen := schedule_rank (essential_subset_selected C v (length_mem_essential ht))
  have h := congrArg (inverse (C : Set Word) (schedule (selected C v))) heq
  rw [inverse_project hK hsep hs hslen.le, inverse_project hK hsep ht htlen.le,
    hslen, htlen, List.take_length, List.take_length] at h
  exact h

theorem codes_card {C : Finset Word} {v : Word} (hC : C.Nonempty) :
    (codes C v).card = C.card := by
  classical
  exact Finset.card_image_of_injOn (code_projection_injective hC)

theorem rayMap_codes {C : Finset Word} {v : Word} (hC : C.Nonempty) (hspine : Spine C v) :
    (codes C v).image (rayMap hC hspine).map = C := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    simpa only [rayMap_code hC hspine hx] using hx
  · intro hw
    exact Finset.mem_image.mpr ⟨_, Finset.mem_image.mpr ⟨w, hw, rfl⟩, rayMap_code hC hspine hw⟩

theorem turn_not_essential {C : Finset Word} {v : Word} {j : Nat}
    (hj : TurnAt C v j) : j ∉ essential C := by
  obtain ⟨p, hp, hpj, he, _⟩ := hj
  intro hje
  exact Nat.lt_irrefl j (he j hje hpj)

theorem turn_previous {C : Finset Word} {v : Word} {j : Nat} (hj : TurnAt C v j) :
    ∃ p ∈ essential C, p < j ∧ v[p]? ≠ some 1 ∧
      ∀ k ∈ selected C v, p < k → k < j → False := by
  obtain ⟨p, hp, hpj, he, hvp, hvj, hfirst⟩ := hj
  refine ⟨p, hp, hpj, hvp, ?_⟩
  intro k hk hpk hkj
  rcases mem_selected_iff.mp hk with hk | ⟨q, hq, hqk, hqe, hvq, hvk, hqfirst⟩
  · have := he k hk hpk
    omega
  · rcases lt_trichotomy q p with hqp | rfl | hpq
    · have := hqe p hp hqp
      omega
    · exact hfirst k hpk hkj hvk
    · have := he q hq hpq
      omega

/-- Prefix closure of the explicitly projected coding set. -/
noncomputable def nodes (C : Finset Word) (v : Word) : Finset Word := by
  classical
  exact (codes C v).biUnion (fun w => (Finset.range (w.length+1)).image (fun j => w.take j))

theorem mem_nodes_iff {C : Finset Word} {v s : Word} :
    s ∈ nodes C v ↔ ∃ w ∈ C, ∃ j, j ≤ rank (selected C v) w.length ∧
      project (schedule (selected C v)) w j = s := by
  classical
  constructor
  · intro hs
    obtain ⟨u, hu, hs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    have hj' : j ≤ rank (selected C v) w.length := by
      simpa only [Finset.mem_range, project_length, Nat.lt_succ_iff] using hj
    exact ⟨w, hw, j, hj', (project_take _ _ hj').symm⟩
  · rintro ⟨w, hw, j, hj, rfl⟩
    refine Finset.mem_biUnion.mpr ⟨_, Finset.mem_image.mpr ⟨w, hw, rfl⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨j, by simpa using hj, project_take _ _ hj⟩

theorem mem_nodes_iff_domain {C : Finset Word} {v s : Word} (hC : C.Nonempty) :
    s ∈ nodes C v ↔ Domain (C : Set Word) (schedule (selected C v)) s := by
  constructor
  · intro hs
    obtain ⟨w, hw, j, hj, rfl⟩ := mem_nodes_iff.mp hs
    apply domain_project hw
    have h := (schedule_strict (selected_nonempty hC v)).monotone hj
    simpa only [schedule_rank (essential_subset_selected C v (length_mem_essential hw))] using h
  · rintro ⟨w, hw, hlen, heq⟩
    refine mem_nodes_iff.mpr ⟨w, hw, s.length, ?_, heq⟩
    exact schedule_index_le (selected_nonempty hC v)
      (essential_subset_selected C v (length_mem_essential hw)) hlen

theorem nodes_root {C : Finset Word} {v : Word} (hC : C.Nonempty) : [] ∈ nodes C v := by
  apply (mem_nodes_iff_domain hC).mpr
  obtain ⟨w, hw⟩ := hC
  exact domain_root ⟨w, hw, root_bound ⟨w, hw⟩ hw⟩

theorem nodes_prefix_closed {C : Finset Word} {v s : Word} (hs : s ∈ nodes C v)
    {j : Nat} (hj : j ≤ s.length) : s.take j ∈ nodes C v := by
  obtain ⟨w, hw, i, hi, rfl⟩ := mem_nodes_iff.mp hs
  have hj' : j ≤ i := by simpa using hj
  rw [project_take _ _ hj']
  exact mem_nodes_iff.mpr ⟨w, hw, j, le_trans hj' hi, rfl⟩

theorem codes_subset_nodes (C : Finset Word) (v : Word) : codes C v ⊆ nodes C v := by
  classical
  intro w hw
  change w ∈ C.image (fun x => project (schedule (selected C v)) x (rank (selected C v) x.length)) at hw
  obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hw
  rw [← heq]
  exact mem_nodes_iff.mpr ⟨x, hx, _, le_rfl, rfl⟩

theorem nodes_bounded {C : Finset Word} {v s : Word} (hs : s ∈ nodes C v) :
    s.length < (selected C v).card := by
  obtain ⟨w, hw, i, hi, rfl⟩ := mem_nodes_iff.mp hs
  simp only [project_length]
  exact lt_of_le_of_lt hi (rank_lt (essential_subset_selected C v (length_mem_essential hw)))

theorem project_of_node {C : Finset Word} {v s : Word} (hC : C.Nonempty)
    (hs : s ∈ nodes C v) :
    project (schedule (selected C v))
      (inverse (C : Set Word) (schedule (selected C v)) s) s.length = s := by
  obtain ⟨w, hw, hlen, heq⟩ := (mem_nodes_iff_domain hC).mp hs
  rw [inverse_eq (schedule_strict (selected_nonempty hC v))
    (schedule_covers_essential C v) hw hlen heq]
  have h := project_eq_of_take_eq (schedule_strict (selected_nonempty hC v))
    (s := w.take (schedule (selected C v) s.length)) (t := w) (j := s.length)
    (by simp)
  exact h.trans heq

end AllThoseBigRamsey.Pseudotree.DiaryNormalization
