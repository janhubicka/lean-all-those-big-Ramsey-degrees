import PseudotreeValidation.LowerLayers
import PseudotreeValidation.LowerSplit
import PseudotreeValidation.SparseLex

/-! Actual geometric one-level choices for lower-bound diary realization. -/

namespace AllThoseBigRamsey.Pseudotree.LowerRealization

open LowerGeometry
open scoped FirstOrder

private theorem binary_no_one (s : List Bool) : TernaryLetter.one ∉ s.map binaryLetter := by
  intro h
  obtain ⟨b, _, hb⟩ := List.mem_map.mp h
  cases b <;> simp [binaryLetter] at hb

/-- Beyond its ray root, every prefix of a ray point leaves only binary
letters to the point. -/
theorem ray_prefix_binary (Q : RayCopy) (p : List TernaryLetter) (q : ℚ)
    (hroot : (rayRoot Q.stem).length ≤ p.length)
    (hp : p <+: fromBlocks (Q q)) :
    ∃ b : List TernaryLetter, .one ∉ b ∧ fromBlocks (Q q) = p ++ b := by
  have hprefix := hp
  obtain ⟨b, hb⟩ := hp
  have hr : rayRoot Q.stem <+: p := List.prefix_of_prefix_length_le
    (by rw [Q.fromBlocks_eq]; exact List.prefix_append _ _) hprefix hroot
  obtain ⟨a, ha⟩ := hr
  have heq : a ++ b = (Q.coordinates q).word.map binaryLetter := by
    rw [← ha, Q.fromBlocks_eq, List.append_assoc] at hb
    exact List.append_cancel_left hb
  refine ⟨b, ?_, hb.symm⟩
  intro h
  have hnot := binary_no_one (Q.coordinates q).word
  apply hnot
  rw [← heq]
  exact List.mem_append_right a h

/-- A prefix of a binary extension is itself a binary extension. -/
theorem binary_prefix_between {p v w : List TernaryLetter}
    (hpv : p <+: v) (hvw : v <+: w)
    (hw : ∃ b : List TernaryLetter, .one ∉ b ∧ w = p ++ b) :
    ∃ b : List TernaryLetter, .one ∉ b ∧ v = p ++ b := by
  obtain ⟨b, hb⟩ := hpv
  obtain ⟨c, hc, rfl⟩ := hw
  have hbc : b <+: c := by
    rw [← hb] at hvw
    exact (List.prefix_append_right_inj p).mp hvw
  exact ⟨b, fun h => hc (hbc.subset h), hb.symm⟩

theorem inTree_of_sparse {w : List TernaryLetter} (hw : Sparse.InSparse w) :
    Sparse.InTree w := by
  obtain ⟨n, rfl⟩ := (Sparse.inSparse_iff_code w).mp hw
  exact ⟨n, List.prefix_refl _⟩

/-- Two occupied children locate the actual critical fork, rather than an
abstract branching point. -/
theorem fork_critical {v : List TernaryLetter}
    (h0 : Sparse.InTree (v ++ [.zero])) (h2 : Sparse.InTree (v ++ [.two])) :
    v = Sparse.critical v.length := by
  have hv := Sparse.inTree_prefix h0 (List.prefix_append _ _)
  have hc0 := (Sparse.critical_children v.length v hv rfl .zero).mp h0
  have hc2 := (Sparse.critical_children v.length v hv rfl .two).mp h2
  by_cases h : v = Sparse.critical v.length
  · exact h
  · simp only [Sparse.CriticalChildren, h, ↓reduceIte] at hc0 hc2
    have hbad := hc0.trans hc2.symm
    contradiction

/-- The geometric data for the selected critical node at one source level. -/
structure CriticalChoice {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} (P : Layer D f j) (kind : PaperKind) (c : Level D j) where
  word : List TernaryLetter
  binary : ∃ b : List TernaryLetter, .one ∉ b ∧ word = P.prefixes c ++ b
  critical : word = Sparse.critical word.length
  coding : kind.coded = true → toBlocks word ∈ Set.range f
  children : ∀ a : Fin 3, kind.special a → ∃ R : RayCopy,
    Set.range R.embedding ⊆ Set.range f ∧ ∀ q, ∃ b : List TernaryLetter,
      fromBlocks (R q) = word ++ RayMapModel.toLetter a :: b ∧ (a ≠ 1 → .one ∉ b)

/-- All four critical events are produced inside the actual self-copy by the
proved split and opposite-cone constructions. -/
theorem critical_choice {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} (P : Layer D f j)
    (hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x))
    (kind : PaperKind) (c : Level D j) : Nonempty (CriticalChoice P kind c) := by
  classical
  have hsQ : ∀ q, Sparse.InSparse (fromBlocks (P.copies c q)) :=
    fun q => hsparse _ (P.inside c ⟨q, rfl⟩)
  have choosePoint : ∃ v : List TernaryLetter,
      (∃ b : List TernaryLetter, .one ∉ b ∧ v = P.prefixes c ++ b) ∧
      v = Sparse.critical v.length ∧ toBlocks v ∈ Set.range f ∧
      v = fromBlocks (P.copies c 0) := by
    let v := fromBlocks (P.copies c 0)
    refine ⟨v, ray_prefix_binary (P.copies c) (P.prefixes c) 0
      (by rw [P.prefix_length]; exact (P.root_short c).le) (P.common_prefix c 0), ?_, ?_, rfl⟩
    · exact ((Sparse.inSparse_at_level v.length v rfl).mp (hsQ 0)).2
    · simpa only [v, toBlocks_fromBlocks] using P.inside c ⟨0, rfl⟩
  cases kind with
  | split =>
      obtain ⟨v, Q0, Q2, hpv, h0stem, h2stem, h0range, h2range, h0, h2⟩ :=
        (P.copies c).sparse_split hsQ (P.prefixes c) (P.common_prefix c)
          (by rw [P.prefix_length]; exact (P.root_short c).le)
      have h0S : Set.range Q0.embedding ⊆ Set.range f := h0range.trans (P.inside c)
      have h2S : Set.range Q2.embedding ⊆ Set.range f := h2range.trans (P.inside c)
      obtain ⟨b0, hb0, he0⟩ := h0 0
      obtain ⟨b2, hb2, he2⟩ := h2 0
      have hv0 : v ++ [.zero] <+: fromBlocks (Q0 0) := ⟨b0, by simpa using he0.symm⟩
      have hv2 : v ++ [.two] <+: fromBlocks (Q2 0) := ⟨b2, by simpa using he2.symm⟩
      have hcrit := fork_critical
        (Sparse.inTree_prefix (inTree_of_sparse (hsparse _ (h0S ⟨0, rfl⟩))) hv0)
        (Sparse.inTree_prefix (inTree_of_sparse (hsparse _ (h2S ⟨0, rfl⟩))) hv2)
      obtain ⟨q, hq⟩ := h0range ⟨0, rfl⟩
      have hvQ : v <+: fromBlocks (P.copies c q) := by
        rw [hq]
        exact (List.prefix_append v [.zero]).trans hv0
      refine ⟨{
        word := v
        binary := binary_prefix_between hpv hvQ
          (ray_prefix_binary (P.copies c) (P.prefixes c) q
            (by rw [P.prefix_length]; exact (P.root_short c).le) (P.common_prefix c q))
        critical := hcrit
        coding := by simp [PaperKind.coded]
        children := ?_
      }⟩
      intro a ha
      rcases ha with rfl | rfl
      · exact ⟨Q0, h0S, fun q => by
          obtain ⟨b, hb, he⟩ := h0 q
          exact ⟨b, he, fun _ => hb⟩⟩
      · exact ⟨Q2, h2S, fun q => by
          obtain ⟨b, hb, he⟩ := h2 q
          exact ⟨b, he, fun _ => hb⟩⟩
  | leaf =>
      obtain ⟨v, hv, hcrit, hmem, _⟩ := choosePoint
      exact ⟨⟨v, hv, hcrit, fun _ => hmem, fun _ h => False.elim h⟩⟩
  | code =>
      obtain ⟨v, hv, hcrit, hmem, heq⟩ := choosePoint
      obtain ⟨R, hR, hturn⟩ := (P.copies c).opposite_continuation f (P.inside c) 0
      refine ⟨⟨v, hv, hcrit, fun _ => hmem, ?_⟩⟩
      intro a ha
      have ha' : a = 1 := ha
      subst a
      refine ⟨R, hR, fun q => ?_⟩
      obtain ⟨b, hb⟩ := (hturn q).2
      refine ⟨b, ?_, by simp⟩
      change fromBlocks (R q) = v ++ .one :: b
      rw [heq]
      simpa only [List.append_assoc, List.singleton_append] using hb.symm
  | turn =>
      obtain ⟨v, hv, hcrit, _, heq⟩ := choosePoint
      obtain ⟨R, hR, hturn⟩ := (P.copies c).opposite_continuation f (P.inside c) 0
      refine ⟨⟨v, hv, hcrit, by simp [PaperKind.coded], ?_⟩⟩
      intro a ha
      have ha' : a = 1 := ha
      subst a
      refine ⟨R, hR, fun q => ?_⟩
      obtain ⟨b, hb⟩ := (hturn q).2
      refine ⟨b, ?_, by simp⟩
      change fromBlocks (R q) = v ++ .one :: b
      rw [heq]
      simpa only [List.append_assoc, List.singleton_append] using hb.symm

/-- Simultaneously refine a finite family of actual ray copies beyond a
prescribed level, keeping both their ambient rays and their original ranges. -/
theorem finite_common_prefix {I : Type} [Fintype I] (Q : I → RayCopy) (k : Nat) :
    ∃ L : Nat, k < L ∧ ∃ R : I → RayCopy, ∃ p : I → List TernaryLetter,
      (∀ i, (R i).stem = (Q i).stem) ∧
      (∀ i, Set.range (R i).embedding ⊆ Set.range (Q i).embedding) ∧
      (∀ i, (p i).length = L) ∧
      (∀ i q, p i <+: fromBlocks (R i q)) ∧
      (∀ i, (rayRoot (R i).stem).length < L) := by
  classical
  let L := k + 1 + Finset.univ.sup (fun i : I => (rayRoot (Q i).stem).length)
  have hroot (i : I) : (rayRoot (Q i).stem).length < L := by
    have hle := Finset.le_sup (s := Finset.univ)
      (f := fun i : I => (rayRoot (Q i).stem).length) (Finset.mem_univ i)
    omega
  have hchoice : ∀ i : I, ∃ R : RayCopy, R.stem = (Q i).stem ∧
      Set.range R.embedding ⊆ Set.range (Q i).embedding ∧
      ∃ p : List TernaryLetter, p.length = L ∧ ∀ q, p <+: fromBlocks (R q) :=
    fun i => (Q i).common_prefix L (hroot i).le
  choose R hstem hsub p hlen hp using hchoice
  exact ⟨L, by omega, R, p, hstem, hsub, hlen, hp, fun i => by rw [hstem]; exact hroot i⟩

/-- Refine each old branch to a prefix just beyond the chosen critical level.
This makes the noncritical letter at that level visible. -/
structure OldRefinement {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} (P : Layer D f j) (k : Nat) where
  copies : Level D j → RayCopy
  prefixes : Level D j → List TernaryLetter
  same_stem : ∀ u, (copies u).stem = (P.copies u).stem
  inside : ∀ u, Set.range (copies u).embedding ⊆ Set.range (P.copies u).embedding
  length : ∀ u, (prefixes u).length = k + 1
  common : ∀ u q, prefixes u <+: fromBlocks (copies u q)
  binary : ∀ u, ∃ b : List TernaryLetter, .one ∉ b ∧ prefixes u = P.prefixes u ++ b

theorem old_refinement {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} (P : Layer D f j) (k : Nat) (hk : P.bound ≤ k) :
    Nonempty (OldRefinement P k) := by
  classical
  have hchoice : ∀ u : Level D j, ∃ R : RayCopy, R.stem = (P.copies u).stem ∧
      Set.range R.embedding ⊆ Set.range (P.copies u).embedding ∧
      ∃ p : List TernaryLetter, p.length = k + 1 ∧ ∀ q, p <+: fromBlocks (R q) := by
    intro u
    apply (P.copies u).common_prefix (k + 1)
    have h := P.root_short u
    omega
  choose R hstem hsub p hlen hp using hchoice
  refine ⟨⟨R, p, hstem, hsub, hlen, hp, ?_⟩⟩
  intro u
  obtain ⟨q, hq⟩ := hsub u ⟨0, rfl⟩
  have hold : P.prefixes u <+: fromBlocks (R u 0) := by
    rw [← hq]
    exact P.common_prefix u q
  have hpp : P.prefixes u <+: p u := List.prefix_of_prefix_length_le hold (hp u 0)
    (by rw [P.prefix_length, hlen]; omega)
  have hpQ : p u <+: fromBlocks (P.copies u q) := by rw [hq]; exact hp u 0
  exact binary_prefix_between hpp hpQ (ray_prefix_binary (P.copies u) (P.prefixes u) q
    (by rw [P.prefix_length]; exact (P.root_short u).le) (P.common_prefix u q))

noncomputable def chosenRoot {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) (O : OldRefinement P C.word.length) (u : Level D j) :
    List TernaryLetter := if u = c then C.word else (O.prefixes u).dropLast

@[simp] theorem chosenRoot_critical {D : PaperDiary n}
    {f : TernaryModel ↪[language] TernaryModel} {j : Nat} {P : Layer D f j}
    {kind : PaperKind} {c : Level D j} (C : CriticalChoice P kind c)
    (O : OldRefinement P C.word.length) : chosenRoot C O c = C.word := by
  simp [chosenRoot]

theorem critical_length_ge {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) : P.bound ≤ C.word.length := by
  obtain ⟨b, _, hb⟩ := C.binary
  rw [hb, List.length_append, P.prefix_length]
  omega

theorem chosenRoot_length {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) (O : OldRefinement P C.word.length) (u : Level D j) :
    (chosenRoot C O u).length = C.word.length := by
  by_cases h : u = c
  · simp [chosenRoot, h]
  · simp [chosenRoot, h, O.length]

theorem chosenRoot_binary {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) (O : OldRefinement P C.word.length) (u : Level D j) :
    ∃ b : List TernaryLetter, .one ∉ b ∧ chosenRoot C O u = P.prefixes u ++ b := by
  by_cases h : u = c
  · subst u
    simpa only [chosenRoot_critical] using C.binary
  · obtain ⟨b, hb, heq⟩ := O.binary u
    have hbne : b ≠ [] := by
      intro hnil
      have hlen := O.length u
      rw [heq, hnil, List.append_nil, P.prefix_length] at hlen
      have hk := critical_length_ge C
      omega
    refine ⟨b.dropLast, fun hmem => hb ((List.dropLast_prefix b).subset hmem), ?_⟩
    simp only [chosenRoot, h, ↓reduceIte, heq, List.dropLast_append_of_ne_nil hbne]

theorem chosenRoot_ordered {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) (O : OldRefinement P C.word.length)
    (u v : Level D j) (huv : u.val < v.val) :
    Sparse.lexLess (chosenRoot C O u) (chosenRoot C O v) = true := by
  obtain ⟨b, _, hb⟩ := chosenRoot_binary C O u
  obtain ⟨d, _, hd⟩ := chosenRoot_binary C O v
  have hne : P.prefixes u ≠ P.prefixes v := by
    intro h
    have hlt := P.ordered u v huv
    rw [h, Sparse.lexLess_self] at hlt
    contradiction
  rw [hb, hd, Sparse.lexLess_append_of_ne ((P.prefix_length u).trans (P.prefix_length v).symm) hne]
  exact P.ordered u v huv

/-- The future rational candidates above a noncritical node have exactly the
forced sparse-tree letter at the newly selected level. -/
theorem noncritical_child {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} {P : Layer D f j} {kind : PaperKind} {c : Level D j}
    (C : CriticalChoice P kind c) (O : OldRefinement P C.word.length)
    (hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x))
    (LP : PaperLevel D.nodes D.codes j kind c.val)
    (u : Level D j) (hne : u ≠ c) (a : Fin 3) (ha : child u.val a ∈ D.nodes) :
    ∀ q, ∃ b : List TernaryLetter,
      fromBlocks (O.copies u q) = chosenRoot C O u ++ RayMapModel.toLetter a :: b ∧
      (a ≠ 1 → .one ∉ b) := by
  classical
  have hune : u.val ≠ c.val := fun h => hne (Subtype.ext h)
  have hsour := (LP.children u.val u.property.1 u.property.2 a).mp ha
  have hpnil : O.prefixes u ≠ [] := by
    intro h
    have hl := O.length u
    rw [h] at hl
    simp at hl
  let letter := (O.prefixes u).getLast hpnil
  have hdecomp : chosenRoot C O u ++ [letter] = O.prefixes u := by
    simpa only [chosenRoot, hne, ↓reduceIte, letter] using List.dropLast_concat_getLast hpnil
  have hprefixTree : Sparse.InTree (O.prefixes u) :=
    Sparse.inTree_prefix
      (inTree_of_sparse (hsparse _ (P.inside u (O.inside u ⟨0, rfl⟩)))) (O.common u 0)
  have hrootTree : Sparse.InTree (chosenRoot C O u) :=
    Sparse.inTree_prefix hprefixTree (by rw [← hdecomp]; exact List.prefix_append _ _)
  have hrootne : chosenRoot C O u ≠ C.word := by
    intro heq
    rcases lt_or_gt_of_ne hune with h | h
    · have hlt := chosenRoot_ordered C O u c h
      rw [chosenRoot_critical, heq, Sparse.lexLess_self] at hlt
      contradiction
    · have hlt := chosenRoot_ordered C O c u h
      rw [chosenRoot_critical, heq, Sparse.lexLess_self] at hlt
      contradiction
  have hactual : letter = Sparse.direction C.word (chosenRoot C O u) := by
    have hh := (Sparse.critical_children C.word.length (chosenRoot C O u) hrootTree
      (chosenRoot_length C O u) letter).mp (hdecomp ▸ hprefixTree)
    rw [← C.critical] at hh
    simpa only [Sparse.CriticalChildren, hrootne, ↓reduceIte] using hh
  have hletter : letter = RayMapModel.toLetter a := by
    by_cases hlt : u.val < c.val
    · have hzero : a = 0 := by simpa only [localChild, hune, hlt, ↓reduceIte] using hsour
      have hlex : Sparse.lexLess (chosenRoot C O u) C.word = true := by
        simpa only [chosenRoot_critical] using chosenRoot_ordered C O u c hlt
      rw [hactual, Sparse.direction, hlex]
      subst a
      rfl
    · have htwo : a = 2 := by simpa only [localChild, hune, hlt, ↓reduceIte] using hsour
      have hcu : c.val < u.val := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hune)
      have hlex : Sparse.lexLess C.word (chosenRoot C O u) = true := by
        simpa only [chosenRoot_critical] using chosenRoot_ordered C O c u hcu
      rw [hactual, Sparse.direction, Sparse.lexLess_asymm hlex]
      subst a
      rfl
  intro q
  obtain ⟨b, hb, heq⟩ := ray_prefix_binary (O.copies u) (O.prefixes u) q
    (by rw [O.same_stem, O.length]; have h := P.root_short u; have hk := critical_length_ge C; omega)
    (O.common u q)
  refine ⟨b, ?_, fun _ => hb⟩
  rw [heq, ← hdecomp, hletter]
  simp

/-- Old-level images and actual rational candidate copies for every allowed
next child, before synchronizing their next prefixes. -/
structure RootChoices {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} (P : Layer D f j) where
  level : Nat
  lower : P.bound ≤ level
  roots : Level D j → List TernaryLetter
  length : ∀ u, (roots u).length = level
  binary : ∀ u, ∃ b : List TernaryLetter, .one ∉ b ∧ roots u = P.prefixes u ++ b
  ordered : ∀ u v, u.val < v.val → Sparse.lexLess (roots u) (roots v) = true
  coding : ∀ u, u.val ∈ D.codes → toBlocks (roots u) ∈ Set.range f
  children : ∀ u a (ha : child u.val a ∈ D.nodes), ∃ R : RayCopy,
    Set.range R.embedding ⊆ Set.range f ∧ ∀ q, ∃ b : List TernaryLetter,
      fromBlocks (R q) = roots u ++ RayMapModel.toLetter a :: b ∧ (a ≠ 1 → .one ∉ b)

/-- All one-level geometric choices, including forced noncritical letters,
come from the actual sparse construction. -/
theorem root_choices {D : PaperDiary n} {f : TernaryModel ↪[language] TernaryModel}
    {j : Nat} (P : Layer D f j)
    (hsparse : ∀ x ∈ Set.range f, Sparse.InSparse (fromBlocks x))
    {kind : PaperKind} {c : DiaryWord} (LP : PaperLevel D.nodes D.codes j kind c) :
    Nonempty (RootChoices P) := by
  classical
  let cp : Level D j := ⟨c, LP.critical_mem, LP.critical_length⟩
  obtain ⟨C⟩ := critical_choice P hsparse kind cp
  obtain ⟨O⟩ := old_refinement P C.word.length (critical_length_ge C)
  refine ⟨{
    level := C.word.length
    lower := critical_length_ge C
    roots := chosenRoot C O
    length := chosenRoot_length C O
    binary := chosenRoot_binary C O
    ordered := chosenRoot_ordered C O
    coding := ?_
    children := ?_
  }⟩
  · intro u hu
    obtain ⟨huc, hcode⟩ := (LP.coding u.val u.property.1 u.property.2).mp hu
    have heq : u = cp := Subtype.ext huc
    subst u
    simpa only [chosenRoot_critical] using C.coding hcode
  · intro u a ha
    by_cases heq : u = cp
    · subst u
      have hspecial : kind.special a := by
        have h := (LP.children c LP.critical_mem LP.critical_length a).mp ha
        simpa only [localChild, ↓reduceIte] using h
      simpa only [chosenRoot_critical] using C.children a hspecial
    · exact ⟨O.copies u, (O.inside u).trans (P.inside u),
        noncritical_child C O hsparse LP u heq a ha⟩

end AllThoseBigRamsey.Pseudotree.LowerRealization
