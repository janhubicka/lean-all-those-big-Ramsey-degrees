import PseudotreeValidation.DiarySoundness
import PseudotreeValidation.WordModelMathlib
import AllThoseBigRamsey.Pseudotree.RayMapModel

/-! Literal diary nodes, and hence coding nodes, form actual pseudotree chains. -/

namespace AllThoseBigRamsey.Pseudotree.DiaryChains

open RayMapModel

/-- Every occurrence of 1 lies before the first occurrence of 2. -/
def OriginalOnes (s : DiaryWord) : Prop :=
  ∀ p t, s = p ++ 1 :: t → (2 : Fin 3) ∉ p

/-- Every first disagreement is the split 0/2 prescribed by the diary. -/
def SplitCompatible (s t : DiaryWord) : Prop :=
  ∀ p a b u v, s = p ++ a :: u → t = p ++ b :: v → a ≠ b →
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0)

theorem originalOnes_tail (hs : OriginalOnes (a :: s)) : OriginalOnes s := by
  intro p t heq
  have h := hs (a :: p) t (by simp [heq])
  exact fun hmem => h (List.mem_cons_of_mem _ hmem)

theorem originalOnes_two (hs : OriginalOnes (2 :: s)) : (1 : Fin 3) ∉ s := by
  intro hmem
  obtain ⟨p, t, heq⟩ := List.append_of_mem hmem
  have h := hs (2 :: p) t (by simp [heq])
  exact h (by simp)

theorem splitCompatible_tail (hs : SplitCompatible (a :: s) (a :: t)) : SplitCompatible s t := by
  intro p b c u v hu hv hbc
  exact hs (a :: p) b c u v (by simp [hu]) (by simp [hv]) hbc

private theorem noOne_point (s : List TernaryLetter) (hs : NoOne s) :
    ∃ b, parseWord s = .point b := by
  induction s with
  | nil => exact ⟨[], rfl⟩
  | cons a s ih =>
      obtain ⟨ha, hs⟩ := (noOne_cons a s).mp hs
      obtain ⟨b, hb⟩ := ih hs
      cases a with
      | zero => exact ⟨false :: b, by simp [parseWord, prependBlock, hb]⟩
      | one => exact (ha rfl).elim
      | two => exact ⟨true :: b, by simp [parseWord, prependBlock, hb]⟩

private theorem below_same (a : TernaryLetter) (s t : List TernaryLetter) :
    wordBelow (a :: s) (a :: t) ↔ wordBelow s t := by
  cases a <;> cases hs : parseWord s <;> cases ht : parseWord t <;>
    simp [wordBelow, parseWord, prependBlock, hs, ht, RayTree.Below, RayTree.first, binaryLE]

private theorem below_nil_zero (s : List TernaryLetter) : wordBelow [] (.zero :: s) := by
  cases h : parseWord s <;>
    simp [wordBelow, parseWord, prependBlock, h, RayTree.first, binaryLE]

private theorem below_nil_one (s : List TernaryLetter) : wordBelow [] (.one :: s) := by
  simp [wordBelow, parseWord, RayTree.first, binaryLE]

private theorem below_two_nil (s : List TernaryLetter) (hs : NoOne s) :
    wordBelow (.two :: s) [] := by
  obtain ⟨b, hb⟩ := noOne_point s hs
  simp [wordBelow, parseWord, prependBlock, hb, RayTree.first, binaryLE]

private theorem below_two_zero (s t : List TernaryLetter) (hs : NoOne s) :
    wordBelow (.two :: s) (.zero :: t) := by
  obtain ⟨b, hb⟩ := noOne_point s hs
  cases ht : parseWord t <;>
    simp [wordBelow, parseWord, prependBlock, hb, ht, RayTree.first, binaryLE]

theorem noOne_map_of_not_one {s : DiaryWord} (hs : (1 : Fin 3) ∉ s) : NoOne (s.map toLetter) := by
  rw [noOne_map]
  intro a ha heq
  exact hs (heq ▸ ha)

/-- The two local word restrictions imply comparability in the ACTUAL
block-defined pseudotree order. Prefix-related words are included. -/
theorem comparable (s t : DiaryWord) (hs : OriginalOnes s) (ht : OriginalOnes t)
    (hcompat : SplitCompatible s t) :
    wordBelow (s.map toLetter) (t.map toLetter) ∨
      wordBelow (t.map toLetter) (s.map toLetter) := by
  induction s generalizing t with
  | nil =>
      cases t with
      | nil => exact Or.inl (wordBelow_refl [])
      | cons a t =>
          fin_cases a
          · exact Or.inl (below_nil_zero _)
          · exact Or.inl (below_nil_one _)
          · exact Or.inr (below_two_nil _ (noOne_map_of_not_one (originalOnes_two ht)))
  | cons a s ih =>
      cases t with
      | nil =>
          fin_cases a
          · exact Or.inr (below_nil_zero _)
          · exact Or.inr (below_nil_one _)
          · exact Or.inl (below_two_nil _ (noOne_map_of_not_one (originalOnes_two hs)))
      | cons b t =>
          by_cases hab : a = b
          · subst b
            rcases ih t (originalOnes_tail hs) (originalOnes_tail ht)
              (splitCompatible_tail hcompat) with h | h
            · exact Or.inl ((below_same (toLetter a) _ _).mpr h)
            · exact Or.inr ((below_same (toLetter a) _ _).mpr h)
          · rcases hcompat [] a b s t rfl rfl hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Or.inr (below_two_zero _ _ (noOne_map_of_not_one (originalOnes_two ht)))
            · exact Or.inl (below_two_zero _ _ (noOne_map_of_not_one (originalOnes_two hs)))

theorem paper_siblings {nodes codes : Finset DiaryWord} {height : Nat}
    (T : PaperTreeAxioms nodes codes height) {p : DiaryWord} {a b : Fin 3}
    (ha : child p a ∈ nodes) (hb : child p b ∈ nodes) (hab : a ≠ b) :
    (a = 0 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by
  have hp : p ∈ nodes := by
    have h := T.prefix_closed _ ha p.length (by simp [child])
    simpa [child] using h
  obtain ⟨kind, c, P⟩ := T.level p.length (T.bounded p hp)
  have har := (P.children p hp rfl a).mp ha
  have hbr := (P.children p hp rfl b).mp hb
  cases kind <;> by_cases heq : p = c <;> by_cases hlt : p < c <;>
    simp_all [localChild, PaperKind.special] <;> aesop

theorem node_prefix_child (d : Diary true n 1) (hw : w ∈ d.toTree.nodes)
    (heq : w = p ++ a :: t) : child p a ∈ d.toTree.nodes := by
  rw [heq] at hw
  have hp := d.toTree_prefix_closed hw (j := p.length + 1) (by simp)
  simpa [child, List.take_append, List.take_of_length_le (show p.length ≤ p.length + 1 by omega)] using hp

theorem node_originalOnes (d : Diary true n 1) (hw : w ∈ d.toTree.nodes) : OriginalOnes w := by
  intro p t heq
  exact d.toTree_one_original (node_prefix_child d hw heq)

theorem nodes_splitCompatible (d : Diary true n 1)
    (hs : s ∈ d.toTree.nodes) (ht : t ∈ d.toTree.nodes) : SplitCompatible s t := by
  intro p a b u v hu hv hab
  exact paper_siblings d.paper_axioms
    (List.mem_toFinset.mpr (node_prefix_child d hs hu))
    (List.mem_toFinset.mpr (node_prefix_child d ht hv)) hab

/-- The alphabet identification followed by the verified block-model map. -/
def model (w : DiaryWord) : TernaryModel := toBlocks (w.map toLetter)

theorem model_injective : Function.Injective model := by
  intro s t h
  have h' : s.map toLetter = t.map toLetter := wordEquiv.injective h
  have h'' := congrArg (List.map toFin) h'
  simpa [List.map_map, Function.comp_def] using h''

/-- In fact every node of a diary, not only its coding nodes, is comparable
in the actual pseudotree. The proof handles prefix and split cases. -/
theorem nodes_chain (d : Diary true n 1)
    (hs : s ∈ d.toTree.nodes) (ht : t ∈ d.toTree.nodes) :
    model s ≤ model t ∨ model t ≤ model s := by
  have h := comparable s t (node_originalOnes d hs) (node_originalOnes d ht)
    (nodes_splitCompatible d hs ht)
  exact h.imp (wordBelow_iff_toBlocks_le _ _).mp (wordBelow_iff_toBlocks_le _ _).mp

theorem codes_chain (d : Diary true n 1)
    (hs : s ∈ d.toTree.codes) (ht : t ∈ d.toTree.codes) :
    model s ≤ model t ∨ model t ≤ model s :=
  nodes_chain d (execute_codes_nodes d.events hs) (execute_codes_nodes d.events ht)

theorem paper_codes_chain (D : PaperDiary n) (hs : s ∈ D.codes) (ht : t ∈ D.codes) :
    model s ≤ model t ∨ model t ≤ model s := by
  obtain ⟨d, _, hc⟩ := D.represented
  exact codes_chain d ((hc s).mpr hs) ((hc t).mpr ht)

end DiaryChains

open FirstOrder
open scoped FirstOrder

namespace PaperDiary

noncomputable def modelCodes (D : PaperDiary n) : Finset TernaryModel := by
  classical
  exact D.codes.image DiaryChains.model

theorem modelCodes_card (D : PaperDiary n) : D.modelCodes.card = n := by
  classical
  rw [modelCodes, Finset.card_image_of_injective _ DiaryChains.model_injective]
  exact D.size

theorem modelCodes_chain (D : PaperDiary n) {s t : TernaryModel}
    (hs : s ∈ D.modelCodes) (ht : t ∈ D.modelCodes) : s ≤ t ∨ t ≤ s := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ht
  exact DiaryChains.paper_codes_chain D ha hb

theorem modelCodes_inf_closed (D : PaperDiary n) {s t : TernaryModel}
    (hs : s ∈ D.modelCodes) (ht : t ∈ D.modelCodes) : s ⊓ t ∈ D.modelCodes := by
  rcases D.modelCodes_chain hs ht with h | h
  · simpa only [inf_eq_left.mpr h] using hs
  · simpa only [inf_eq_right.mpr h] using ht

/-- An actual finite substructure in the functional language `{≤,∧}` whose
underlying set is the diary's coding nodes in the verified model. -/
noncomputable def codeSubstructure (D : PaperDiary n) : language.Substructure TernaryModel :=
  substructureOfMeetClosed (D.modelCodes : Set TernaryModel)
    (fun _ hs _ ht => D.modelCodes_inf_closed hs ht)

abbrev CodePoint (D : PaperDiary n) := {x : TernaryModel // x ∈ D.modelCodes}

noncomputable instance codePointLinearOrder (D : PaperDiary n) : LinearOrder D.CodePoint := by
  classical
  exact {
    toPartialOrder := (inferInstance : PartialOrder D.CodePoint)
    le_total := fun x y => D.modelCodes_chain x.property y.property
    toDecidableLE := Classical.decRel _
    toDecidableEq := Classical.decEq _ }

noncomputable def codeOrderIso (D : PaperDiary n) : Fin n ≃o D.CodePoint :=
  Fintype.orderIsoFinOfCardEq D.CodePoint (by
    rw [Fintype.card_coe, D.modelCodes_card])

/-- A concrete embedding of the standard n-element chain in the functional
language, with image exactly the diary's coding nodes. -/
noncomputable def chainEmbedding (D : PaperDiary n) : Fin n ↪[language] TernaryModel where
  toFun i := (D.codeOrderIso i).val
  inj' := by
    intro i j heq
    exact D.codeOrderIso.injective (Subtype.ext heq)
  map_fun' := by
    intro k f x
    cases f
    change (D.codeOrderIso (x 0 ⊓ x 1)).val = (D.codeOrderIso (x 0)).val ⊓ (D.codeOrderIso (x 1)).val
    rcases le_total (x 0) (x 1) with h | h
    · have hi : (D.codeOrderIso (x 0)).val ≤ (D.codeOrderIso (x 1)).val :=
        D.codeOrderIso.monotone h
      rw [inf_eq_left.mpr h, inf_eq_left.mpr hi]
    · have hi : (D.codeOrderIso (x 1)).val ≤ (D.codeOrderIso (x 0)).val :=
        D.codeOrderIso.monotone h
      rw [inf_eq_right.mpr h, inf_eq_right.mpr hi]
  map_rel' := by
    intro k r x
    cases r
    change (D.codeOrderIso (x 0)).val ≤ (D.codeOrderIso (x 1)).val ↔ x 0 ≤ x 1
    exact D.codeOrderIso.le_iff_le

theorem chainEmbedding_range (D : PaperDiary n) :
    Set.range D.chainEmbedding = (D.modelCodes : Set TernaryModel) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact (D.codeOrderIso i).property
  · intro hx
    refine ⟨D.codeOrderIso.symm ⟨x, hx⟩, ?_⟩
    change (D.codeOrderIso (D.codeOrderIso.symm ⟨x, hx⟩)).val = x
    rw [OrderIso.apply_symm_apply]

end PaperDiary

end AllThoseBigRamsey.Pseudotree
