import PseudotreeValidation.LowerLayers
import PseudotreeValidation.DiaryCanonization

/-! Finite iteration and assembly of the geometric diary realization steps. -/

namespace AllThoseBigRamsey.Pseudotree.LowerRealization

open scoped FirstOrder
open RayEmbeddings

private def emptyLayer (D : PaperDiary n)
    (f : TernaryModel ↪[language] TernaryModel) (j b : Nat)
    (hempty : ∀ _u : Level D j, False) : Layer D f j where
  bound := b
  copies u := False.elim (hempty u)
  prefixes u := False.elim (hempty u)
  prefix_length u := False.elim (hempty u)
  common_prefix u := False.elim (hempty u)
  root_short u := False.elim (hempty u)
  inside u := False.elim (hempty u)
  ordered u := False.elim (hempty u)

private def emptyStep (D : PaperDiary n)
    (f : TernaryModel ↪[language] TernaryModel) (j : Nat) (P : Layer D f j)
    (hempty : ∀ _u : Level D j, False) (hnext : ∀ _u : Level D (j + 1), False) : Step P where
  next := emptyLayer D f (j + 1) (P.bound + 1) hnext
  level := P.bound
  lower := Nat.le_refl _
  upper := Nat.lt_succ_self _
  roots u := False.elim (hempty u)
  root_length u := False.elim (hempty u)
  root_binary u := False.elim (hempty u)
  coding u := False.elim (hempty u)
  edge u := False.elim (hempty u)

/-- Iterating actual transitions. Past the finite height, all domains are
empty and harmless empty transitions extend the indexing sequence. -/
noncomputable def layerSequence (D : PaperDiary n)
    (f : TernaryModel ↪[language] TernaryModel)
    (pick : ∀ j, (P : Layer D f j) → Step P) : (j : Nat) → Layer D f j
  | 0 => Classical.choice (initial D f)
  | j + 1 => (pick j (layerSequence D f pick j)).next

/-- Local geometric transitions assemble into an actual total ray-preserving
strong map realizing every coding node inside the specified self-copy.
The geometric existence of each transition is the explicit input to this
finite iteration lemma. -/
theorem finite_realization_of_steps (D : PaperDiary n)
    (f : TernaryModel ↪[language] TernaryModel)
    {height : Nat} (T : PaperTreeAxioms D.nodes D.codes height)
    (hstep : ∀ j, j < height → ∀ P : Layer D f j, Nonempty (Step P)) :
    ∃ g : RayStrongMap, ∀ w ∈ D.codes, DiaryChains.model (g.map w) ∈ Set.range f := by
  classical
  have allSteps (j : Nat) (P : Layer D f j) : Nonempty (Step P) := by
    by_cases hj : j < height
    · exact hstep j hj P
    · refine ⟨emptyStep D f j P ?_ ?_⟩
      · intro u
        have hbound := T.bounded u.val u.property.1
        rw [u.property.2] at hbound
        omega
      · intro u
        have hbound := T.bounded u.val u.property.1
        rw [u.property.2] at hbound
        omega
  let pick (j : Nat) (P : Layer D f j) : Step P := Classical.choice (allSteps j P)
  let P := layerSequence D f pick
  let S (j : Nat) : Step (P j) := pick j (P j)
  let levels (j : Nat) := (S j).level
  have level_succ (j : Nat) : levels j < levels (j + 1) :=
    (S j).upper.trans_le (S (j + 1)).lower
  have hlevels : StrictMono levels := strictMono_nat_of_lt_succ level_succ
  let e : D.shape.Node → Word := fun s =>
    ((S s.val.length).roots ⟨s.val, s.property, rfl⟩).map RayMapModel.toFin
  have eat (j : Nat) (u : Level D j) :
      e ⟨u.val, u.property.1⟩ = ((S j).roots u).map RayMapModel.toFin := by
    rcases u with ⟨u, hu, hlen⟩
    subst j
    rfl
  have elength (s : D.shape.Node) : (e s).length = levels s.val.length := by
    exact (List.length_map _).trans ((S s.val.length).root_length ⟨s.val, s.property, rfl⟩)
  have estep : ∀ s a (ha : s ++ [a] ∈ D.shape.nodes), ∃ b : Word,
      e ⟨s ++ [a], ha⟩ = e ⟨s, D.shape.prefix_closed s [a] ha⟩ ++ a :: b ∧
        (a ≠ 1 → Binary b) := by
    intro s a ha
    let u : Level D s.length := ⟨s, D.shape.prefix_closed s [a] ha, rfl⟩
    let v : Level D (s.length + 1) := childNode u a ha
    obtain ⟨b, hb, hb_binary⟩ := (S s.length).edge u a ha
    obtain ⟨c, hc_binary, hc⟩ := (S (s.length + 1)).root_binary v
    have hroots : (S (s.length + 1)).roots v =
        (S s.length).roots u ++ RayMapModel.toLetter a :: (b ++ c) := by
      rw [hc]
      change (S s.length).next.prefixes (childNode u a ha) ++ c = _
      rw [hb]
      simp only [List.append_assoc, List.cons_append]
    refine ⟨(b ++ c).map RayMapModel.toFin, ?_, ?_⟩
    · change e ⟨v.val, v.property.1⟩ =
        e ⟨u.val, u.property.1⟩ ++ a :: (b ++ c).map RayMapModel.toFin
      rw [eat (s.length + 1) v, eat s.length u, hroots]
      simp only [List.map_append, List.map_cons, RayMapModel.toFin_toLetter]
    · intro ha1
      apply (RayMapModel.binary_map _).mpr
      intro x hx hx1
      have hnot : TernaryLetter.one ∉ b ++ c := by
        simp only [List.mem_append, not_or]
        exact ⟨hb_binary ha1, hc_binary⟩
      exact hnot (hx1 ▸ hx)
  obtain ⟨g, hg⟩ := RayMilliken.realizable_of_local D.shape e levels
    (fun hij _ => hlevels hij) elength estep
  refine ⟨g, ?_⟩
  intro w hw
  rw [hg ⟨w, D.code_node hw⟩]
  change toBlocks ((((S w.length).roots ⟨w, D.code_node hw, rfl⟩).map
    RayMapModel.toFin).map RayMapModel.toLetter) ∈ Set.range f
  simpa only [List.map_map, Function.comp_def, RayMapModel.toLetter_toFin,
    List.map_id_fun', id_eq] using
    (S w.length).coding ⟨w, D.code_node hw, rfl⟩ hw

/-- The same assembly statement expressed as inclusion of the range of an
actual standard-chain embedding. -/
theorem chain_realization_of_steps (D : PaperDiary n)
    (f : TernaryModel ↪[language] TernaryModel)
    {height : Nat} (T : PaperTreeAxioms D.nodes D.codes height)
    (hstep : ∀ j, j < height → ∀ P : Layer D f j, Nonempty (Step P)) :
    ∃ g : RayStrongMap,
      Set.range ((RayMapModel.embedding g).comp D.chainEmbedding) ⊆ Set.range f := by
  obtain ⟨g, hg⟩ := finite_realization_of_steps D f T hstep
  refine ⟨g, ?_⟩
  rintro x ⟨i, rfl⟩
  obtain ⟨w, hw, hi⟩ := D.chainEmbedding_word i
  change RayMapModel.embedding g (D.chainEmbedding i) ∈ Set.range f
  rw [hi.symm, PaperDiary.ray_embedding_model]
  exact hg w hw

end AllThoseBigRamsey.Pseudotree.LowerRealization
