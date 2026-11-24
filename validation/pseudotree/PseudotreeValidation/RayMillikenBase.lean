import PseudotreeValidation.MixedProduct

/-!
# Finite prefix trees and their actual ray embeddings

An embedding is a function on the finite node set, with a proposition
witnessing extension to a total ray-preserving strong map. Thus colourings
cannot depend on an irrelevant chosen level sequence or extension witness.
The local-to-total theorem below identifies this with the local definition
in the manuscript, using the independently proved completion construction.
-/

namespace AllThoseBigRamsey.Pseudotree.RayMilliken

open RayEmbeddings

def LastOne (s : Word) : Prop := ∃ t, s = t ++ [1]

structure Shape where
  nodes : Finset Word
  root_mem : [] ∈ nodes
  prefix_closed : ∀ s t, s ++ t ∈ nodes → s ∈ nodes
  one_per_level : ∀ s ∈ nodes, ∀ t ∈ nodes,
    s.length = t.length → LastOne s → LastOne t → s = t

namespace Shape

abbrev Node (F : Shape) := {s : Word // s ∈ F.nodes}

def height (F : Shape) : ℕ := F.nodes.sup List.length + 1

theorem height_pos (F : Shape) : 0 < F.height := Nat.zero_lt_succ _

theorem length_lt_height (F : Shape) (s : Word) (hs : s ∈ F.nodes) :
    s.length < F.height := by
  have h := Finset.le_sup (f := List.length) hs
  dsimp [height]
  omega

noncomputable def topNode (F : Shape) : F.Node :=
  let h := Finset.exists_mem_eq_sup F.nodes ⟨[], F.root_mem⟩ List.length
  ⟨h.choose, h.choose_spec.1⟩

theorem topNode_length (F : Shape) : F.topNode.val.length = F.height - 1 := by
  have h := (Finset.exists_mem_eq_sup F.nodes ⟨[], F.root_mem⟩ List.length).choose_spec.2
  simpa only [topNode, height, Nat.add_sub_cancel] using h.symm

def truncate (F : Shape) (h : ℕ) (hh : 0 < h) : Shape where
  nodes := F.nodes.filter (fun s => s.length < h)
  root_mem := Finset.mem_filter.mpr ⟨F.root_mem, hh⟩
  prefix_closed := by
    intro s t hst
    obtain ⟨hmem, hlen⟩ := Finset.mem_filter.mp hst
    refine Finset.mem_filter.mpr ⟨F.prefix_closed s t hmem, ?_⟩
    simp only [List.length_append] at hlen
    omega
  one_per_level := by
    intro s hs t ht hlen hs1 ht1
    exact F.one_per_level s (Finset.mem_filter.mp hs).1 t
      (Finset.mem_filter.mp ht).1 hlen hs1 ht1

theorem truncate_subset (F : Shape) (h : ℕ) (hh : 0 < h) :
    (F.truncate h hh).nodes ⊆ F.nodes := Finset.filter_subset _ _

@[simp] theorem mem_truncate (F : Shape) (h : ℕ) (hh : 0 < h) (s : Word) :
    s ∈ (F.truncate h hh).nodes ↔ s ∈ F.nodes ∧ s.length < h := Finset.mem_filter

end Shape

/-- Only the finite map is data; realizability is proof-irrelevant. -/
@[ext] structure Embedding (F : Shape) where
  map : F.Node → Word
  realizable : ∃ g : RayStrongMap, ∀ s : F.Node, g.map s.val = map s

instance (F : Shape) : CoeFun (Embedding F) (fun _ => F.Node → Word) := ⟨Embedding.map⟩

namespace Embedding

variable {F G H : Shape}

def ofTotal (F : Shape) (g : RayStrongMap) : Embedding F :=
  ⟨fun s => g.map s.val, ⟨g, fun _ => rfl⟩⟩

noncomputable def realizer (e : Embedding F) : RayStrongMap := e.realizable.choose

theorem realizer_agrees (e : Embedding F) (s : F.Node) : e.realizer.map s.val = e s :=
  e.realizable.choose_spec s

theorem injective (e : Embedding F) : Function.Injective e := by
  intro s t h
  apply Subtype.ext
  apply e.realizer.injective
  simpa only [e.realizer_agrees] using h

def comp (g : RayStrongMap) (e : Embedding F) : Embedding F where
  map s := g.map (e s)
  realizable := by
    obtain ⟨f, hf⟩ := e.realizable
    exact ⟨g.comp f, fun s => by simp only [RayStrongMap.comp_map, hf]⟩

@[simp] theorem comp_apply (g : RayStrongMap) (e : Embedding F) (s : F.Node) :
    comp g e s = g.map (e s) := rfl

@[simp] theorem comp_comp (f g : RayStrongMap) (e : Embedding F) :
    comp f (comp g e) = comp (f.comp g) e := by ext s; rfl

@[simp] theorem comp_identity (e : Embedding F) : comp RayStrongMap.identity e = e := by
  ext s
  rfl

def restrict (e : Embedding F) (G : Shape) (hGF : G.nodes ⊆ F.nodes) : Embedding G where
  map s := e ⟨s.val, hGF s.property⟩
  realizable := by
    obtain ⟨f, hf⟩ := e.realizable
    exact ⟨f, fun s => hf ⟨s.val, hGF s.property⟩⟩

@[simp] theorem restrict_apply (e : Embedding F) (G : Shape) (hGF : G.nodes ⊆ F.nodes)
    (s : G.Node) : e.restrict G hGF s = e ⟨s.val, hGF s.property⟩ := rfl

@[simp] theorem restrict_comp (e : Embedding F) (g : RayStrongMap)
    (G : Shape) (hGF : G.nodes ⊆ F.nodes) :
    (comp g e).restrict G hGF = comp g (e.restrict G hGF) := by ext s; rfl

@[simp] theorem restrict_trans (e : Embedding F) (G : Shape) (H : Shape)
    (hGF : G.nodes ⊆ F.nodes) (hHG : H.nodes ⊆ G.nodes) :
    (e.restrict G hGF).restrict H hHG = e.restrict H (fun _s hs => hGF (hHG hs)) := by
  ext s
  rfl

theorem restrict_surjective (G F : Shape) (hGF : G.nodes ⊆ F.nodes) :
    Function.Surjective (fun e : Embedding F => e.restrict G hGF) := by
  intro e
  refine ⟨ofTotal F e.realizer, ?_⟩
  apply Embedding.ext
  funext s
  exact e.realizer_agrees s

noncomputable def topLevel (e : Embedding F) : ℕ := (e F.topNode).length

theorem length_bounded (e : Embedding F) (s : F.Node) : (e s).length ≤ e.topLevel := by
  have hsrc : s.val.length ≤ F.topNode.val.length := by
    have h := F.length_lt_height s.val s.property
    rw [F.topNode_length]
    omega
  change (e s).length ≤ (e F.topNode).length
  rw [← e.realizer_agrees s, ← e.realizer_agrees F.topNode,
    e.realizer.length_map, e.realizer.length_map]
  rcases Nat.lt_or_eq_of_le hsrc with h | h
  · exact Nat.le_of_lt (e.realizer.level_strict h)
  · rw [h]

end Embedding

private def wordsThrough : ℕ → Finset Word
  | 0 => {[]}
  | n + 1 => {[]} ∪ (Finset.univ : Finset (Fin 3)).biUnion
      (fun a => (wordsThrough n).image (List.cons a))

private theorem mem_wordsThrough (n : ℕ) (s : Word) : s ∈ wordsThrough n ↔ s.length ≤ n := by
  induction n generalizing s with
  | zero => simp [wordsThrough]
  | succ n ih => cases s <;> simp [wordsThrough, ih]

instance finite_bounded_embeddings (F : Shape) (j : ℕ) :
    Finite {e : Embedding F // ∀ s, (e s).length ≤ j} := by
  let encode (e : {e : Embedding F // ∀ s, (e s).length ≤ j}) :
      F.Node → {s : Word // s ∈ wordsThrough j} :=
    fun s => ⟨e.val s, (mem_wordsThrough j _).mpr (e.property s)⟩
  apply Finite.of_injective encode
  intro e f h
  apply Subtype.ext
  apply Embedding.ext
  funext s
  exact congrArg Subtype.val (congrFun h s)

instance finite_topLevel_embeddings (F : Shape) (j : ℕ) :
    Finite {e : Embedding F // e.topLevel = j} := by
  let encode (e : {e : Embedding F // e.topLevel = j}) :
      {e : Embedding F // ∀ s, (e s).length ≤ j} :=
    ⟨e.val, fun s => by simpa only [e.property] using e.val.length_bounded s⟩
  apply Finite.of_injective encode
  intro e f h
  apply Subtype.ext
  exact congrArg (fun z : {e : Embedding F // ∀ s, (e s).length ≤ j} => z.val) h

/-- The restriction-based type admits every map satisfying the local
finite-domain conditions from the manuscript. -/
theorem realizable_of_local (F : Shape) (e : F.Node → Word) (levels : ℕ → ℕ)
    (hlevels : ∀ {i j}, i < j → j < F.height → levels i < levels j)
    (hlength : ∀ s, (e s).length = levels s.val.length)
    (hstep : ∀ s a (h : s ++ [a] ∈ F.nodes), ∃ p : Word,
      e ⟨s ++ [a], h⟩ = e ⟨s, F.prefix_closed s [a] h⟩ ++ a :: p ∧
        (a ≠ 1 → Binary p)) :
    ∃ g : RayStrongMap, ∀ s : F.Node, g.map s.val = e s := by
  classical
  let total (s : Word) : Word := if hs : s ∈ F.nodes then e ⟨s, hs⟩ else []
  have htotal (s : F.Node) : total s.val = e s := by simp [total, s.property]
  obtain ⟨g, hg, _⟩ := finite_completion (fun s => s ∈ F.nodes)
    ⟨[], F.root_mem⟩ F.prefix_closed F.height F.length_lt_height total levels hlevels
    (by
      intro s hs
      rw [htotal (⟨s, hs⟩ : F.Node)]
      exact hlength ⟨s, hs⟩)
    (by
      intro s a h
      obtain ⟨p, hp, hb⟩ := hstep s a h
      refine ⟨p, ?_, hb⟩
      rw [htotal (⟨s ++ [a], h⟩ : F.Node),
        htotal (⟨s, F.prefix_closed s [a] h⟩ : F.Node)]
      exact hp)
  exact ⟨g, fun s => (hg s.val s.property).trans (htotal s)⟩

/-- The literal finite level and edge conditions. The schedule is an
existential witness, not additional colourable data. -/
def Local (F : Shape) (e : F.Node → Word) : Prop :=
  ∃ levels : ℕ → ℕ,
    (∀ {i j}, i < j → j < F.height → levels i < levels j) ∧
    (∀ s, (e s).length = levels s.val.length) ∧
    (∀ s a (h : s ++ [a] ∈ F.nodes), ∃ p : Word,
      e ⟨s ++ [a], h⟩ = e ⟨s, F.prefix_closed s [a] h⟩ ++ a :: p ∧
        (a ≠ 1 → Binary p))

/-- Thus the embedding domain used in the Ramsey theorem is exactly the
manuscript's local finite embedding domain. -/
theorem local_iff_realizable (F : Shape) (e : F.Node → Word) :
    Local F e ↔ ∃ g : RayStrongMap, ∀ s : F.Node, g.map s.val = e s := by
  constructor
  · rintro ⟨levels, hlevels, hlength, hstep⟩
    exact realizable_of_local F e levels hlevels hlength hstep
  · rintro ⟨g, hg⟩
    refine ⟨g.level, fun h _ => g.level_strict h, ?_, ?_⟩
    · intro s
      rw [← hg s]
      exact g.length_map s.val
    · intro s a h
      obtain ⟨p, hp, hb⟩ := g.step s a
      refine ⟨p, ?_, hb⟩
      rw [hg (⟨s ++ [a], h⟩ : F.Node),
        hg (⟨s, F.prefix_closed s [a] h⟩ : F.Node)] at hp
      exact hp

def FixesThrough (j : ℕ) (g : RayStrongMap) : Prop :=
  ∀ s : Word, s.length ≤ j → g.map s = s

theorem fixes_comp {j : ℕ} {f g : RayStrongMap}
    (hf : FixesThrough j f) (hg : FixesThrough j g) : FixesThrough j (f.comp g) := by
  intro s hs
  simp only [RayStrongMap.comp_map, hg s hs, hf s hs]

theorem comp_fixed_embedding {F : Shape} {j : ℕ} (g : RayStrongMap)
    (hg : FixesThrough j g) (e : Embedding F) (he : e.topLevel ≤ j) :
    Embedding.comp g e = e := by
  apply Embedding.ext
  funext s
  exact hg (e s) ((e.length_bounded s).trans he)

def induced {F : Shape} {κ : Type} (colour : Embedding F → κ) (g : RayStrongMap) :
    Embedding F → κ := fun e => colour (Embedding.comp g e)

def FibreConstant {F G : Shape} (hGF : G.nodes ⊆ F.nodes) {κ : Type}
    (colour : Embedding F → κ) (e' : Embedding G) : Prop :=
  ∀ e₁ e₂ : Embedding F, e₁.restrict G hGF = e' → e₂.restrict G hGF = e' →
    colour e₁ = colour e₂

theorem fibreConstant_comp {F G : Shape} (hGF : G.nodes ⊆ F.nodes) {κ : Type}
    (colour : Embedding F → κ) (e' : Embedding G) (j : ℕ)
    (hc : FibreConstant hGF colour e') (g : RayStrongMap)
    (hg : FixesThrough j g) (he : e'.topLevel ≤ j) :
    FibreConstant hGF (induced colour g) e' := by
  intro e₁ e₂ h₁ h₂
  apply hc (Embedding.comp g e₁) (Embedding.comp g e₂)
  · rw [Embedding.restrict_comp, h₁]
    exact comp_fixed_embedding g hg e' he
  · rw [Embedding.restrict_comp, h₂]
    exact comp_fixed_embedding g hg e' he

end AllThoseBigRamsey.Pseudotree.RayMilliken
