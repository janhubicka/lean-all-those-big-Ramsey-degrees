import PseudotreeValidation.RayMillikenBoundary

/-! One genuine local fibre step of the restricted finite-tree theorem.
The finite colouring is pulled back only along actual finite embeddings.
Mixed boundary homogenization and the checked global graft then make the
whole fibre constant. -/

namespace AllThoseBigRamsey.Pseudotree.RayMilliken

open RayEmbeddings

namespace Shape

theorem take_mem (F : Shape) (s : Word) (hs : s ∈ F.nodes) (n : ℕ) :
    s.take n ∈ F.nodes := by
  apply F.prefix_closed (s.take n) (s.drop n)
  simpa only [List.take_append_drop] using hs

theorem truncate_height (F : Shape) (h : ℕ) (hh : 0 < h) (hF : h ≤ F.height) :
    (F.truncate h hh).height = h := by
  have hUpper : (F.truncate h hh).nodes.sup List.length < h := by
    have hle : (F.truncate h hh).nodes.sup List.length ≤ h - 1 := by
      apply Finset.sup_le
      intro s hs
      have hs' := (F.mem_truncate h hh s).mp hs
      omega
    omega
  let s := F.topNode.val.take (h - 1)
  have hlen : s.length = h - 1 := by
    dsimp [s]
    rw [List.length_take, F.topNode_length, Nat.min_eq_left (by omega)]
  have hs : s ∈ (F.truncate h hh).nodes := by
    apply (F.mem_truncate h hh s).mpr
    exact ⟨F.take_mem F.topNode.val F.topNode.property _, by omega⟩
  have hLower : h - 1 ≤ (F.truncate h hh).nodes.sup List.length := by
    simpa only [hlen] using (Finset.le_sup (f := List.length) hs)
  dsimp [height]
  omega

abbrev Top (F : Shape) (h : ℕ) := {s : F.Node // s.val.length = h}

instance (F : Shape) (h : ℕ) : Finite (Top F h) := inferInstanceAs (Finite {_s : F.Node // _})

noncomputable instance (F : Shape) (h : ℕ) : Fintype (Top F h) := Fintype.ofFinite _

namespace Top

variable {F : Shape} {h : ℕ}

def parent (i : Top F h) : Word := i.val.val.dropLast

def letter (hh : 0 < h) (i : Top F h) : Fin 3 :=
  i.val.val.getLast (by intro heq; have ht := i.property; simp [heq] at ht; omega)

theorem parent_letter (hh : 0 < h) (i : Top F h) :
    i.parent ++ [i.letter hh] = i.val.val := List.dropLast_append_getLast _

theorem parent_length (i : Top F h) : i.parent.length = h - 1 := by
  simp only [parent, List.length_dropLast, i.property]

def parentNode (hh : 0 < h) (i : Top F h) : (F.truncate h hh).Node :=
  ⟨i.parent, (F.mem_truncate h hh i.parent).mpr ⟨by
    apply F.prefix_closed i.parent [i.letter hh]
    rw [i.parent_letter hh]
    exact i.val.property, by rw [i.parent_length]; omega⟩⟩

def boundary (hh : 0 < h) (e' : Embedding (F.truncate h hh)) (i : Top F h) : Word :=
  e' (i.parentNode hh) ++ [i.letter hh]

theorem parent_image_length (hh : 0 < h) (hF : h ≤ F.height)
    (e' : Embedding (F.truncate h hh)) (i : Top F h) :
    (e' (i.parentNode hh)).length = e'.topLevel := by
  change _ = (e' (F.truncate h hh).topNode).length
  rw [← e'.realizer_agrees, ← e'.realizer_agrees,
    e'.realizer.length_map, e'.realizer.length_map]
  congr 1
  rw [(F.truncate h hh).topNode_length, F.truncate_height h hh hF]
  exact i.parent_length

theorem boundary_length (hh : 0 < h) (hF : h ≤ F.height)
    (e' : Embedding (F.truncate h hh)) (i : Top F h) :
    (i.boundary hh e').length = e'.topLevel + 1 := by
  simp only [boundary, List.length_append, List.length_singleton, i.parent_image_length hh hF e']

theorem boundary_injective (hh : 0 < h) (e' : Embedding (F.truncate h hh)) :
    Function.Injective (boundary hh e') := by
  intro i k heq
  have hp : e' (i.parentNode hh) = e' (k.parentNode hh) := by
    have hd := congrArg List.dropLast heq
    simpa only [boundary, List.dropLast_concat] using hd
  have hs : i.parent = k.parent := congrArg Subtype.val (e'.injective hp)
  have ha : i.letter hh = k.letter hh := by
    have hl := congrArg List.getLast? heq
    simpa only [boundary, List.getLast?_concat, Option.some.injEq] using hl
  apply Subtype.ext
  apply Subtype.ext
  rw [← i.parent_letter hh, ← k.parent_letter hh, hs, ha]

theorem lastOne_boundary (hh : 0 < h) (e' : Embedding (F.truncate h hh)) (i : Top F h) :
    LastOne (i.boundary hh e') ↔ i.letter hh = 1 := by
  constructor
  · rintro ⟨p, hp⟩
    have hl := congrArg List.getLast? hp
    simpa only [boundary, List.getLast?_concat, Option.some.injEq] using hl
  · intro h
    exact ⟨e' (i.parentNode hh), by simp only [boundary, h]⟩

theorem boundary_one (hh : 0 < h) (e' : Embedding (F.truncate h hh))
    (i k : Top F h) (hi : LastOne (i.boundary hh e')) (hk : LastOne (k.boundary hh e')) : i = k := by
  have hi' := (i.lastOne_boundary hh e').mp hi
  have hk' := (k.lastOne_boundary hh e').mp hk
  apply Subtype.ext
  apply Subtype.ext
  apply F.one_per_level i.val.val i.val.property k.val.val k.val.property
  · rw [i.property, k.property]
  · exact ⟨i.parent, by rw [← hi', i.parent_letter hh]⟩
  · exact ⟨k.parent, by rw [← hk', k.parent_letter hh]⟩

end Top
end Shape

/-- Restriction to all lower levels and the values at the top level
uniquely determine a finite embedding. -/
theorem embedding_ext_top (F : Shape) (h : ℕ) (hh : 0 < h)
    (hF : F.height = h + 1) (e f : Embedding F)
    (hlower : e.restrict (F.truncate h hh) (F.truncate_subset h hh) =
      f.restrict (F.truncate h hh) (F.truncate_subset h hh))
    (htop : ∀ i : F.Top h, e i.val = f i.val) : e = f := by
  apply Embedding.ext
  funext s
  have hs := F.length_lt_height s.val s.property
  by_cases hlt : s.val.length < h
  · let t : (F.truncate h hh).Node := ⟨s.val, (F.mem_truncate h hh _).mpr ⟨s.property, hlt⟩⟩
    exact congrArg (fun a : Embedding (F.truncate h hh) => a t) hlower
  · exact htop ⟨s, by omega⟩

/-- The highest source level of any extension is a synchronized choice
from the immediate cones determined by its lower restriction. -/
theorem embedding_top_tails (F : Shape) (h : ℕ) (hh : 0 < h)
    (hF : F.height = h + 1) (e' : Embedding (F.truncate h hh)) (e : Embedding F)
    (he : e.restrict (F.truncate h hh) (F.truncate_subset h hh) = e') :
    ∃ (n : ℕ) (x : F.Top h → Word),
      (∀ i, e i.val = i.boundary hh e' ++ x i) ∧
      (∀ i, (x i).length = n) ∧
      (∀ i, ¬ LastOne (i.boundary hh e') → Binary (x i)) := by
  classical
  have ht (i : F.Top h) : ∃ p : Word,
      e i.val = i.boundary hh e' ++ p ∧ (i.letter hh ≠ 1 → Binary p) := by
    obtain ⟨p, hp, hb⟩ := e.realizer.step i.parent (i.letter hh)
    have hparent : e.realizer.map i.parent = e' (i.parentNode hh) := by
      rw [← he]
      exact e.realizer_agrees ⟨i.parent, (F.truncate_subset h hh) (i.parentNode hh).property⟩
    rw [i.parent_letter hh, e.realizer_agrees i.val, hparent] at hp
    exact ⟨p, by simpa only [Shape.Top.boundary, List.append_assoc, List.singleton_append] using hp, hb⟩
  choose x hx hxBinary using ht
  refine ⟨e.realizer.level h - (e'.topLevel + 1), x, hx, ?_, ?_⟩
  · intro i
    have hlen := congrArg List.length (hx i)
    rw [← e.realizer_agrees i.val, e.realizer.length_map, i.property,
      List.length_append, i.boundary_length hh (by omega) e'] at hlen
    omega
  · intro i hi
    apply hxBinary i
    intro hlast
    exact hi ((i.lastOne_boundary hh e').mpr hlast)

/-- This is the genuine one-fibre step used in the height induction:
its hypotheses are solely the finite tree and its given colouring. -/
theorem homogenize_fibre (F : Shape) (h : ℕ) (hh : 0 < h) (hF : F.height = h + 1)
    {colours : ℕ} (colour : Embedding F → Fin (colours + 1))
    (e' : Embedding (F.truncate h hh)) :
    ∃ g : RayStrongMap, FixesThrough e'.topLevel g ∧
      FibreConstant (F.truncate_subset h hh) (induced colour g) e' := by
  classical
  let G := F.truncate h hh
  let inclusion := F.truncate_subset h hh
  let compatible (x : F.Top h → Word) (e : Embedding F) : Prop :=
    e.restrict G inclusion = e' ∧ ∀ i, e i.val = x i
  let lift (x : F.Top h → Word) : Fin (colours + 1) :=
    if hx : ∃ e, compatible x e then colour hx.choose else 0
  have hlift (x : F.Top h → Word) (e : Embedding F) (he : compatible x e) :
      lift x = colour e := by
    have hex : ∃ f, compatible x f := ⟨e, he⟩
    simp only [lift, hex, ↓reduceDIte]
    congr 1
    apply embedding_ext_top F h hh hF
    · exact hex.choose_spec.1.trans he.1.symm
    · intro i
      exact (hex.choose_spec.2 i).trans (he.2 i).symm
  obtain ⟨c, g, hg, hc⟩ := boundary_product (fun i : F.Top h => i.boundary hh e')
    (fun i => i.boundary_length hh (by omega) e') (Shape.Top.boundary_injective hh e')
    (Shape.Top.boundary_one hh e') lift
  refine ⟨g, hg, ?_⟩
  have hcolour (e : Embedding F) (he : e.restrict G inclusion = e') :
      colour (Embedding.comp g e) = c := by
    obtain ⟨n, x, hx, hxLength, hxBinary⟩ := embedding_top_tails F h hh hF e' e he
    have hmono := hc n x hxLength hxBinary
    let y (i : F.Top h) := g.map (i.boundary hh e' ++ x i)
    have hy : compatible y (Embedding.comp g e) := by
      constructor
      · rw [Embedding.restrict_comp, he]
        exact comp_fixed_embedding g hg e' (Nat.le_refl _)
      · intro i
        exact congrArg g.map (hx i)
    exact (hlift y (Embedding.comp g e) hy).symm.trans hmono
  intro e₁ e₂ h₁ h₂
  change colour (Embedding.comp g e₁) = colour (Embedding.comp g e₂)
  exact (hcolour e₁ h₁).trans (hcolour e₂ h₂).symm

end AllThoseBigRamsey.Pseudotree.RayMilliken
