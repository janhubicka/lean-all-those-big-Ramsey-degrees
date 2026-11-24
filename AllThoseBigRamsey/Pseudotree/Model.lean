import Std

/-!
# The block model of a pseudotree

This file checks the order-theoretic part of the ternary model in
`pseudotree_degrees.tex`.  Splitting a ternary word at its `1`s gives a nonempty
list of binary words.  Here a terminal binary block is `point a`, and an initial
binary block followed by `1` and further blocks is `above a t`.

The statements are generic in the order on the blocks.  They prove the partial
order laws, linearity of each predecessor set, and the stated meet formula.
They do **not** prove that the binary-word order is isomorphic to the rationals,
the parsing equivalence with ternary words, or the Fraïssé extension property.
-/

namespace AllThoseBigRamsey.Pseudotree

/-- A nonempty sequence of ray coordinates. -/
inductive RayTree (α : Type u) where
  | point : α → RayTree α
  | above : α → RayTree α → RayTree α
  deriving DecidableEq, Repr

namespace RayTree

variable {α : Type u}

/-- The nonempty list of ray coordinates of a node. -/
def coordinates : RayTree α → List α
  | point a => [a]
  | above a s => a :: coordinates s

@[simp] theorem coordinates_ne_nil (s : RayTree α) : coordinates s ≠ [] := by
  cases s <;> simp [coordinates]

theorem coordinates_injective :
    ∀ {s t : RayTree α}, coordinates s = coordinates t → s = t := by
  intro s
  induction s with
  | point a =>
    intro t h
    cases t with
    | point b =>
      exact congrArg point (List.cons.inj h).1
    | above b t =>
      exact False.elim (coordinates_ne_nil t (List.cons.inj h).2.symm)
  | above a s ih =>
    intro t h
    cases t with
    | point b => exact False.elim (coordinates_ne_nil s (List.cons.inj h).2)
    | above b t =>
      obtain ⟨rfl, hst⟩ := List.cons.inj h
      exact congrArg (above a) (ih hst)

/-- The block comparison from the manuscript's ternary model. -/
def Below (r : α → α → Prop) : RayTree α → RayTree α → Prop
  | point a, point b => r a b
  | point a, above b _ => r a b
  | above _ _, point _ => False
  | above a s, above b t => a = b ∧ Below r s t

@[simp] theorem below_point_point (r : α → α → Prop) (a b : α) :
    Below r (point a) (point b) ↔ r a b := Iff.rfl

@[simp] theorem below_point_above (r : α → α → Prop) (a b : α) (t : RayTree α) :
    Below r (point a) (above b t) ↔ r a b := Iff.rfl

@[simp] theorem not_below_above_point (r : α → α → Prop) (a b : α) (s : RayTree α) :
    ¬ Below r (above a s) (point b) := id

@[simp] theorem below_above_above (r : α → α → Prop) (a b : α) (s t : RayTree α) :
    Below r (above a s) (above b t) ↔ a = b ∧ Below r s t := Iff.rfl

/-- Reflexivity is inherited from the order of each ray. -/
theorem below_refl {r : α → α → Prop} (hr : ∀ a, r a a) (s : RayTree α) :
    Below r s s := by
  induction s with
  | point a => exact hr a
  | above a s ih => exact ⟨rfl, ih⟩

/-- Transitivity is inherited from the order of each ray. -/
theorem below_trans {r : α → α → Prop}
    (hr : ∀ {a b c}, r a b → r b c → r a c)
    {x y z : RayTree α} (hxy : Below r x y) (hyz : Below r y z) :
    Below r x z := by
  induction x generalizing y z with
  | point a =>
    cases y with
    | point b =>
      cases z with
      | point c => exact hr hxy hyz
      | above c t => exact hr hxy hyz
    | above b s =>
      cases z with
      | point c => exact False.elim hyz
      | above c t =>
        obtain ⟨rfl, _⟩ := hyz
        exact hxy
  | above a s ih =>
    cases y with
    | point b => exact False.elim hxy
    | above b t =>
      cases z with
      | point c => exact False.elim hyz
      | above c u =>
        obtain ⟨rfl, hst⟩ := hxy
        obtain ⟨rfl, htu⟩ := hyz
        exact ⟨rfl, ih hst htu⟩

/-- Antisymmetry is inherited from the order of each ray. -/
theorem below_antisymm {r : α → α → Prop}
    (hr : ∀ {a b}, r a b → r b a → a = b)
    {s t : RayTree α} (hst : Below r s t) (hts : Below r t s) : s = t := by
  induction s generalizing t with
  | point a =>
    cases t with
    | point b => exact congrArg point (hr hst hts)
    | above b u => exact False.elim hts
  | above a s ih =>
    cases t with
    | point b => exact False.elim hst
    | above b t =>
      obtain ⟨rfl, hst⟩ := hst
      exact congrArg (above a) (ih hst hts.2)

/-- Every predecessor set is linearly ordered when each ray is linearly ordered. -/
theorem predecessors_comparable {r : α → α → Prop}
    (hr : ∀ a b, r a b ∨ r b a)
    {s t w : RayTree α} (hs : Below r s w) (ht : Below r t w) :
    Below r s t ∨ Below r t s := by
  induction w generalizing s t with
  | point c =>
    cases s with
    | above a u => exact False.elim hs
    | point a =>
      cases t with
      | above b u => exact False.elim ht
      | point b => exact hr a b
  | above c w ih =>
    cases s with
    | point a =>
      cases t with
      | point b => exact hr a b
      | above b t =>
        obtain ⟨rfl, _⟩ := ht
        exact Or.inl hs
    | above a s =>
      obtain ⟨rfl, hs⟩ := hs
      cases t with
      | point b => exact Or.inr ht
      | above b t =>
        obtain ⟨rfl, ht⟩ := ht
        rcases ih hs ht with h | h
        · exact Or.inl ⟨rfl, h⟩
        · exact Or.inr ⟨rfl, h⟩

section Meet

variable [DecidableEq α]

/-- The meet formula: stay in the shared initial block, otherwise stop at the
smaller first different block.  The parameter `μ` is the meet of ray coordinates. -/
def meet (μ : α → α → α) : RayTree α → RayTree α → RayTree α
  | point a, point b => point (μ a b)
  | point a, above b _ => point (μ a b)
  | above a _, point b => point (μ a b)
  | above a s, above b t =>
      if a = b then above a (meet μ s t) else point (μ a b)

theorem meet_below_left {r : α → α → Prop} {μ : α → α → α}
    (hμ : ∀ a b, r (μ a b) a) (s t : RayTree α) :
    Below r (meet μ s t) s := by
  induction s generalizing t with
  | point a =>
    cases t <;> exact hμ _ _
  | above a s ih =>
    cases t with
    | point b => exact hμ _ _
    | above b t =>
      by_cases hab : a = b
      · subst b
        simp only [meet, ↓reduceIte, below_above_above]
        exact ⟨True.intro, ih t⟩
      · simp only [meet, hab, ↓reduceIte, below_point_above]
        exact hμ _ _

theorem meet_below_right {r : α → α → Prop} {μ : α → α → α}
    (hμ : ∀ a b, r (μ a b) b) (s t : RayTree α) :
    Below r (meet μ s t) t := by
  induction s generalizing t with
  | point a =>
    cases t <;> exact hμ _ _
  | above a s ih =>
    cases t with
    | point b => exact hμ _ _
    | above b t =>
      by_cases hab : a = b
      · subst b
        simp only [meet, ↓reduceIte, below_above_above]
        exact ⟨True.intro, ih t⟩
      · simp only [meet, hab, ↓reduceIte, below_point_above]
        exact hμ _ _

theorem below_meet {r : α → α → Prop} {μ : α → α → α}
    (hμ : ∀ {a b c}, r c a → r c b → r c (μ a b))
    {s t w : RayTree α} (hs : Below r w s) (ht : Below r w t) :
    Below r w (meet μ s t) := by
  induction s generalizing t w with
  | point a =>
    cases w with
    | above c u => exact False.elim hs
    | point c =>
      cases t <;> exact hμ hs ht
  | above a s ih =>
    cases t with
    | point b =>
      cases w with
      | above c u => exact False.elim ht
      | point c => exact hμ hs ht
    | above b t =>
      by_cases hab : a = b
      · subst b
        simp only [meet, ↓reduceIte]
        cases w with
        | point c => exact hs
        | above c u =>
          obtain ⟨rfl, hs⟩ := hs
          exact ⟨rfl, ih hs ht.2⟩
      · simp only [meet, hab, ↓reduceIte]
        cases w with
        | point c => exact hμ hs ht
        | above c u =>
          exact False.elim (hab (hs.1.symm.trans ht.1))

/-- Together, the preceding lemmas validate the manuscript's explicit meet
formula as the greatest lower bound, not only as a binary operation. -/
theorem below_meet_iff {r : α → α → Prop} {μ : α → α → α}
    (htrans : ∀ {a b c}, r a b → r b c → r a c)
    (hleft : ∀ a b, r (μ a b) a) (hright : ∀ a b, r (μ a b) b)
    (hgreatest : ∀ {a b c}, r c a → r c b → r c (μ a b))
    {s t w : RayTree α} :
    Below r w (meet μ s t) ↔ Below r w s ∧ Below r w t := by
  constructor
  · intro h
    exact ⟨below_trans (r := r) htrans h (meet_below_left (r := r) hleft s t),
      below_trans (r := r) htrans h (meet_below_right (r := r) hright s t)⟩
  · rintro ⟨hs, ht⟩
    exact below_meet hgreatest hs ht

end Meet

/-- Strict comparison, kept independent of any chosen order typeclass. -/
def StrictBelow (r : α → α → Prop) (s t : RayTree α) : Prop :=
  Below r s t ∧ s ≠ t

/-- The first coordinate identifies the initial ray. -/
def first : RayTree α → α
  | point a => a
  | above a _ => a

@[simp] theorem point_below_iff {r : α → α → Prop} (a : α) (t : RayTree α) :
    Below r (point a) t ↔ r a (first t) := by
  cases t <;> exact Iff.rfl

/-- Absence of a least point on the ray gives absence of a least point in the tree. -/
theorem exists_strict_below {r : α → α → Prop}
    (hr : ∀ a, ∃ b, r b a ∧ b ≠ a) (s : RayTree α) :
    ∃ t, StrictBelow r t s := by
  obtain ⟨b, hb, hne⟩ := hr (first s)
  refine ⟨point b, (point_below_iff b s).2 hb, ?_⟩
  intro heq
  have : b = first s := congrArg first heq
  exact hne this

/-- Every node has a strict upper node, even if the coordinate order has a top. -/
theorem exists_strict_above {r : α → α → Prop}
    (hr : ∀ a, r a a) (s : RayTree α) : ∃ t, StrictBelow r s t := by
  induction s with
  | point a => exact ⟨above a (point a), hr a, by intro h; cases h⟩
  | above a s ih =>
    obtain ⟨t, hst, hne⟩ := ih
    refine ⟨above a t, ⟨rfl, hst⟩, ?_⟩
    exact fun h => hne (RayTree.above.inj h).2

/-- Dense rays without a least element yield dense comparable intervals. -/
theorem exists_between {r : α → α → Prop}
    (hrefl : ∀ a, r a a)
    (hnoMin : ∀ a, ∃ b, r b a ∧ b ≠ a)
    (hdense : ∀ a b, r a b → a ≠ b →
      ∃ c, r a c ∧ a ≠ c ∧ r c b ∧ c ≠ b)
    {s t : RayTree α} (hst : StrictBelow r s t) :
    ∃ u, StrictBelow r s u ∧ StrictBelow r u t := by
  induction s generalizing t with
  | point a =>
    cases t with
    | point b =>
      have hab : a ≠ b := fun h => hst.2 (congrArg point h)
      obtain ⟨c, hac, hnac, hcb, hncb⟩ := hdense a b hst.1 hab
      exact ⟨point c, ⟨hac, fun h => hnac (RayTree.point.inj h)⟩,
        hcb, fun h => hncb (RayTree.point.inj h)⟩
    | above b t =>
      by_cases hab : a = b
      · subst b
        obtain ⟨u, hut, hne⟩ := exists_strict_below hnoMin t
        exact ⟨above a u, ⟨hrefl a, by intro h; cases h⟩,
          ⟨rfl, hut⟩, fun h => hne (RayTree.above.inj h).2⟩
      · obtain ⟨c, hac, hnac, hcb, _⟩ := hdense a b hst.1 hab
        exact ⟨point c, ⟨hac, fun h => hnac (RayTree.point.inj h)⟩,
          hcb, by intro h; cases h⟩
  | above a s ih =>
    cases t with
    | point b => exact False.elim hst.1
    | above b t =>
      obtain ⟨hab, hbelow⟩ := hst.1
      subst b
      have hne : s ≠ t := fun h => hst.2 (congrArg (above a) h)
      obtain ⟨u, hsu, hut⟩ := ih ⟨hbelow, hne⟩
      exact ⟨above a u, ⟨⟨rfl, hsu.1⟩, fun h => hsu.2 (RayTree.above.inj h).2⟩,
        ⟨rfl, hut.1⟩, fun h => hut.2 (RayTree.above.inj h).2⟩

section Maps

variable {β : Type v}

/-- Apply a map to every ray coordinate. -/
def map (f : α → β) : RayTree α → RayTree β
  | point a => point (f a)
  | above a s => above (f a) (map f s)

@[simp] theorem map_id (s : RayTree α) : map id s = s := by
  induction s with
  | point a => rfl
  | above a s ih => simp only [map, id_eq, ih]

@[simp] theorem map_map {γ : Type w} (f : α → β) (g : β → γ) (s : RayTree α) :
    map g (map f s) = map (fun a => g (f a)) s := by
  induction s with
  | point a => rfl
  | above a s ih => simp only [map, ih]

theorem map_injective {f : α → β}
    (hf : ∀ {a b}, f a = f b → a = b) :
    ∀ {s t}, map f s = map f t → s = t := by
  intro s
  induction s with
  | point a =>
    intro t h
    cases t with
    | point b => exact congrArg point (hf (RayTree.point.inj h))
    | above b u => cases h
  | above a s ih =>
    intro t h
    cases t with
    | point b => cases h
    | above b t =>
      obtain ⟨hab, hst⟩ := RayTree.above.inj h
      have hab' := hf hab
      subst b
      exact congrArg (above a) (ih hst)

/-- Order embeddings of the ray induce embeddings of the pseudotree order. -/
theorem below_map_iff {f : α → β} {r : α → α → Prop} {q : β → β → Prop}
    (hf : ∀ {a b}, f a = f b → a = b)
    (hr : ∀ a b, q (f a) (f b) ↔ r a b) (s t : RayTree α) :
    Below q (map f s) (map f t) ↔ Below r s t := by
  induction s generalizing t with
  | point a => cases t <;> exact hr _ _
  | above a s ih =>
    cases t with
    | point b => exact Iff.rfl
    | above b t =>
      change (f a = f b ∧ Below q (map f s) (map f t)) ↔
        (a = b ∧ Below r s t)
      exact and_congr ⟨hf, congrArg f⟩ (ih t)

/-- Coordinate maps preserving the ray meet preserve the pseudotree meet. -/
theorem map_meet [DecidableEq α] [DecidableEq β]
    {f : α → β} {μ : α → α → α} {ν : β → β → β}
    (hf : ∀ {a b}, f a = f b → a = b)
    (hμ : ∀ a b, f (μ a b) = ν (f a) (f b)) (s t : RayTree α) :
    map f (meet μ s t) = meet ν (map f s) (map f t) := by
  induction s generalizing t with
  | point a => cases t <;> exact congrArg point (hμ _ _)
  | above a s ih =>
    cases t with
    | point b => exact congrArg point (hμ _ _)
    | above b t =>
      by_cases hab : a = b
      · subst b
        simp only [meet, ↓reduceIte, map]
        rw [ih]
      · have hfab : f a ≠ f b := fun h => hab (hf h)
        simp only [meet, hab, hfab, ↓reduceIte, map]
        exact congrArg point (hμ _ _)

end Maps
end RayTree
end AllThoseBigRamsey.Pseudotree
