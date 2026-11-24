import PseudotreeValidation.SparseModel
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Vector
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Interval.Set.Infinite

/-!
# Geometric refinements used in diary unavoidability

These lemmas work with actual order embeddings into the concrete pseudotree.
They locate an entire rational suborder in one ambient ray and then refine
it to words sharing an arbitrarily long literal prefix.
-/

namespace AllThoseBigRamsey.Pseudotree

namespace RayTree

variable {α : Type u} [LinearOrder α]

/-- The coordinates before the terminal binary ray. -/
def rayStem : RayTree α → List α
  | .point _ => []
  | .above a s => a :: rayStem s

/-- The terminal coordinate on the ray. -/
def rayValue : RayTree α → α
  | .point a => a
  | .above _ s => rayValue s

/-- A point on the ray specified by a fixed sequence of preceding coordinates. -/
def onRay (stem : List α) (a : α) : RayTree α :=
  stem.foldr .above (.point a)

@[simp] theorem onRay_nil (a : α) : onRay [] a = .point a := rfl
@[simp] theorem onRay_cons (b : α) (stem : List α) (a : α) :
    onRay (b :: stem) a = .above b (onRay stem a) := rfl

@[simp] theorem onRay_stem_value (s : RayTree α) : onRay (rayStem s) (rayValue s) = s := by
  induction s with
  | point a => rfl
  | above a s ih => simpa only [rayStem, rayValue, onRay_cons] using congrArg (RayTree.above a) ih

@[simp] theorem rayStem_onRay (stem : List α) (a : α) : rayStem (onRay stem a) = stem := by
  induction stem with
  | nil => rfl
  | cons b stem ih => simpa [rayStem] using congrArg (List.cons b) ih

@[simp] theorem rayValue_onRay (stem : List α) (a : α) : rayValue (onRay stem a) = a := by
  induction stem with
  | nil => rfl
  | cons b stem ih => exact ih

@[simp] theorem onRay_le_iff (stem : List α) (a b : α) : onRay stem a ≤ onRay stem b ↔ a ≤ b := by
  induction stem with
  | nil => rfl
  | cons c stem ih =>
      change (c = c ∧ onRay stem a ≤ onRay stem b) ↔ a ≤ b
      simpa only [true_and] using ih

def rayEmbedding (stem : List α) : α ↪o RayTree α where
  toFun := onRay stem
  inj' := by
    intro a b hab
    simpa using congrArg rayValue hab
  map_rel_iff' := fun {a b} => onRay_le_iff stem a b

/-- Ray depth is monotone along a predecessor chain. -/
theorem stem_length_mono {s t : RayTree α} (hst : s ≤ t) :
    (rayStem s).length ≤ (rayStem t).length := by
  induction s generalizing t with
  | point a => simp [rayStem]
  | above a s ih =>
      cases t with
      | point b => exact False.elim hst
      | above b t =>
          obtain ⟨rfl, hst⟩ := hst
          simpa [rayStem] using ih hst

/-- Comparable nodes at the same ray depth are on the same ambient ray. -/
theorem stem_eq_of_le_of_length_eq {s t : RayTree α} (hst : s ≤ t)
    (hlen : (rayStem s).length = (rayStem t).length) : rayStem s = rayStem t := by
  induction s generalizing t with
  | point a =>
      cases t with
      | point b => rfl
      | above b t => simp [rayStem] at hlen
  | above a s ih =>
      cases t with
      | point b => exact False.elim hst
      | above b t =>
          obtain ⟨rfl, hst⟩ := hst
          exact congrArg (List.cons a) (ih hst (by simpa [rayStem] using hlen))

/-- A nonempty interval in any densely ordered subcopy contains a nonempty
terminal interval whose images all lie on one ambient ray. Choose a point
of maximal ambient ray depth; no finite convex-partition theorem is needed. -/
theorem exists_interval_single_ray {M : Type v} [PartialOrder M] [DenselyOrdered M]
    (f : M ↪o RayTree α) {y w : M} (hyw : y < w) :
    ∃ u, y < u ∧ u < w ∧ ∀ z, u < z → z < w → rayStem (f z) = rayStem (f u) := by
  classical
  let D : Set ℕ := {d | ∃ z : M, y < z ∧ z < w ∧ (rayStem (f z)).length = d}
  have hDfinite : D.Finite := (Set.finite_le_nat (rayStem (f w)).length).subset (by
    rintro d ⟨z, _, hzw, rfl⟩
    exact stem_length_mono (f.monotone hzw.le))
  have hD : D.Nonempty := by
    obtain ⟨z, hyz, hzw⟩ := _root_.exists_between hyw
    exact ⟨_, z, hyz, hzw, rfl⟩
  have hfin : hDfinite.toFinset.Nonempty := by simpa using hD
  let d := hDfinite.toFinset.max' hfin
  have hd : d ∈ D := by
    exact hDfinite.mem_toFinset.mp (Finset.max'_mem _ hfin)
  obtain ⟨u, hyu, huw, hu⟩ := hd
  refine ⟨u, hyu, huw, ?_⟩
  intro z huz hzw
  apply (stem_eq_of_le_of_length_eq (f.monotone huz.le) ?_).symm
  apply le_antisymm
  · exact stem_length_mono (f.monotone huz.le)
  · have hzD : (rayStem (f z)).length ∈ D := ⟨z, hyu.trans huz, hzw, rfl⟩
    rw [hu]
    exact Finset.le_max' _ _ (hDfinite.mem_toFinset.mpr hzD)

end RayTree

namespace LowerGeometry

/-- The predecessor interval carries its inherited linear order. -/
noncomputable abbrev intervalLinearOrder {M : Type u} [PartialOrder M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x) (y w : M) :
    LinearOrder (Set.Ioo y w) where
  toPartialOrder := inferInstance
  le_total x z := htree x.property.2.le z.property.2.le
  toDecidableLE := Classical.decRel _
  toDecidableEq := Classical.decEq _

/-- An entire open interval in a countable dense meet-tree is a rational
order. This states the actual subtype, with no density assumption on a set. -/
theorem interval_orderIso_rat {M : Type u} [PartialOrder M] [DenselyOrdered M] [Countable M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    {y w : M} (hyw : y < w) :
    letI := intervalLinearOrder htree y w
    Nonempty (ℚ ≃o Set.Ioo y w) := by
  letI := intervalLinearOrder htree y w
  letI : Nonempty (Set.Ioo y w) := Set.nonempty_Ioo_subtype hyw
  exact Order.iso_of_countable_dense ℚ (Set.Ioo y w)

/-- A rational suborder lying entirely on a specified ambient ray. -/
structure RayCopy where
  embedding : ℚ ↪o TernaryModel
  stem : List BinaryRay
  same_ray : ∀ q, RayTree.rayStem (embedding q) = stem

instance : CoeFun RayCopy (fun _ => ℚ → TernaryModel) := ⟨fun Q => Q.embedding⟩

/-- Every open interval in an actual self-copy contains a single-ray rational
suborder. The output's points are explicitly images of points in the original
interval. -/
theorem interval_rayCopy (f : TernaryModel ↪o TernaryModel)
    {y w : TernaryModel} (hyw : y < w) :
    ∃ Q : RayCopy, ∀ q, ∃ z, y < z ∧ z < w ∧ Q q = f z := by
  obtain ⟨u, hyu, huw, hray⟩ := RayTree.exists_interval_single_ray f hyw
  letI := intervalLinearOrder RayTree.le_or_ge_of_le_common u w
  obtain ⟨e⟩ := interval_orderIso_rat RayTree.le_or_ge_of_le_common huw
  let E : ℚ ↪o TernaryModel := e.toOrderEmbedding.trans (OrderEmbedding.subtype _)
  let Q : RayCopy := ⟨E.trans f, RayTree.rayStem (f u), fun q =>
    hray (E q) (e q).property.1 (e q).property.2⟩
  refine ⟨Q, fun q => ⟨E q, ?_, (e q).property.2, rfl⟩⟩
  exact hyu.trans (e q).property.1

/-- Binary prefix cylinders are convex for the manuscript's ray order. -/
theorem binary_prefix_of_between (p a b c : List Bool)
    (hac : binaryLE (p ++ a) c = true) (hcb : binaryLE c (p ++ b) = true) :
    p <+: c := by
  induction p generalizing c with
  | nil => exact List.nil_prefix
  | cons d p ih =>
      cases c with
      | nil => cases d <;> simp [binaryLE] at hac hcb
      | cons e c =>
          cases d <;> cases e <;> simp only [List.cons_append, binaryLE] at hac hcb
          · obtain ⟨t, ht⟩ := ih c hac hcb
            exact ⟨t, congrArg (List.cons false) ht⟩
          · simp at hac
          · simp at hcb
          · obtain ⟨t, ht⟩ := ih c hac hcb
            exact ⟨t, congrArg (List.cons true) ht⟩

private def prefixColour (n : ℕ) (s : List Bool) :
    Σ k : Fin (n + 1), List.Vector Bool k.val :=
  ⟨⟨(s.take n).length, by simp⟩, ⟨s.take n, rfl⟩⟩

private theorem take_length_of_distinct {s t : List Bool} {n : ℕ}
    (hne : s ≠ t) (heq : s.take n = t.take n) : n ≤ s.length ∧ n ≤ t.length := by
  have hlen := congrArg List.length heq
  simp only [List.length_take] at hlen
  have hs : n ≤ s.length := by
    by_contra h
    have hs' : s.length ≤ n := by omega
    have ht' : t.length ≤ n := by omega
    simp only [List.take_of_length_le hs', List.take_of_length_le ht'] at heq
    exact hne heq
  have ht : n ≤ t.length := by omega
  exact ⟨hs, ht⟩

/-- A rational suborder of the binary ray contains a rational suborder in
one arbitrarily long binary prefix cylinder. Distinct points with equal
finite prefix colours automatically avoid all shorter exceptional words. -/
theorem binary_common_prefix (e : ℚ ↪o BinaryRay) (n : ℕ) :
    ∃ p : List Bool, p.length = n ∧ ∃ g : ℚ ↪o BinaryRay,
      Set.range g ⊆ Set.range e ∧ ∀ q, p <+: (g q).word := by
  classical
  obtain ⟨a, b, hab, hcol⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun q : ℚ => prefixColour n (e q).word)
  have heq : (e a).word.take n = (e b).word.take n :=
    congrArg (fun x : Σ k : Fin (n + 1), List.Vector Bool k.val => x.2.val) hcol
  have hne : (e a).word ≠ (e b).word := by
    intro h
    exact hab (e.injective (BinaryRay.ext h))
  suffices H : ∀ a b : ℚ, a < b → (e a).word.take n = (e b).word.take n →
      n ≤ (e a).word.length →
      ∃ p : List Bool, p.length = n ∧ ∃ g : ℚ ↪o BinaryRay,
        Set.range g ⊆ Set.range e ∧ ∀ q, p <+: (g q).word by
    have hlen := take_length_of_distinct hne heq
    rcases lt_or_gt_of_ne hab with h | h
    · exact H a b h heq hlen.1
    · exact H b a h heq.symm hlen.2
  intro a b hab heq hlen
  let p := (e a).word.take n
  letI : Nonempty (Set.Ioo a b) := Set.nonempty_Ioo_subtype hab
  obtain ⟨i⟩ := Order.iso_of_countable_dense ℚ (Set.Ioo a b)
  let g : ℚ ↪o BinaryRay :=
    i.toOrderEmbedding.trans ((OrderEmbedding.subtype _).trans e)
  refine ⟨p, by simp [p, List.length_take, Nat.min_eq_left hlen], g, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    exact ⟨(i q).val, rfl⟩
  · intro q
    have ha : binaryLE (p ++ (e a).word.drop n) (g q).word = true := by
      rw [show p ++ (e a).word.drop n = (e a).word from List.take_append_drop n _]
      exact (e.monotone (i q).property.1.le)
    have hb : binaryLE (g q).word (p ++ (e b).word.drop n) = true := by
      rw [show p = (e b).word.take n from heq, List.take_append_drop]
      exact (e.monotone (i q).property.2.le)
    exact binary_prefix_of_between p _ _ _ ha hb

/-- The literal root of a block-coordinate ray ends immediately after its
last separator (or is empty for the initial ray). -/
def rayRoot : List BinaryRay → List TernaryLetter
  | [] => []
  | a :: stem => a.word.map binaryLetter ++ .one :: rayRoot stem

@[simp] theorem fromBlocks_onRay (stem : List BinaryRay) (a : BinaryRay) :
    fromBlocks (RayTree.onRay stem a) = rayRoot stem ++ a.word.map binaryLetter := by
  induction stem with
  | nil => rfl
  | cons b stem ih =>
      simpa only [RayTree.onRay_cons, fromBlocks, RayTree.map, printWord,
        rayRoot, List.append_assoc, List.cons_append] using
        congrArg (fun w => b.word.map binaryLetter ++ .one :: w) ih

namespace RayCopy

/-- The terminal coordinate realizes a single-ray rational suborder in the
literal binary ray. -/
def coordinates (Q : RayCopy) : ℚ ↪o BinaryRay where
  toFun q := RayTree.rayValue (Q q)
  inj' := by
    intro a b hab
    apply Q.embedding.injective
    calc
      Q a = RayTree.onRay Q.stem (RayTree.rayValue (Q a)) := by
        rw [← Q.same_ray a, RayTree.onRay_stem_value]
      _ = RayTree.onRay Q.stem (RayTree.rayValue (Q b)) := congrArg _ hab
      _ = Q b := by rw [← Q.same_ray b, RayTree.onRay_stem_value]
  map_rel_iff' := by
    intro a b
    change RayTree.rayValue (Q a) ≤ RayTree.rayValue (Q b) ↔ a ≤ b
    rw [← RayTree.onRay_le_iff Q.stem]
    have ha : RayTree.onRay Q.stem (RayTree.rayValue (Q a)) = Q a := by
      rw [← Q.same_ray a, RayTree.onRay_stem_value]
    have hb : RayTree.onRay Q.stem (RayTree.rayValue (Q b)) = Q b := by
      rw [← Q.same_ray b, RayTree.onRay_stem_value]
    rw [ha, hb]
    exact Q.embedding.le_iff_le

@[simp] theorem fromBlocks_eq (Q : RayCopy) (q : ℚ) :
    fromBlocks (Q q) = rayRoot Q.stem ++ (Q.coordinates q).word.map binaryLetter := by
  have h : Q q = RayTree.onRay Q.stem (Q.coordinates q) := by
    change Q q = RayTree.onRay Q.stem (RayTree.rayValue (Q q))
    rw [← Q.same_ray q, RayTree.onRay_stem_value]
  rw [h, fromBlocks_onRay]

/-- Refine a genuine rational suborder on one ambient ray to an arbitrarily
long common literal prefix, retaining its exact ray and its source range. -/
theorem common_prefix (Q : RayCopy) (L : ℕ) (hL : (rayRoot Q.stem).length ≤ L) :
    ∃ R : RayCopy, R.stem = Q.stem ∧ Set.range R.embedding ⊆ Set.range Q.embedding ∧
      ∃ p : List TernaryLetter, p.length = L ∧ ∀ q, p <+: fromBlocks (R q) := by
  obtain ⟨p, hp, g, hsub, hprefix⟩ := binary_common_prefix Q.coordinates
    (L - (rayRoot Q.stem).length)
  let R : RayCopy := ⟨g.trans (RayTree.rayEmbedding Q.stem), Q.stem,
    fun q => RayTree.rayStem_onRay Q.stem (g q)⟩
  refine ⟨R, rfl, ?_, rayRoot Q.stem ++ p.map binaryLetter, ?_, ?_⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨t, ht⟩ := hsub ⟨q, rfl⟩
    refine ⟨t, ?_⟩
    change Q t = RayTree.onRay Q.stem (g q)
    rw [← ht]
    change Q t = RayTree.onRay Q.stem (RayTree.rayValue (Q t))
    rw [← Q.same_ray t, RayTree.onRay_stem_value]
  · simp only [List.length_append, List.length_map, hp]
    omega
  · intro q
    change rayRoot Q.stem ++ p.map binaryLetter <+:
      fromBlocks (RayTree.onRay Q.stem (g q))
    rw [fromBlocks_onRay]
    obtain ⟨tail, htail⟩ := hprefix q
    refine ⟨tail.map binaryLetter, ?_⟩
    rw [List.append_assoc, ← List.map_append, htail]

end RayCopy

end LowerGeometry
end AllThoseBigRamsey.Pseudotree
