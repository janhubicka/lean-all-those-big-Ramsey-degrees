import PseudotreeValidation.HeterogeneousMatrices
import PseudotreeValidation.HalpernLauchli
import Mathlib.Data.List.Induction

/-!
# Full word trees as actual Halpern–Läuchli factors

The tree order in this module is the initial-segment order. It is distinct
from the pseudotree order on ternary words. We build the library's
`AmbientTree` for any finite nonempty alphabet, identify its level with
word length, and specialize it to binary and ternary alphabets.
-/

namespace AllThoseBigRamsey.Pseudotree.WordTrees

open Milliken Milliken.GeneralTree

/-- A type wrapper to keep the prefix tree order separate from other list
orders used by the pseudotree model. -/
@[ext] structure Node (α : Type) where
  letters : List α
  deriving DecidableEq

variable {α : Type}

instance : PartialOrder (Node α) where
  le x y := x.letters <+: y.letters
  le_refl _ := List.prefix_rfl
  le_trans _ _ _ := List.IsPrefix.trans
  le_antisymm x y hxy hyx := Node.ext (hxy.eq_of_length_le hyx.length_le)

@[simp] theorem le_iff {x y : Node α} : x ≤ y ↔ x.letters <+: y.letters := Iff.rfl

instance : OrderBot (Node α) where
  bot := ⟨[]⟩
  bot_le _ := List.nil_prefix

theorem length_lt_of_lt {x y : Node α} (h : x < y) :
    x.letters.length < y.letters.length := by
  have hle := h.le.length_le
  by_contra hnot
  have heq : x = y := Node.ext (h.le.eq_of_length_le (by omega))
  exact h.ne heq

private def common [DecidableEq α] : List α → List α → List α
  | [], _ => []
  | _, [] => []
  | a :: s, b :: t => if a = b then a :: common s t else []

private theorem common_prefix_left [DecidableEq α] (s t : List α) :
    common s t <+: s := by
  induction s generalizing t with
  | nil => simp [common]
  | cons a s ih =>
      cases t with
      | nil => simp [common]
      | cons b t =>
          by_cases h : a = b
          · simp [common, h, ih]
          · simp [common, h]

private theorem common_prefix_right [DecidableEq α] (s t : List α) :
    common s t <+: t := by
  induction s generalizing t with
  | nil => simp [common]
  | cons a s ih =>
      cases t with
      | nil => simp [common]
      | cons b t =>
          by_cases h : a = b
          · simp [common, h, ih]
          · simp [common, h]

private theorem prefix_common [DecidableEq α] {r s t : List α}
    (hs : r <+: s) (ht : r <+: t) : r <+: common s t := by
  induction r generalizing s t with
  | nil => exact List.nil_prefix
  | cons a r ih =>
      cases s with
      | nil => simp at hs
      | cons b s =>
          cases t with
          | nil => simp at ht
          | cons c t =>
              obtain ⟨hab, hs'⟩ := List.cons_prefix_cons.mp hs
              obtain ⟨hac, ht'⟩ := List.cons_prefix_cons.mp ht
              subst b c
              simpa [common] using ih hs' ht'

instance [DecidableEq α] : SemilatticeInf (Node α) where
  inf x y := ⟨common x.letters y.letters⟩
  inf_le_left _ _ := common_prefix_left _ _
  inf_le_right _ _ := common_prefix_right _ _
  le_inf _ _ _ := prefix_common

instance : PredOrder (Node α) where
  pred x := ⟨x.letters.dropLast⟩
  pred_le x := List.dropLast_prefix x.letters
  min_of_le_pred := by
    intro x hx
    have hlen := hx.length_le
    simp only [List.length_dropLast] at hlen
    have hz : x.letters = [] := List.length_eq_zero_iff.mp (by omega)
    have heq : x = ⊥ := Node.ext hz
    simpa only [heq] using (isMin_bot : IsMin (⊥ : Node α))
  le_pred_of_lt := by
    intro x y hxy
    apply List.prefix_of_prefix_length_le hxy.le (List.dropLast_prefix _)
    have hlen := length_lt_of_lt hxy
    simp only [List.length_dropLast]
    omega

@[simp] theorem pred_append_singleton (s : List α) (a : α) :
    Order.pred (⟨s ++ [a]⟩ : Node α) = ⟨s⟩ := by
  apply Node.ext
  change (s ++ [a]).dropLast = s
  simp

private theorem pred_iterate_append (s t : List α) :
    (Order.pred^[t.length]) (⟨s ++ t⟩ : Node α) = ⟨s⟩ := by
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t a ih =>
      simpa only [List.length_append, List.length_singleton,
        Function.iterate_succ_apply, ← List.append_assoc, pred_append_singleton] using ih

instance : IsPredArchimedean (Node α) where
  exists_pred_iterate_of_le := by
    intro x y hxy
    obtain ⟨t, ht⟩ := hxy
    refine ⟨t.length, ?_⟩
    have heq : y = ⟨x.letters ++ t⟩ := Node.ext ht.symm
    rw [heq]
    exact pred_iterate_append x.letters t

theorem append_singleton_covBy (s : List α) (a : α) :
    (⟨s⟩ : Node α) ⋖ ⟨s ++ [a]⟩ := by
  constructor
  · apply lt_of_le_of_ne (List.prefix_append _ _)
    intro h
    have := congrArg (fun x : Node α => x.letters.length) h
    simp at this
  · intro z hxz hzy
    have h1 := length_lt_of_lt hxz
    have h2 := length_lt_of_lt hzy
    change s.length < z.letters.length at h1
    simp only [List.length_append, List.length_singleton] at h2
    omega

theorem covBy_append_singleton {x y : Node α} (h : x ⋖ y) :
    ∃ a : α, y = ⟨x.letters ++ [a]⟩ := by
  have hy : y.letters ≠ [] := by
    have := length_lt_of_lt h.lt
    intro hz
    simp [hz] at this
  refine ⟨y.letters.getLast hy, ?_⟩
  have hp := congrArg Node.letters (Order.pred_eq_of_covBy h)
  apply Node.ext
  change y.letters = x.letters ++ [y.letters.getLast hy]
  rw [← hp]
  exact (List.dropLast_append_getLast hy).symm

/-- The full word tree over a finite nonempty alphabet. -/
def ambientTree (α : Type) [Finite α] [Nonempty α] [DecidableEq α] : AmbientTree where
  toRootedTree := { α := Node α }
  finite_children x := by
    apply (Set.finite_range (fun a : α => (⟨x.letters ++ [a]⟩ : Node α))).subset
    intro y hy
    obtain ⟨a, rfl⟩ := covBy_append_singleton hy
    exact Set.mem_range_self a
  has_child x := by
    obtain ⟨a⟩ := ‹Nonempty α›
    exact ⟨⟨x.letters ++ [a]⟩, append_singleton_covBy _ _⟩

@[simp] theorem level_eq_length [Finite α] [Nonempty α] [DecidableEq α]
    (x : Node α) : (ambientTree α).level x = x.letters.length := by
  obtain ⟨s⟩ := x
  induction s using List.reverseRecOn with
  | nil => exact (ambientTree α).level_root
  | append_singleton s a ih =>
      rw [(ambientTree α).level_covBy (append_singleton_covBy s a), ih]
      simp

/-- The actual binary alphabet used by the manuscript, inside `Fin 3`. -/
abbrev BinaryLetter := {a : Fin 3 // a ≠ 1}

instance : Nonempty BinaryLetter := ⟨⟨0, by decide⟩⟩

def binaryTree : AmbientTree := ambientTree BinaryLetter
def ternaryTree : AmbientTree := ambientTree (Fin 3)

/-- Dense-matrix HL specialized to full word trees. All nodes and all
finite demands in the conclusion are ordinary finite words; the level is
their common word length. Different coordinates may use different alphabets. -/
theorem wordFiniteDemandDenseMatrices
    (d : ℕ) (hd : 0 < d) (A : Fin d → Type)
    [∀ i, Finite (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (n : ℕ) (colour : (∀ i, List (A i)) → Fin (n + 1)) :
    ∃ base : (∀ i, List (A i)), ∃ a : Fin (n + 1),
      ∀ F : (i : Fin d) → Finset (List (A i)),
        (∀ i, ∀ x ∈ F i, base i <+: x) →
        ∀ m : ℕ, ∃ l : ℕ, m ≤ l ∧
          ∃ X : (i : Fin d) → Set (List (A i)),
            (∀ i, ∀ x ∈ X i, x.length = l) ∧
            (∀ i, ∀ x ∈ F i, ∃ y ∈ X i, x <+: y) ∧
            ∀ x : (∀ i, List (A i)), (∀ i, x i ∈ X i) → colour x = a := by
  classical
  let T : Fin d → AmbientTree := fun i => ambientTree (A i)
  obtain ⟨base, a, hall⟩ := heterogeneousFiniteDemandDenseMatrices d hd T n
    (fun x => colour (fun i => (x i).letters))
  refine ⟨(fun i => (base i).letters), a, ?_⟩
  intro F hF m
  let (i : Fin d) : DecidableEq (Node (A i)) := Classical.decEq _
  let F' : (i : Fin d) → Finset (T i) := fun i => (F i).image Node.mk
  have hF' : ∀ i, ∀ x ∈ F' i, base i ≤ x := by
    intro i x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hF i y hy
  obtain ⟨l, hml, X, hLevel, hDom, hMono⟩ := hall F' hF' m
  refine ⟨l, hml, (fun i => {x | (⟨x⟩ : Node (A i)) ∈ X i}), ?_, ?_, ?_⟩
  · intro i x hx
    simpa only [T, level_eq_length] using hLevel i ⟨x⟩ hx
  · intro i x hx
    have hx' : (⟨x⟩ : Node (A i)) ∈ F' i := by
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hDom i ⟨x⟩ hx'
    exact ⟨y.letters, hy, hxy⟩
  · intro x hx
    exact hMono (fun i => ⟨x i⟩) hx

/-- `true` selects a binary ray; `false` selects a full ternary cone. -/
def FactorLetter : Bool → Type
  | true => BinaryLetter
  | false => Fin 3

instance (b : Bool) : Fintype (FactorLetter b) := by
  cases b <;> dsimp [FactorLetter] <;> infer_instance

instance (b : Bool) : Nonempty (FactorLetter b) := by
  cases b <;> dsimp [FactorLetter] <;> infer_instance

instance (b : Bool) : DecidableEq (FactorLetter b) := by
  cases b <;> dsimp [FactorLetter] <;> infer_instance

def letterValue : (b : Bool) → FactorLetter b → Fin 3
  | true, a => a.1
  | false, a => a

theorem letterValue_injective (b : Bool) : Function.Injective (letterValue b) := by
  cases b
  · exact Function.injective_id
  · exact Subtype.val_injective

/-- A factor word, placed above the specified original ternary root. -/
def place (b : Bool) (root : List (Fin 3)) (s : List (FactorLetter b)) : List (Fin 3) :=
  root ++ s.map (letterValue b)

@[simp] theorem place_length (b : Bool) (root : List (Fin 3))
    (s : List (FactorLetter b)) : (place b root s).length = root.length + s.length := by
  simp [place]

private theorem map_prefix_map_iff {β : Type} {f : α → β}
    (hf : Function.Injective f) (s t : List α) :
    s.map f <+: t.map f ↔ s <+: t := by
  induction s generalizing t with
  | nil => simp
  | cons a s ih =>
      cases t with
      | nil => simp
      | cons b t => simp [hf.eq_iff, ih]

@[simp] theorem place_prefix_iff (b : Bool) (root : List (Fin 3))
    (s t : List (FactorLetter b)) :
    place b root s <+: place b root t ↔ s <+: t := by
  rw [place, place, List.prefix_append_right_inj]
  exact map_prefix_map_iff (letterValue_injective b) s t

theorem binary_tail_range (t : List (Fin 3)) :
    (∃ s : List BinaryLetter, s.map Subtype.val = t) ↔ ∀ a ∈ t, a ≠ 1 := by
  constructor
  · rintro ⟨s, rfl⟩ a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact b.2
  · intro ht
    induction t with
    | nil => exact ⟨[], rfl⟩
    | cons a t ih =>
        have ha : a ≠ 1 := ht a (by simp)
        obtain ⟨s, hs⟩ := ih (fun b hb => ht b (by simp [hb]))
        exact ⟨⟨a, ha⟩ :: s, by simp [hs]⟩

/-- The binary factor has exactly the manuscript's binary-ray image. -/
theorem binary_place_range (root x : List (Fin 3)) :
    (∃ s, place true root s = x) ↔
      ∃ t : List (Fin 3), (∀ a ∈ t, a ≠ 1) ∧ root ++ t = x := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.map Subtype.val, (binary_tail_range _).mp ⟨s, rfl⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨s, hs⟩ := (binary_tail_range t).mpr ht
    refine ⟨s, ?_⟩
    change root ++ s.map Subtype.val = root ++ t
    rw [hs]

/-- The ternary factor has exactly the full-cone image. -/
theorem ternary_place_range (root x : List (Fin 3)) :
    (∃ s, place false root s = x) ↔ root <+: x := by
  change (∃ s : List (Fin 3), root ++ s.map id = x) ↔ root <+: x
  simp only [List.map_id, List.IsPrefix]

/-- The finite-demand dense-matrix theorem for any finite mixture of the
actual binary and ternary alphabets. This is an ordinary HL input; it does
not assert a ray-preserving mixed strong-subtree theorem. -/
theorem binaryTernaryFiniteDemandDenseMatrices
    (d : ℕ) (hd : 0 < d) (binary : Fin d → Bool)
    (n : ℕ) (colour : (∀ i, List (FactorLetter (binary i))) → Fin (n + 1)) :
    ∃ base : (∀ i, List (FactorLetter (binary i))), ∃ a : Fin (n + 1),
      ∀ F : (i : Fin d) → Finset (List (FactorLetter (binary i))),
        (∀ i, ∀ x ∈ F i, base i <+: x) →
        ∀ m : ℕ, ∃ l : ℕ, m ≤ l ∧
          ∃ X : (i : Fin d) → Set (List (FactorLetter (binary i))),
            (∀ i, ∀ x ∈ X i, x.length = l) ∧
            (∀ i, ∀ x ∈ F i, ∃ y ∈ X i, x <+: y) ∧
            ∀ x : (∀ i, List (FactorLetter (binary i))),
              (∀ i, x i ∈ X i) → colour x = a :=
  wordFiniteDemandDenseMatrices d hd (fun i => FactorLetter (binary i)) n colour

theorem place_injective (b : Bool) (root : List (Fin 3)) :
    Function.Injective (place b root) := by
  intro s t h
  have hst : s <+: t := (place_prefix_iff b root s t).mp (by rw [h])
  have hts : t <+: s := (place_prefix_iff b root t s).mp (by rw [h])
  exact hst.eq_of_length_le hts.length_le

/-- The manuscript's dense-matrix HL input, now stated entirely with
original ternary words. `Set.range (place true w)` is exactly `B(w)`;
`Set.range (place false w)` is exactly `T(w)`, as the range lemmas above
prove. Roots share their original word length, so every output matrix is
supported on one common original level. -/
theorem rayConeDenseMatrices
    (d : ℕ) (hd : 0 < d) (binary : Fin d → Bool)
    (root : Fin d → List (Fin 3)) (r : ℕ) (hroot : ∀ i, (root i).length = r)
    (n : ℕ) (colour : (Fin d → List (Fin 3)) → Fin (n + 1)) :
    ∃ base : Fin d → List (Fin 3),
      (∀ i, base i ∈ Set.range (place (binary i) (root i))) ∧
      ∃ a : Fin (n + 1), ∀ F : Fin d → Finset (List (Fin 3)),
        (∀ i, ∀ x ∈ F i,
          x ∈ Set.range (place (binary i) (root i)) ∧ base i <+: x) →
        ∀ m : ℕ, ∃ l : ℕ, m ≤ l ∧
          ∃ X : Fin d → Set (List (Fin 3)),
            (∀ i, ∀ x ∈ X i,
              x ∈ Set.range (place (binary i) (root i)) ∧ x.length = l) ∧
            (∀ i, ∀ x ∈ F i, ∃ y ∈ X i, x <+: y) ∧
            ∀ x : Fin d → List (Fin 3), (∀ i, x i ∈ X i) → colour x = a := by
  classical
  let decode (i : Fin d) : List (Fin 3) → List (FactorLetter (binary i)) :=
    Function.invFun (place (binary i) (root i))
  have hdecode (i : Fin d) (s : List (FactorLetter (binary i))) :
      decode i (place (binary i) (root i) s) = s :=
    Function.leftInverse_invFun (place_injective (binary i) (root i)) s
  have hencode (i : Fin d) (x : List (Fin 3))
      (hx : x ∈ Set.range (place (binary i) (root i))) :
      place (binary i) (root i) (decode i x) = x := by
    obtain ⟨s, rfl⟩ := hx
    rw [hdecode]
  let colour' : (∀ i, List (FactorLetter (binary i))) → Fin (n + 1) :=
    fun x => colour (fun i => place (binary i) (root i) (x i))
  obtain ⟨base, a, hall⟩ := binaryTernaryFiniteDemandDenseMatrices d hd binary n colour'
  refine ⟨(fun i => place (binary i) (root i) (base i)),
    (fun i => Set.mem_range_self _), a, ?_⟩
  intro F hF m
  let F' : (i : Fin d) → Finset (List (FactorLetter (binary i))) :=
    fun i => (F i).image (decode i)
  have hF' : ∀ i, ∀ x ∈ F' i, base i <+: x := by
    intro i x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    apply (place_prefix_iff (binary i) (root i) _ _).mp
    rw [hencode i y (hF i y hy).1]
    exact (hF i y hy).2
  obtain ⟨l, hml, X, hLength, hDom, hMono⟩ := hall F' hF' m
  refine ⟨r + l, by omega,
    (fun i => place (binary i) (root i) '' X i), ?_, ?_, ?_⟩
  · intro i x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨Set.mem_range_self _, by rw [place_length, hroot, hLength i y hy]⟩
  · intro i x hx
    have hx' : decode i x ∈ F' i := Finset.mem_image.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hDom i (decode i x) hx'
    refine ⟨place (binary i) (root i) y, ⟨y, hy, rfl⟩, ?_⟩
    have h := (place_prefix_iff (binary i) (root i) _ _).mpr hxy
    rwa [hencode i x (hF i x hx).1] at h
  · intro x hx
    choose y hy heq using hx
    have h := hMono y hy
    change colour (fun i => place (binary i) (root i) (y i)) = a at h
    have heq' : (fun i => place (binary i) (root i) (y i)) = x := funext heq
    rwa [heq'] at h

/-- The ordinary strong-product HL input on actual full word trees, for
arbitrary finite index types and arbitrary positive finite colour sets. -/
theorem wordStrongProductHL
    (A : Type) [Finite A] [Nonempty A] [DecidableEq A]
    (I : Type) [Fintype I] (colors : ℕ) [NeZero colors]
    (colour : (I → List A) → Fin colors) :
    ∃ c : Fin colors, ∃ M : ℕ → ℕ,
      ∃ F : I → StrongSubtree (ambientTree A),
        StrictMono M ∧ (∀ i, (F i).levels = M) ∧
        ∀ k (x : I → List A),
          (∀ i, (⟨x i⟩ : Node A) ∈ (F i).sourceLevel k) → colour x = c := by
  obtain ⟨c, M, F, hM, hF, hMono⟩ := finiteIndexedProductHL
    (ambientTree A) I colors (fun _ => identityStrongSubtree (ambientTree A))
    id (fun _ => rfl) (fun x => colour (fun i => (x i).letters))
  exact ⟨c, M, F, hM, (fun i => (hF i).2),
    (fun k x hx => hMono k (fun i => ⟨x i⟩) hx)⟩

end AllThoseBigRamsey.Pseudotree.WordTrees
