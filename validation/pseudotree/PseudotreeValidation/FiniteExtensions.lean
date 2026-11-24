import PseudotreeValidation.Insertions
import PseudotreeValidation.Closure
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Set.Card

/-!
# Finite extension lemmas for binary meet-trees

This module develops the finite-diagram classification needed to turn the
four insertion lemmas into genuine structural embeddings.
-/

namespace AllThoseBigRamsey.Pseudotree

open FirstOrder
open scoped FirstOrder

variable {M : Type u} {N : Type v} [SemilatticeInf M] [SemilatticeInf N]

attribute [instance 100] semilatticeStructure

/-- Compatibility of the actual language structure with its order and meet.
This permits mathlib's induced substructure instances, rather than replacing
them by a second, merely propositionally equal structure. -/
class MeetsInterpreted (M : Type u) [SemilatticeInf M] [language.Structure M] : Prop where
  meet_eq (x : Fin 2 → M) : FirstOrder.Language.Structure.funMap (L := language) MeetFunction.meet x = x 0 ⊓ x 1
  order_iff (x : Fin 2 → M) : FirstOrder.Language.Structure.RelMap (L := language) OrderRelation.le x ↔ x 0 ≤ x 1

attribute [simp] MeetsInterpreted.meet_eq MeetsInterpreted.order_iff

instance canonicalMeetsInterpreted (M : Type u) [SemilatticeInf M] :
    @MeetsInterpreted M _ (semilatticeStructure M) where
  meet_eq _ := rfl
  order_iff _ := Iff.rfl

variable [language.Structure M] [language.Structure N]
    [MeetsInterpreted M] [MeetsInterpreted N]

theorem inf_mem (S : language.Substructure M) {x y : M} (hx : x ∈ S) (hy : y ∈ S) :
    x ⊓ y ∈ S := by
  let v : Fin 2 → M := fun i => if i = 0 then x else y
  have hv : ∀ i, v i ∈ S := by
    intro i
    by_cases hi : i = 0
    · simpa [v, hi] using hx
    · simpa [v, hi] using hy
  have h := S.fun_mem MeetFunction.meet v hv
  simpa [v] using h

def substructureOfInfClosed (A : Set M) (hA : ∀ x ∈ A, ∀ y ∈ A, x ⊓ y ∈ A) :
    language.Substructure M where
  carrier := A
  fun_mem := by
    intro n g x hx
    cases g
    simpa using hA (x 0) (hx 0) (x 1) (hx 1)

instance substructureSemilattice (S : language.Substructure M) : SemilatticeInf S where
  inf a b := ⟨(a : M) ⊓ b, inf_mem S a.property b.property⟩
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ := le_inf

@[simp] theorem coe_substructure_inf (S : language.Substructure M) (a b : S) :
    ((a ⊓ b : S) : M) = (a : M) ⊓ b := rfl

instance substructureMeetsInterpreted (S : language.Substructure M) : MeetsInterpreted S where
  meet_eq x := by
    apply Subtype.ext
    change FirstOrder.Language.Structure.funMap (L := language) MeetFunction.meet
      (fun i => ((x i : S) : M)) = ((x 0 ⊓ x 1 : S) : M)
    rw [MeetsInterpreted.meet_eq, coe_substructure_inf]
  order_iff x := by
    change FirstOrder.Language.Structure.RelMap (L := language) OrderRelation.le
      (fun i => ((x i : S) : M)) ↔ (x 0 : M) ≤ (x 1 : M)
    exact MeetsInterpreted.order_iff _

/-- Function-symbol preservation is exactly meet preservation in this language. -/
theorem embedding_map_inf (f : M ↪[language] N) (a b : M) :
    f (a ⊓ b) = f a ⊓ f b := by
  let v : Fin 2 → M := fun i => if i = 0 then a else b
  have h := f.map_fun MeetFunction.meet v
  simpa [v, Function.comp_def] using h

/-- The relation-symbol part gives the usual order-embedding interface. -/
def embeddingOrderEmbedding (f : M ↪[language] N) : M ↪o N where
  toEmbedding := f.toEmbedding
  map_rel_iff' := by
    intro a b
    let v : Fin 2 → M := fun i => if i = 0 then a else b
    have h := f.map_rel OrderRelation.le v
    change (f a ≤ f b) ↔ (a ≤ b)
    simpa [v, Function.comp_def] using h

@[simp] theorem embedding_le_iff (f : M ↪[language] N) (a b : M) :
    f a ≤ f b ↔ a ≤ b := by
  exact (embeddingOrderEmbedding f).le_iff_le

@[simp] theorem embedding_lt_iff (f : M ↪[language] N) (a b : M) :
    f a < f b ↔ a < b := by
  exact (embeddingOrderEmbedding f).lt_iff_lt

/-- Injective meet-preserving maps preserve and reflect the order automatically. -/
def embeddingOfInfMap (f : M → N) (hf : Function.Injective f)
    (hInf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) : M ↪[language] N where
  toFun := f
  inj' := hf
  map_fun' := by
    intro n g x
    cases g
    simpa [Function.comp_def] using hInf (x 0) (x 1)
  map_rel' := by
    intro n r x
    cases r
    simp only [MeetsInterpreted.order_iff, Function.comp_apply]
    change (f (x 0) ≤ f (x 1)) ↔ (x 0 ≤ x 1)
    constructor
    · intro h
      apply inf_eq_left.mp
      apply hf
      rw [hInf, inf_eq_left.mpr h]
    · intro h
      apply inf_eq_left.mp
      rw [← hInf, inf_eq_left.mpr h]

section OnePointMap

variable (S : language.Substructure M) (b : M) (hb : b ∉ S)
    (hcover : ∀ x : M, x = b ∨ x ∈ S) (f : S ↪[language] N) (v : N)

/-- Extend a map to the unique new point. -/
noncomputable def onePointFun (x : M) : N := by
  classical
  exact if h : x = b then v else f ⟨x, (hcover x).resolve_left h⟩

@[simp] theorem onePointFun_new : onePointFun S b hcover f v b = v := by
  simp [onePointFun]

include hb

@[simp] theorem onePointFun_old (a : S) : onePointFun S b hcover f v a = f a := by
  have hne : (a : M) ≠ b := fun h => hb (h ▸ a.property)
  simp only [onePointFun, hne, ↓reduceDIte]

/-- The mixed meet equations are the only equations needed to extend an
embedding across a single new point. -/
noncomputable def onePointEmbedding
    (hv : ∀ a : S, v ≠ f a)
    (hmixed : ∀ a : S, onePointFun S b hcover f v (b ⊓ a) = v ⊓ f a) :
    M ↪[language] N := by
  classical
  apply embeddingOfInfMap (onePointFun S b hcover f v)
  · intro x y hxy
    by_cases hxb : x = b
    · subst x
      by_cases hyb : y = b
      · exact hyb.symm
      · have hy : y ∈ S := (hcover y).resolve_left hyb
        have hbad : v = f ⟨y, hy⟩ := by
          simpa only [onePointFun_new,
            onePointFun_old S b hb hcover f v ⟨y, hy⟩] using hxy
        exact False.elim (hv ⟨y, hy⟩ hbad)
    · have hx : x ∈ S := (hcover x).resolve_left hxb
      by_cases hyb : y = b
      · subst y
        have hbad : f ⟨x, hx⟩ = v := by
          simpa only [onePointFun_new,
            onePointFun_old S b hb hcover f v ⟨x, hx⟩] using hxy
        exact False.elim (hv ⟨x, hx⟩ hbad.symm)
      · have hy : y ∈ S := (hcover y).resolve_left hyb
        have hsame : f ⟨x, hx⟩ = f ⟨y, hy⟩ := by
          simpa only [onePointFun_old S b hb hcover f v ⟨x, hx⟩,
            onePointFun_old S b hb hcover f v ⟨y, hy⟩] using hxy
        exact congrArg Subtype.val (f.injective hsame)
  · intro x y
    by_cases hxb : x = b
    · subst x
      by_cases hyb : y = b
      · subst y
        simp only [inf_idem, onePointFun_new]
      · have hy : y ∈ S := (hcover y).resolve_left hyb
        simpa only [onePointFun_new, onePointFun_old S b hb hcover f v ⟨y, hy⟩]
          using hmixed ⟨y, hy⟩
    · have hx : x ∈ S := (hcover x).resolve_left hxb
      by_cases hyb : y = b
      · subst y
        simpa only [inf_comm, onePointFun_new, onePointFun_old S b hb hcover f v ⟨x, hx⟩]
          using hmixed ⟨x, hx⟩
      · have hy : y ∈ S := (hcover y).resolve_left hyb
        have hinf : x ⊓ y ∈ S := inf_mem S hx hy
        have he := embedding_map_inf f ⟨x, hx⟩ ⟨y, hy⟩
        have hsub : (⟨x, hx⟩ : S) ⊓ ⟨y, hy⟩ = ⟨x ⊓ y, hinf⟩ := by
          apply Subtype.ext
          exact coe_substructure_inf S ⟨x, hx⟩ ⟨y, hy⟩
        rw [hsub] at he
        simpa only [onePointFun_old S b hb hcover f v ⟨x ⊓ y, hinf⟩,
          onePointFun_old S b hb hcover f v ⟨x, hx⟩,
          onePointFun_old S b hb hcover f v ⟨y, hy⟩]
          using he

@[simp] theorem onePointEmbedding_old
    (hv : ∀ a : S, v ≠ f a)
    (hmixed : ∀ a : S, onePointFun S b hcover f v (b ⊓ a) = v ⊓ f a)
    (a : S) : onePointEmbedding S b hb hcover f v hv hmixed a = f a :=
  onePointFun_old S b hb hcover f v a

end OnePointMap

/-- The at-most-two-cones condition, expressed without quotienting upper nodes. -/
def BinaryBranching (M : Type u) [SemilatticeInf M] : Prop :=
  ∀ s x y z : M, s < x → s < y → s < z →
    s < x ⊓ y ∨ s < x ⊓ z ∨ s < y ⊓ z

theorem RayTree.binaryBranching {α : Type u} [LinearOrder α] : BinaryBranching (RayTree α) := by
  intro s x y z hx hy hz
  rw [RayTree.lt_inf_iff_coneCode_eq hx hy, RayTree.lt_inf_iff_coneCode_eq hx hz,
    RayTree.lt_inf_iff_coneCode_eq hy hz]
  cases RayTree.coneCode s x <;> cases RayTree.coneCode s y <;>
    cases RayTree.coneCode s z <;> simp

section OnePointExistence

variable {α : Type v} [LinearOrder α] [NoMinOrder α] [NoMaxOrder α]
    [DenselyOrdered α] [Nonempty α]

/-- Every one-point extension of a finite binary meet-tree can be embedded
into the concrete dense binary tree, extending an existing embedding. -/
theorem extend_one_point [Finite M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbinary : BinaryBranching M)
    (S : language.Substructure M) (b : M) (hb : b ∉ S)
    (hcover : ∀ x : M, x = b ∨ x ∈ S)
    (f : S ↪[language] RayTree α) :
    ∃ g : M ↪[language] RayTree α, ∀ a : S, g a = f a := by
  classical
  let _ : Nonempty (RayTree α) := ⟨.point (Classical.choice ‹Nonempty α›)⟩
  let A : Set (RayTree α) := Set.range f
  have hAfin : A.Finite := Set.finite_range f
  have hmeetOld (a : S) (hnot : ¬b ≤ (a : M)) : b ⊓ (a : M) ∈ S := by
    apply (hcover _).resolve_left
    exact fun h => hnot (inf_eq_left.mp h)
  have finish (v : RayTree α) (hv : v ∉ A)
      (hmixed : ∀ a : S, onePointFun S b hcover f v (b ⊓ a) = v ⊓ f a) :
      ∃ g : M ↪[language] RayTree α, ∀ a : S, g a = f a := by
    have hfresh : ∀ a : S, v ≠ f a := fun a h => hv ⟨a, h.symm⟩
    exact ⟨onePointEmbedding S b hb hcover f v hfresh hmixed,
      onePointEmbedding_old S b hb hcover f v hfresh hmixed⟩
  let L : Set M := {a | a ∈ S ∧ a ≤ b}
  by_cases hL : L.Nonempty
  · obtain ⟨l, hl⟩ := (Set.toFinite L).exists_maximal hL
    have hlS : l ∈ S := hl.1.1
    have hlb : l ≤ b := hl.1.2
    have hlb' : l < b := lt_of_le_of_ne hlb (fun h => hb (h ▸ hlS))
    have hmax (a : M) (ha : a ∈ S) (hab : a ≤ b) : a ≤ l := by
      rcases htree hab hlb with h | h
      · exact h
      · exact hl.2 ⟨ha, hab⟩ h
    let ls : S := ⟨l, hlS⟩
    let U : Set M := {a | a ∈ S ∧ b ≤ a}
    by_cases hU : U.Nonempty
    · obtain ⟨m, hm⟩ := (Set.toFinite U).exists_minimal hU
      have hmS : m ∈ S := hm.1.1
      have hbm : b ≤ m := hm.1.2
      have hmin (a : M) (ha : a ∈ S) (hba : b ≤ a) : m ≤ a := by
        have hinf : m ⊓ a ∈ U := ⟨inf_mem S hmS ha, le_inf hbm hba⟩
        exact le_trans (hm.2 hinf inf_le_left) inf_le_right
      let ms : S := ⟨m, hmS⟩
      have hlm : f ls < f ms := by
        apply (embedding_lt_iff f ls ms).2
        change l < m
        exact lt_of_lt_of_le hlb' hbm
      have hma (a : S) (hnot : ¬b ≤ (a : M)) : m ⊓ (a : M) = b ⊓ a :=
        inf_above_eq_of_not_lt htree hbm (fun h => hnot h.le)
      have hprofile : ∀ y ∈ A, f ms ≤ y ∨ f ms ⊓ y ≤ f ls := by
        rintro y ⟨a, rfl⟩
        by_cases hba : b ≤ (a : M)
        · exact Or.inl ((embedding_le_iff f ms a).2 (hmin a a.property hba))
        · right
          rw [← embedding_map_inf f ms a]
          apply (embedding_le_iff f _ ls).2
          change ((ms ⊓ a : S) : M) ≤ l
          rw [coe_substructure_inf]
          exact (hma a hba).symm ▸ hmax _ (hmeetOld a hba) inf_le_left
      obtain ⟨v, hlv, hvm, hv, hvprofile⟩ := insertion_between A (f ls) (f ms) hlm hprofile
      apply finish v hv
      intro a
      by_cases hba : b ≤ (a : M)
      · rw [inf_eq_left.mpr hba, onePointFun_new]
        exact (inf_eq_left.mpr (le_trans hvm.le
          ((embedding_le_iff f ms a).2 (hmin a a.property hba)))).symm
      · have hca := hmeetOld a hba
        rw [onePointFun_old S b hb hcover f v ⟨b ⊓ a, hca⟩]
        rcases hvprofile (f a) ⟨a, rfl⟩ with ⟨hwrong, _⟩ | ⟨_, hvmeet⟩
        · exact False.elim (hba (le_trans hbm ((embedding_le_iff f ms a).1 hwrong)))
        · rw [hvmeet, ← embedding_map_inf f ms a]
          congr 1
          apply Subtype.ext
          exact (hma a hba).symm
    · have hnotupper (a : S) : ¬b ≤ (a : M) := fun h => hU ⟨a, a.property, h⟩
      have hmeets (a : S) : b ⊓ (a : M) = l ⊓ a := by
        apply le_antisymm
        · exact le_inf (hmax _ (hmeetOld a (hnotupper a)) inf_le_left) inf_le_right
        · exact inf_le_inf_right _ hlb
      have hex : ∃ v : RayTree α, v ∉ A ∧ ∀ a : S, v ⊓ f a = f ls ⊓ f a := by
        by_cases hR : ∃ r : S, l < (r : M)
        · obtain ⟨r, hlr⟩ := hR
          have hlrF : f ls < f r := (embedding_lt_iff f ls r).2 hlr
          have hused : ∀ y ∈ A, f ls < y → f ls < y ⊓ f r := by
            rintro y ⟨a, rfl⟩ hlaF
            have hla : l < (a : M) := (embedding_lt_iff f ls a).1 hlaF
            have hba : b ⊓ (a : M) = l := (hmeets a).trans (inf_eq_left.mpr hla.le)
            have hbr : b ⊓ (r : M) = l := (hmeets r).trans (inf_eq_left.mpr hlr.le)
            have har : l < (a : M) ⊓ r := by
              rcases hbinary l b a r hlb' hla hlr with h | h | h
              · exact False.elim ((lt_irrefl l) (hba ▸ h))
              · exact False.elim ((lt_irrefl l) (hbr ▸ h))
              · exact h
            rw [← embedding_map_inf f a r]
            apply (embedding_lt_iff f ls _).2
            change l < ((a ⊓ r : S) : M)
            simpa only [coe_substructure_inf] using har
          obtain ⟨v, _, _, hv, hvm⟩ := RayTree.insertion_unused_cone A (f ls) (f r) hlrF hused
          exact ⟨v, hv, fun a => hvm (f a) ⟨a, rfl⟩⟩
        · have hmaximal : ∀ y ∈ A, ¬f ls < y := by
            rintro y ⟨a, rfl⟩ h
            exact hR ⟨a, (embedding_lt_iff f ls a).1 h⟩
          obtain ⟨v, _, hv, hvm⟩ := insertion_above_maximal
            RayTree.le_or_ge_of_le_common A (f ls) hmaximal
          exact ⟨v, hv, fun a => hvm (f a) ⟨a, rfl⟩⟩
      obtain ⟨v, hv, hvm⟩ := hex
      apply finish v hv
      intro a
      have hca := hmeetOld a (hnotupper a)
      rw [onePointFun_old S b hb hcover f v ⟨b ⊓ a, hca⟩, hvm,
        ← embedding_map_inf f ls a]
      congr 1
      apply Subtype.ext
      exact hmeets a
  · have hbelow (a : S) : b ≤ (a : M) := by
      by_contra hnot
      exact hL ⟨b ⊓ a, hmeetOld a hnot, inf_le_left⟩
    obtain ⟨v, hv, hvm⟩ := insertion_below_finite hAfin
    apply finish v hv
    intro a
    rw [inf_eq_left.mpr (hbelow a), onePointFun_new]
    exact (hvm (f a) ⟨a, rfl⟩).2.symm

end OnePointExistence

/-- Regard a smaller old substructure inside a larger source substructure. -/
abbrev inside (S B : language.Substructure M) : language.Substructure B :=
  S.comap B.subtype.toHom

def insideEquiv (S B : language.Substructure M) (hSB : S ≤ B) :
    inside S B ≃[language] S where
  toFun a := ⟨a.val.val, a.property⟩
  invFun a := ⟨⟨a.val, hSB a.property⟩, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_fun' := by intro n g x; cases g; rfl
  map_rel' := by intro n r x; cases r; rfl

theorem predecessor_comparability_substructure
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (B : language.Substructure M) {x y z : B} (hx : x ≤ z) (hy : y ≤ z) :
    x ≤ y ∨ y ≤ x := htree hx hy

theorem binaryBranching_substructure (hbinary : BinaryBranching M)
    (B : language.Substructure M) : BinaryBranching B := by
  intro s x y z hx hy hz
  have h := hbinary (s : M) x y z hx hy hz
  change (s : M) < ((x ⊓ y : B) : M) ∨
    (s : M) < ((x ⊓ z : B) : M) ∨ (s : M) < ((y ⊓ z : B) : M)
  simpa only [coe_substructure_inf] using h

section FiniteExistence

variable {α : Type v} [LinearOrder α] [NoMinOrder α] [NoMaxOrder α]
    [DenselyOrdered α] [Nonempty α]

/-- Extend an embedding of any substructure of a finite binary meet-tree to
an embedding of the whole tree. The induction adds a minimal missing point;
its meet with any old point is old or is the new point itself. -/
theorem extend_finite [Finite M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbinary : BinaryBranching M)
    (S : language.Substructure M) (f : S ↪[language] RayTree α) :
    ∃ g : M ↪[language] RayTree α, ∀ a : S, g a = f a := by
  classical
  suffices H : ∀ n : ℕ, ∀ (S : language.Substructure M) (f : S ↪[language] RayTree α),
      ((S : Set M)ᶜ).ncard = n →
      ∃ g : M ↪[language] RayTree α, ∀ a : S, g a = f a from H _ S f rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S f hn
    by_cases hall : ∀ x : M, x ∈ S
    · have htop : S = ⊤ := by ext x; simp [hall x]
      subst S
      refine ⟨f.comp FirstOrder.Language.Substructure.topEquiv.symm.toEmbedding, ?_⟩
      intro a
      rfl
    · have hmissing : ((S : Set M)ᶜ).Nonempty := by
        push Not at hall
        exact hall
      obtain ⟨b, hbmin⟩ := (Set.toFinite ((S : Set M)ᶜ)).exists_minimal hmissing
      have hb : b ∉ S := hbmin.1
      have hinsert : ∀ x ∈ insert b (S : Set M), ∀ y ∈ insert b (S : Set M),
          x ⊓ y ∈ insert b (S : Set M) := by
        have hmix (a : M) (ha : a ∈ S) : b ⊓ a ∈ insert b (S : Set M) := by
          by_cases hc : b ⊓ a ∈ S
          · exact Set.mem_insert_of_mem _ hc
          · have hcb : b ⊓ a = b := le_antisymm inf_le_left (hbmin.2 hc inf_le_left)
            exact Set.mem_insert_iff.mpr (Or.inl hcb)
        rintro x (rfl | hx) y (rfl | hy)
        · exact Set.mem_insert_iff.mpr (Or.inl (inf_idem _))
        · exact hmix y hy
        · simpa only [inf_comm] using hmix x hx
        · exact Set.mem_insert_of_mem _ (inf_mem S hx hy)
      let B := substructureOfInfClosed (insert b (S : Set M)) hinsert
      have hSB : S ≤ B := fun _ hx => Set.mem_insert_of_mem _ hx
      let bs : B := ⟨b, Set.mem_insert _ _⟩
      have hbInside : bs ∉ inside S B := hb
      have hcover : ∀ x : B, x = bs ∨ x ∈ inside S B := by
        intro x
        rcases x.property with h | h
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr h
      let fInside := f.comp (insideEquiv S B hSB).toEmbedding
      obtain ⟨fB, hfB⟩ := extend_one_point
        (predecessor_comparability_substructure htree B)
        (binaryBranching_substructure hbinary B) (inside S B) bs hbInside hcover fInside
      have hfB_old (a : S) : fB ⟨a, hSB a.property⟩ = f a := by
        exact hfB ⟨⟨a, hSB a.property⟩, a.property⟩
      have hstrict : (B : Set M)ᶜ ⊂ (S : Set M)ᶜ := by
        constructor
        · intro x hx hxS
          exact hx (hSB hxS)
        · intro hreverse
          exact hreverse hb (Set.mem_insert _ _)
      have hlt : ((B : Set M)ᶜ).ncard < n := by
        rw [← hn]
        exact Set.ncard_lt_ncard hstrict
      obtain ⟨g, hg⟩ := ih _ hlt B fB rfl
      exact ⟨g, fun a => (hg ⟨a, hSB a.property⟩).trans (hfB_old a)⟩

/-- The same theorem in the ambient-substructure form used by mathlib's
back-and-forth interface. -/
theorem extend_finite_substructure
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbinary : BinaryBranching M)
    (S B : language.Substructure M) [Finite B] (hSB : S ≤ B)
    (f : S ↪[language] RayTree α) :
    ∃ g : B ↪[language] RayTree α, ∀ a : S, g ⟨a, hSB a.property⟩ = f a := by
  let fInside := f.comp (insideEquiv S B hSB).toEmbedding
  obtain ⟨g, hg⟩ := extend_finite (predecessor_comparability_substructure htree B)
    (binaryBranching_substructure hbinary B) (inside S B) fInside
  exact ⟨g, fun a => hg ⟨⟨a, hSB a.property⟩, a.property⟩⟩

/-- Every finite binary meet-tree embeds in the concrete model. -/
theorem finite_universal [Finite M]
    (htree : ∀ {x y z : M}, x ≤ z → y ≤ z → x ≤ y ∨ y ≤ x)
    (hbinary : BinaryBranching M) : Nonempty (M ↪[language] RayTree α) := by
  let E : language.Substructure M := substructureOfInfClosed ∅ (by simp)
  let f : E ↪[language] RayTree α := embeddingOfInfMap
    (fun x => False.elim x.property) (fun x => False.elim x.property)
    (fun x => False.elim x.property)
  obtain ⟨g, _⟩ := extend_finite htree hbinary E f
  exact ⟨g⟩

end FiniteExistence

/-- The actual concrete model is ultrahomogeneous, by mathlib back-and-forth. -/
theorem RayTree.isUltrahomogeneous {α : Type u} [LinearOrder α] [Countable α]
    [NoMinOrder α] [NoMaxOrder α] [DenselyOrdered α] [Nonempty α] :
    language.IsUltrahomogeneous (RayTree α) := by
  apply (FirstOrder.Language.isUltrahomogeneous_iff_IsExtensionPair
    FirstOrder.Language.Structure.cg_of_countable).2
  apply FirstOrder.Language.isExtensionPair_iff_exists_embedding_closure_singleton_sup.2
  intro S hS f m
  let B : language.Substructure (RayTree α) :=
    FirstOrder.Language.Substructure.closure language {m} ⊔ S
  have hBfg : B.FG := (FirstOrder.Language.Substructure.fg_closure_singleton m).sup hS
  obtain ⟨X, hX, hXB⟩ := FirstOrder.Language.Substructure.fg_def.mp hBfg
  have hBfinite := finite_meet_closure RayTree.le_or_ge_of_le_common hX
  rw [hXB] at hBfinite
  let _ : Finite B := hBfinite.to_subtype
  obtain ⟨g, hg⟩ := extend_finite_substructure RayTree.le_or_ge_of_le_common
    RayTree.binaryBranching S B le_sup_right f
  refine ⟨g, ?_⟩
  ext a
  exact (hg a).symm

end AllThoseBigRamsey.Pseudotree
