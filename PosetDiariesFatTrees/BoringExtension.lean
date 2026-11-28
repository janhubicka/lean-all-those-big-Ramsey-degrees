import PosetDiariesFatTrees.WordDistance
import Mathlib.Data.Nat.Find

/-! The clipped directed-distance extension formula. The statement does not
require compatibility of the prescribed domain. The empty-domain extension
chosen here is constantly 2 (also non-expansive); the manuscript chooses 1. -/

namespace PosetDiariesFatTrees

private def Candidate {X : Type*} (d : X → X → Nat) {B : Set X}
    (e : B → Letter) (v : X) (k : Nat) : Prop :=
  k = 2 ∨ ∃ u : B, k = (e u).val + d u.val v

private theorem candidate_exists {X : Type*} (d : X → X → Nat) {B : Set X}
    (e : B → Letter) (v : X) : ∃ k, Candidate d e v k :=
  ⟨2, Or.inl rfl⟩

noncomputable def extensionNat {X : Type*} (d : X → X → Nat) {B : Set X}
    (e : B → Letter) (v : X) : Nat := by
  classical
  exact Nat.find (candidate_exists d e v)

private theorem extensionNat_spec {X : Type*} (d : X → X → Nat)
    {B : Set X} (e : B → Letter) (v : X) :
    Candidate d e v (extensionNat d e v) := by
  classical
  unfold extensionNat
  exact Nat.find_spec (candidate_exists d e v)

private theorem extensionNat_le {X : Type*} (d : X → X → Nat)
    {B : Set X} (e : B → Letter) (v : X) {k : Nat}
    (hk : Candidate d e v k) : extensionNat d e v ≤ k := by
  classical
  unfold extensionNat
  exact Nat.find_min' (candidate_exists d e v) hk

theorem extensionNat_bound {X : Type*} (d : X → X → Nat)
    {B : Set X} (e : B → Letter) (v : X) : extensionNat d e v ≤ 2 :=
  extensionNat_le d e v (Or.inl rfl)

theorem extensionNat_agrees {X : Type*} (d : X → X → Nat)
    {B : Set X} (e : B → Letter) (hdiag : ∀ x, d x x = 0)
    (he : Nonexpansive d e) (v : B) : extensionNat d e v.val = (e v).val := by
  apply Nat.le_antisymm
  · have h := extensionNat_le d e v.val
      (k := (e v).val + d v.val v.val) (Or.inr ⟨v, rfl⟩)
    simpa [hdiag] using h
  · rcases extensionNat_spec d e v.val with h | ⟨u, h⟩
    · have hv := (e v).isLt
      omega
    · rw [h]
      exact he u v

theorem extensionNat_nonexpansive {X : Type*} (d : X → X → Nat)
    {B : Set X} (e : B → Letter)
    (htri : ∀ u v w, d u w ≤ d u v + d v w) (w v : X) :
    extensionNat d e v ≤ extensionNat d e w + d w v := by
  rcases extensionNat_spec d e w with h | ⟨u, h⟩
  · have hv := extensionNat_bound d e v
    omega
  · have hv := extensionNat_le d e v
      (k := (e u).val + d u.val v) (Or.inr ⟨u, rfl⟩)
    have ht := htri u.val w v
    omega

noncomputable def extend {X : Type*} (d : X → X → Nat)
    {B : Set X} (e : B → Letter) (v : X) : Letter :=
  ⟨extensionNat d e v, Nat.lt_succ_of_le (extensionNat_bound d e v)⟩

theorem exists_nonexpansive_extension {n : Nat} (B : Set (LevelWord n))
    (e : B → Letter) (he : Nonexpansive delta e) :
    ∃ f : LevelWord n → Letter,
      (∀ v : B, f v.val = e v) ∧
      (∀ u v, (f v).val ≤ (f u).val + delta u v) := by
  refine ⟨extend delta e, ?_, ?_⟩
  · intro v
    apply Fin.ext
    exact extensionNat_agrees delta e delta_self he v
  · intro u v
    exact extensionNat_nonexpansive delta e delta_triangle u v

end PosetDiariesFatTrees
