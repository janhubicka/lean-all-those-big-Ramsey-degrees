import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-! Ternary levels and directed distance (Definition 3.1 in the manuscript).
The order on coding words will be separate from the prefix order. -/

namespace PosetDiariesFatTrees

abbrev Letter := Fin 3
abbrev LevelWord (n : Nat) := Fin n → Letter

def delta {n : Nat} (u v : LevelWord n) : Nat :=
  Finset.univ.sup (fun i : Fin n => (v i).val - (u i).val)

theorem coordinate_le_delta {n : Nat} (u v : LevelWord n) (i : Fin n) :
    (v i).val - (u i).val ≤ delta u v := by
  unfold delta
  exact Finset.le_sup (Finset.mem_univ i)

theorem delta_self {n : Nat} (u : LevelWord n) : delta u u = 0 := by
  apply Nat.le_antisymm
  · unfold delta
    apply Finset.sup_le_iff.mpr
    intro i _
    simp
  · exact Nat.zero_le _

theorem delta_le_two {n : Nat} (u v : LevelWord n) : delta u v ≤ 2 := by
  unfold delta
  apply Finset.sup_le_iff.mpr
  intro i _
  have hv := (v i).isLt
  omega

theorem delta_triangle {n : Nat} (u v w : LevelWord n) :
    delta u w ≤ delta u v + delta v w := by
  change Finset.univ.sup (fun i : Fin n => (w i).val - (u i).val) ≤
    delta u v + delta v w
  apply Finset.sup_le_iff.mpr
  intro i _
  have h₁ := coordinate_le_delta u v i
  have h₂ := coordinate_le_delta v w i
  omega

theorem delta_zero_iff {n : Nat} (u v : LevelWord n) :
    delta u v = 0 ↔ ∀ i, (v i).val ≤ (u i).val := by
  constructor
  · intro h i
    have hi := coordinate_le_delta u v i
    omega
  · intro h
    apply Nat.le_antisymm
    · unfold delta
      apply Finset.sup_le_iff.mpr
      intro i _
      have hi := h i
      omega
    · exact Nat.zero_le _

def Nonexpansive {X : Type*} (d : X → X → Nat) {B : Set X}
    (e : B → Letter) : Prop :=
  ∀ u v : B, (e v).val ≤ (e u).val + d u.val v.val

end PosetDiariesFatTrees
