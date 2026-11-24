import AllThoseBigRamsey.Pseudotree.RayGrafting
import PseudotreeValidation.WordTrees

/-! Shared literal-word interface for the mixed ray-preserving argument. -/

namespace AllThoseBigRamsey.Pseudotree.Mixed

open RayEmbeddings

abbrev Tuple (m : ℕ) := Fin (m + 1) → Word

/-- The first `m` factors are binary, and the last factor is ternary. -/
def AdmissibleAt (m n : ℕ) (x : Tuple m) : Prop :=
  (∀ i, (x i).length = n) ∧ ∀ i, i ≠ Fin.last m → Binary (x i)

/-- All factors use total ray-preserving maps. On the binary factors only
binary source words are relevant; total extension on the other branches
lets composition and fusion use one uniform type. -/
structure Embedding (m : ℕ) where
  maps : Fin (m + 1) → RayStrongMap
  level : ℕ → ℕ
  synchronized : ∀ i, (maps i).level = level
  binary_roots : ∀ i, i ≠ Fin.last m → Binary ((maps i).map [])

namespace Embedding

variable {m : ℕ}

def applyTuple (F : Embedding m) (x : Tuple m) : Tuple m := fun i => (F.maps i).map (x i)

theorem level_strict (F : Embedding m) : StrictMono F.level := by
  intro i j hij
  have h := (F.maps (Fin.last m)).level_strict hij
  simpa only [F.synchronized] using h

theorem length_map (F : Embedding m) (i : Fin (m + 1)) (s : Word) :
    ((F.maps i).map s).length = F.level s.length := by
  rw [(F.maps i).length_map, F.synchronized]

theorem map_binary (F : Embedding m) (i : Fin (m + 1)) (hi : i ≠ Fin.last m)
    (s : Word) (hs : Binary s) : Binary ((F.maps i).map s) := by
  obtain ⟨p, hp, hbin⟩ := (F.maps i).map_append [] s
  have heq : (F.maps i).map s = (F.maps i).map [] ++ p := by simpa using hp
  rw [heq]
  exact (binary_append _ _).mpr ⟨F.binary_roots i hi, hbin hs⟩

theorem admissible_image (F : Embedding m) {n : ℕ} {x : Tuple m}
    (hx : AdmissibleAt m n x) : AdmissibleAt m (F.level n) (F.applyTuple x) := by
  constructor
  · intro i
    simp only [applyTuple, F.length_map, hx.1 i]
  · intro i hi
    exact F.map_binary i hi (x i) (hx.2 i hi)

def identity (m : ℕ) : Embedding m where
  maps _ := RayStrongMap.identity
  level := id
  synchronized _ := rfl
  binary_roots _ _ := binary_nil

def comp (F G : Embedding m) : Embedding m where
  maps i := (F.maps i).comp (G.maps i)
  level := F.level ∘ G.level
  synchronized i := by simp only [RayStrongMap.comp, F.synchronized, G.synchronized]
  binary_roots i hi := F.map_binary i hi _ (G.binary_roots i hi)

@[simp] theorem comp_applyTuple (F G : Embedding m) (x : Tuple m) :
    (F.comp G).applyTuple x = F.applyTuple (G.applyTuple x) := rfl

theorem map_take (F : Embedding m) (i : Fin (m + 1)) (s : Word) (n : ℕ)
    (hn : n ≤ s.length) :
    (F.maps i).map (s.take n) = ((F.maps i).map s).take (F.level n) := by
  obtain ⟨p, hp, _⟩ := (F.maps i).map_append (s.take n) (s.drop n)
  rw [List.take_append_drop] at hp
  have hlen : ((F.maps i).map (s.take n)).length = F.level n := by
    rw [F.length_map, List.length_take, Nat.min_eq_left hn]
  rw [hp, ← hlen, List.take_append_length]

end Embedding

theorem binary_take (s : Word) (hs : Binary s) (n : ℕ) : Binary (s.take n) := by
  have h : Binary (s.take n ++ s.drop n) := by simpa using hs
  exact (binary_append _ _).mp h |>.1

theorem admissible_take {m k n : ℕ} {x : Tuple m}
    (hx : AdmissibleAt m k x) (hn : n ≤ k) :
    AdmissibleAt m n (fun i => (x i).take n) := by
  constructor
  · intro i
    simp only [List.length_take, hx.1 i, Nat.min_eq_left hn]
  · intro i hi
    exact binary_take _ (hx.2 i hi) n

def induced {m : ℕ} {κ : Type} (colour : Tuple m → κ) (F : Embedding m) : Tuple m → κ :=
  fun x => colour (F.applyTuple x)

/-- Stability at source level `j`, along every binary continuation in the
ternary factor. All other factors are truncated to that same source level. -/
def StableAt {m : ℕ} {κ : Type} (colour : Tuple m → κ) (j : ℕ) : Prop :=
  ∀ n, j ≤ n → ∀ x : Tuple m, AdmissibleAt m n x →
    Binary ((x (Fin.last m)).drop j) →
    colour x = colour (fun i => (x i).take j)

def RayStable {m : ℕ} {κ : Type} (colour : Tuple m → κ) : Prop :=
  ∀ j, StableAt colour j

def Monochromatic {m : ℕ} {κ : Type} (colour : Tuple m → κ)
    (F : Embedding m) (c : κ) : Prop :=
  ∀ n, ∀ x : Tuple m, AdmissibleAt m n x → induced colour F x = c

end AllThoseBigRamsey.Pseudotree.Mixed
