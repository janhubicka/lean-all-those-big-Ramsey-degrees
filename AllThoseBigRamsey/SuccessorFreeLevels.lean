import Std
import Std.Tactic.Omega

/-!
# The successor free-level marker and its one-level insertion

The successor draft uses a binary relation E whose incoming edges at j form
an initial segment with a gap: E(i,j) iff i < free(j), and free(j) < j
for j > 0. This is prefix-closed but not hereditary under arbitrary
subsets. Insertion of one vertex after a NONEMPTY prefix has a canonical
free-level action that preserves all old E-relations and the comparison
of one-types at every initial cut.

These are arithmetic/marking lemmas. They do not establish the TRAP of the
full L+E class for an arbitrary non-free relational L-class.
-/
namespace AllThoseBigRamsey.SuccessorFreeLevels

def Spaced (free : Nat → Nat) : Prop :=
  free 0 = 0 ∧ ∀ j, 0 < j → free j < j

def Marked (free : Nat → Nat) (i j : Nat) : Prop :=
  i < free j

/-- The function associated with E after inserting vertex m, using free
level k<m for the new vertex. All old vertices at or above m shift by one.
This formula is meaningful on the whole Nat enumeration. -/
def insert (m k : Nat) (free : Nat → Nat) (j : Nat) : Nat :=
  if j < m then free j
  else if j = m then k
  else if free (j-1) < m then free (j-1) else free (j-1)+1

def shift (m j : Nat) : Nat :=
  if j < m then j else j+1

def adjust (m j : Nat) : Nat := shift m j

theorem adjust_strict (m : Nat) {a b : Nat} (h : a < b) :
    adjust m a < adjust m b := by
  simp only [adjust, shift]
  split_ifs <;> omega

theorem adjust_le_iff (m a b : Nat) :
    adjust m a ≤ adjust m b ↔ a ≤ b := by
  constructor
  · intro h
    by_contra hc
    have := adjust_strict m (show b<a by omega)
    omega
  · intro h
    by_cases hab : a=b
    · subst b; omega
    · exact Nat.le_of_lt (adjust_strict m (by omega))

theorem adjust_min (m a b : Nat) :
    adjust m (min a b) = min (adjust m a) (adjust m b) := by
  unfold adjust shift
  split_ifs <;> omega

theorem insert_on_shift (m k : Nat) (free : Nat → Nat) (j : Nat)
    (hj : m ≤ j) :
    insert m k free (shift m j) = adjust m (free j) := by
  unfold insert shift adjust
  simp only [if_neg (by omega : ¬ j < m)]
  have h₁ : ¬ j+1 < m := by omega
  have h₂ : j+1 ≠ m := by omega
  simp [h₁, h₂]
  by_cases ht : free j < m
  · simp [shift, ht]
  · simp [shift, ht]

theorem insert_spaced {free : Nat → Nat} (hf : Spaced free)
    {m k : Nat} (hm : 0 < m) (hk : k < m) :
    Spaced (insert m k free) := by
  constructor
  · simp [insert, hm, hf.1]
  · intro j hj
    unfold insert
    split_ifs with h₁ h₂ h₃
    · exact hf.2 j hj
    · omega
    · have hfj : free (j-1) < j-1 := hf.2 (j-1) (by omega)
      omega
    · have hfj : free (j-1) < j-1 := hf.2 (j-1) (by omega)
      omega

theorem old_mark_preserved {free : Nat → Nat}
    (hf : Spaced free) {m k : Nat} (hm : 0 < m)
    (i j : Nat) :
    Marked free i j ↔
    Marked (insert m k free) (shift m i) (shift m j) := by
  simp only [Marked]
  by_cases hj : j < m
  · have hfree : free j < m := by
      by_cases hz : j = 0
      · subst j; simp [hf.1]
      · have h := hf.2 j (by omega)
        omega
    unfold shift insert
    simp only [if_pos hj]
    by_cases hi : i < m
    · simp [hi]
    · simp [hi]
      omega
  · have hfix := insert_on_shift m k free j (by omega)
    rw [hfix]
    simp only [shift, adjust]
    split_ifs <;> omega

theorem cut_profile_preserved {free : Nat → Nat}
    (m k : Nat) {j ell : Nat} (hm : 0 < m)
    (hje : m ≤ ell) (hell : ell ≤ j) :
    min (insert m k free (shift m j)) (shift m ell) =
      adjust m (min (free j) ell) := by
  rw [insert_on_shift m k free j (by omega), adjust_min]
  rfl

theorem cut_profile_before_insert {free : Nat → Nat}
    (m k : Nat) {j ell : Nat} (hell : ell < m) (hj : m ≤ j) :
    min (insert m k free (shift m j)) ell = min (free j) ell := by
  rw [insert_on_shift m k free j hj]
  simp only [adjust, shift]
  split_ifs <;> omega

/-- Literal spacing fails to survive deletion of a noninitial middle
vertex: E(0,2) is permitted, but on {0,2} it becomes E(0,1). -/
def exampleFree (j : Nat) : Nat := if j = 2 then 1 else 0

theorem example_spaced : Spaced exampleFree := by
  constructor
  · decide
  · intro j hj
    unfold exampleFree
    split_ifs <;> omega

theorem example_edge : Marked exampleFree 0 2 := by
  simp [Marked, exampleFree]

theorem example_relabel_not_spaced :
    ¬ Spaced (fun j => if j=1 then exampleFree 2 else 0) := by
  intro h
  have h1 := h.2 1 (by omega)
  simp [exampleFree] at h1

/-- Prefix restrictions are valid: only noninitial deletions are problematic. -/
theorem prefix_spaced {free : Nat → Nat} (h : Spaced free) (n : Nat) :
    (free 0 = 0 ∧ ∀ j, 0 < j → j < n → free j < j) := by
  exact ⟨h.1, fun j hj _ => h.2 j hj⟩

end AllThoseBigRamsey.SuccessorFreeLevels
