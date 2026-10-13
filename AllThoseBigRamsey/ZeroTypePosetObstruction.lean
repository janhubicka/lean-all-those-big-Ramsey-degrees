import Std

/-!
# The finite obstruction to prefix TRAP for successor-marked posets

This module proves the exact obstruction in the manuscript's full
TRAP-square counterexample. The exhaustive Python audit verifies the
given insertion maps on all small marked posets and syntactic 1-types.
Constructing class-type-respecting maps in Lean for all continuations
remains outside the scope of these lemmas.
-/
namespace AllThoseBigRamsey.ZeroTypePosetObstruction

def IsPartialPoset {n : Nat}
    (R E : Fin n → Fin n → Prop) : Prop :=
  (∀ i, ¬ R i i) ∧
  (∀ i j k, R i j → R j k → R i k) ∧
  (∀ i j, R i j → (if i < j then E i j else E j i)) ∧
  (∀ i j, E i j → i.val+1 < j.val) ∧
  (∀ i j k, i < j → E j k → E i k)

def BasePrimeR (i j : Fin 3) : Prop := i.val = 2 ∧ j.val = 0
def BasePrimeE (i j : Fin 3) : Prop := i.val = 0 ∧ j.val = 2

def ContinuationR (i j : Fin 3) : Prop := i.val = 0 ∧ j.val = 2
def ContinuationE (i j : Fin 3) : Prop := i.val = 0 ∧ j.val = 2

instance : Decidable (IsPartialPoset BasePrimeR BasePrimeE) := by
  unfold IsPartialPoset BasePrimeR BasePrimeE
  infer_instance

instance : Decidable (IsPartialPoset ContinuationR ContinuationE) := by
  unfold IsPartialPoset ContinuationR ContinuationE
  infer_instance

theorem basePrime_valid : IsPartialPoset BasePrimeR BasePrimeE := by decide
theorem continuation_valid : IsPartialPoset ContinuationR ContinuationE := by decide

/-- The finite consequence does not rely on where the old future
vertex is placed. A filler between z and x cannot repair the conflict. -/
theorem no_amalgam_of_poset_and_E
    (R E : Nat → Nat → Prop)
    (x : Nat) (hx : 2 < x)
    (trans : ∀ i j k, R i j → R j k → R i k)
    (support : ∀ i j, i < j → R i j → E i j)
    (down : ∀ i j k, i < j → E j k → E i k)
    (hza : R 2 0) (hax : R 0 x) (hbx : ¬ E 1 x) : False := by
  have hzx := trans 2 0 x hza hax
  exact hbx (down 1 2 x (by omega) (support 2 x hx hzx))

end AllThoseBigRamsey.ZeroTypePosetObstruction
