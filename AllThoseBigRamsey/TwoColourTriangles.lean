import Std

/-!
# Exact small-amalgamation check for two-colour triangle palettes

Bit i of a palette says that a triangle with i red edges is permitted. Red is
true and blue is false. SmallSAP tests actual one-point strong-amalgamation
requests over bases of size one and two, including two copies of the same type.

The finite classification is kernel reduction (`decide`), not `native_decide`.
The manuscript proves the passage to full strong amalgamation and TRAP by
identifying the seven classes. Those class-theoretic results are not asserted
as Lean theorems here.
-/
namespace AllThoseBigRamsey.TwoColourTriangles

def redCount (a b c : Bool) : Nat :=
  (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)

def Triangle (palette : Fin 16) (a b c : Bool) : Prop :=
  palette.val.testBit (redCount a b c) = true

def SmallSAP (palette : Fin 16) : Prop :=
  (∀ a b : Bool, ∃ c : Bool, Triangle palette a b c) ∧
  (∀ edge p₀ p₁ q₀ q₁ : Bool,
    Triangle palette edge p₀ p₁ → Triangle palette edge q₀ q₁ →
    ∃ c : Bool, Triangle palette p₀ q₀ c ∧ Triangle palette p₁ q₁ c)

def Listed (palette : Fin 16) : Prop :=
  palette.val = 5 ∨ palette.val = 7 ∨ palette.val = 10 ∨
  palette.val = 11 ∨ palette.val = 13 ∨ palette.val = 14 ∨ palette.val = 15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem classification : ∀ palette : Fin 16, SmallSAP palette ↔ Listed palette := by
  unfold SmallSAP Triangle Listed
  decide

/-- Allowing just one-red and two-red triangles fails even small strong AP. -/
theorem mixed_only_fails : ¬ SmallSAP ⟨6, by decide⟩ := by
  unfold SmallSAP Triangle
  decide

end AllThoseBigRamsey.TwoColourTriangles
