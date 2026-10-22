import Std

/-!
# An obstruction when closure uses more than one input

Two one-dimensional subspaces of F_2^2 are closed under addition,
but their union is not. This is why the companion manuscript's
minimal-block free-amalgamation reduction assumes unary closure:
unions of closed structures are then closed automatically.

The vector-space example does not identify CF d-closure with
vector-space addition. It only refutes that unsupported closure axiom.
-/
namespace AllThoseBigRamsey.NonUnaryClosure

abbrev Vector := Bool × Bool

def add (x y : Vector) : Vector :=
  (Bool.xor x.1 y.1, Bool.xor x.2 y.2)

def AddClosed (S : Vector → Prop) : Prop :=
  ∀ x y, S x → S y → S (add x y)

def axisX (v : Vector) : Prop := v.2 = false
def axisY (v : Vector) : Prop := v.1 = false

theorem axisX_closed : AddClosed axisX := by
  intro x y hx hy
  change Bool.xor x.2 y.2 = false
  rw [hx,hy]
  rfl

theorem axisY_closed : AddClosed axisY := by
  intro x y hx hy
  change Bool.xor x.1 y.1 = false
  rw [hx,hy]
  rfl

theorem union_axes_not_closed :
    ¬ AddClosed (fun v => axisX v ∨ axisY v) := by
  intro h
  have hu : axisX (true,false) ∨ axisY (true,false) :=
    Or.inl rfl
  have hv : axisX (false,true) ∨ axisY (false,true) :=
    Or.inr rfl
  have hw := h (true,false) (false,true) hu hv
  simp [axisX,axisY,add] at hw

end AllThoseBigRamsey.NonUnaryClosure
