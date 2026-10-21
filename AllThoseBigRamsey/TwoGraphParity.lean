import Std

/-!
# Boolean four-point parity: the rooted two-graph repair core

Each two-graph is represented, after choosing a root, by an arbitrary graph.
The parity of three graph edges is its ternary relation. Four-point parity
then holds identically, and the newly inserted ternary relation is uniquely
determined by its three rooted edge bits.

This verifies the Boolean repair identities, not the class-level full-TRAP
quantifier structure or the synthetic invalid-type completion.
-/
namespace AllThoseBigRamsey.TwoGraphParity

/-- Three-edge parity, corresponding to a symmetric irreflexive triple. -/
def triangle (ab ac bc : Bool) : Bool :=
  Bool.xor (Bool.xor ab ac) bc

def xor4 (a b c d : Bool) : Bool :=
  Bool.xor (Bool.xor (Bool.xor a b) c) d

/-- The four triples of an undirected graph on four vertices have even parity. -/
theorem four_point_even (ab ac ad bc bd cd : Bool) :
    xor4 (triangle ab ac bc)
      (triangle ab ad bd)
      (triangle ac ad cd)
      (triangle bc bd cd) = false := by
  cases ab <;> cases ac <;> cases ad <;>
    cases bc <;> cases bd <;> cases cd <;> decide

/-- Three rooted graph-edge bits force the fourth ternary relation. -/
theorem forced_fourth (a b c d : Bool) :
    xor4 a b c d = false ↔ d = triangle a b c := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Any freely assigned new rooted bits produce a legal four-point condition. -/
theorem rooted_insert (old_xy new_x new_y : Bool) :
    xor4 old_xy new_x new_y
      (triangle old_xy new_x new_y) = false := by
  cases old_xy <;> cases new_x <;> cases new_y <;> decide

/-- Uniqueness of the inserted mixed triple, for each pair of future vertices. -/
theorem unique_mixed (old_xy new_x new_y t u : Bool)
    (ht : xor4 old_xy new_x new_y t = false)
    (hu : xor4 old_xy new_x new_y u = false) : t = u := by
  have ht' := (forced_fourth old_xy new_x new_y t).mp ht
  have hu' := (forced_fourth old_xy new_x new_y u).mp hu
  exact ht'.trans hu'.symm

/-- Adding the new root graph edge to an old base point forces
the relation with a future vertex and that base point. -/
theorem rooted_base_atom (base_new base_old future_new candidate : Bool)
    (h : xor4 base_new base_old future_new candidate = false) :
    candidate = triangle base_new base_old future_new :=
  (forced_fourth base_new base_old future_new candidate).mp h

end AllThoseBigRamsey.TwoGraphParity
