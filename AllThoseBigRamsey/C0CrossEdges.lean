import Std

/-!
# Cross-edge budget for strong sparse-graph substructures

For a finite simple graph with vertex sets A,B disjoint,
δ(A ∪ B)=δ(A)+δ(B)-e(A,B), where δ(X)=2|X|-|E(X)|.
If both A and B are strong in the ambient graph,
δ(A∪B) is at least each of δ(A), δ(B).
Therefore the number of cross edges is bounded by
the smaller of the two predimensions.

This file proves the numerical core. The actual
finite-graph inclusion-exclusion and strongness lemmas
are in the Big Hrushovski library, not re-axiomatized here.
-/
namespace AllThoseBigRamsey.C0CrossEdges

/-- The C0 predimension of a finite simple graph, from its counts. -/
def delta (vertices edges : Nat) : Int :=
  2 * (vertices : Int) - (edges : Int)

/-- Exact inclusion-exclusion across disjoint vertex sets. -/
theorem delta_disjoint_union
    (verticesA verticesB edgesA edgesB cross : Nat) :
    delta (verticesA + verticesB) (edgesA + edgesB + cross) =
      delta verticesA edgesA + delta verticesB edgesB - (cross : Int) := by
  unfold delta
  omega

/-- If A and B are strong in a disjoint union, the number of crossing
edges is at most the predimension of either side. -/
theorem cross_bound
    (verticesA verticesB edgesA edgesB cross : Nat)
    (hA : delta verticesA edgesA ≤
      delta (verticesA+verticesB) (edgesA+edgesB+cross))
    (hB : delta verticesB edgesB ≤
      delta (verticesA+verticesB) (edgesA+edgesB+cross)) :
    (cross : Int) ≤ delta verticesA edgesA ∧
      (cross : Int) ≤ delta verticesB edgesB := by
  have h := delta_disjoint_union verticesA verticesB edgesA edgesB cross
  constructor <;> omega

/-- A predimension-zero strong block cannot have a crossing edge
to any disjoint strong substructure. -/
theorem zero_block_no_cross_edges
    (verticesA verticesB edgesA edgesB cross : Nat)
    (hzero : delta verticesA edgesA = 0)
    (hB : delta verticesB edgesB ≤
      delta (verticesA+verticesB) (edgesA+edgesB+cross)) :
    cross = 0 := by
  have h := delta_disjoint_union verticesA verticesB edgesA edgesB cross
  have hn : 0 ≤ (cross : Int) := Int.natCast_nonneg _
  omega

/-- Each vertex of a simple graph has predimension 2, and a
minimal root strong extension has predimension ≤2 by choosing
a predimension-minimal finite set containing one vertex.
This simple arithmetic bound is separated from the finite-subset
minimality argument in the manuscript. -/
theorem singleton_delta_two : delta 1 0 = 2 := by
  decide

end AllThoseBigRamsey.C0CrossEdges
