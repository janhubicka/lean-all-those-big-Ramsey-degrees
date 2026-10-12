# All those big Ramsey degrees — Lean

Companion to `janhubicka/All-those-big-Ramsey-degrees`, which is authoritative
for mathematical scope. Lean/Std only. Run `lake build`, then
`lake env lean Checks.lean`.

## Interface index

| Module | Main interfaces |
| --- | --- |
| `Relational` | structures, induced embeddings, separate enumerations, ordinary embedding big Ramsey degrees |
| `FullTypes` | full atomic diagrams, evaluation, coordinate and base restriction |
| `TypeRespecting` | `Prefix`, `TailTuple`, `NTypeRespecting`, `MaximumArity`, `TypeRespecting`; identity/composition/monotonicity |
| `MetricInterpolation` | natural-number scalar clipping and `interpolation` |
| `GroupLabelTypes` | compatible profiles, anchor determination, restriction injectivity and covered types |
| `TwoColourTriangles` | exact small-amalgamation classification of two-colour palettes |
| `TriangleRepair` | `RepairSystem`, `step_anchor`, `uniform_choice` on arbitrary type sets and finite bases |
| `ThreeColourCertificates` | symmetric repair, obstruction, relabelling and exhaustive classification certificates |
| `DirectedTriangleRepair` | oriented triangle convention; `LocalLaws`, `AnchoredLaws`, `Problem.step_preserves_at`, `Problem.uniform_choice` |
| `DirectedTriangleCertificates` | all 128 oriented palettes; 16 small-AP classes; 15 local repairs; anchored repair for palette 37; `no_empty_rule`; `poset_triangle_iff` |

Full types include internal relations, unary/diagonal information and repeated
entries. The naming of parameters and future vertices is injective in the
`Prefix`/`TailTuple` application. Big Ramsey degrees count all embeddings.
Enumerations are not relation symbols; every tuple size at most n is tested.
The maximum-arity convention is sharp, with value one for the empty language.

## Directed and anchored repair

`T a b c` means labels 01=a, 12=b, 02=c. Pair reversal is an involution, not
an assumption of symmetry. In `DirectedTriangleRepair.Problem`, the initial
rule fits one fixed root anchor. The output rule processes an arbitrary finite
list of additional anchors, preserves the root, every previously fixed anchor,
all possible future-pair relations (including repeated types), and all prescribed
image values. This is not a bounded-base search.

The directed certificates use labels 0=forward, 1=backward, 2=absent. Their seven
triangle orbits are transitive tournament, cyclic tournament, directed path,
in-star, out-star, single arc, empty. Small strong amalgamation is tested on
actual one-point spans over bases of size at most three. The manuscript proves
that this finite test is sufficient for triangle classes. The 16 surviving
palettes are 33,35,37,63,89,90,91,92,95,97,99,121,124,125,126,127.

Fifteen have local repair tables. The remaining palette 37 has an anchored table
for each of its 18 admissible labelled base triangles. `no_empty_rule` excludes
empty-source amalgamation requests there. Palette 121 is checked to encode
exactly transitivity of the strict relation on a three-vertex structure.

All finite certificates use ordinary kernel `decide`, not `native_decide`.
The search generator is not part of the trusted proof. Full relational type maps,
class-level uniform continuation/TRAP, and the finite-quotient interpretation of
the symmetric exception remain written manuscript arguments. In particular, the
certificate theorem alone is not an end-to-end Lean proof of a class-level result.

## Validation and remaining work

Foundations passed at b44a67b98744, metric scalar interpolation at 36c600fa1ced,
group/two-colour interfaces at 424ea0ad09e6. Symmetric arbitrary-base repair and
its certificates passed at 04b7a27d8003, Actions run 38299496216. The directed
modules are submitted for CI; their status will be recorded after the actual run.
`Checks.lean` reports dependencies. No custom axiom or proof placeholder is used.

Next formalize the exact full-type-map and class-relative continuation interfaces
and connect the checked constraint constructions to them. Exact splits, the
maximum-arity reduction and concrete metric endpoint geometry remain to be
formalized. The general cycles-and-cliques theorem, beyond the stated small-pair
triangle cases, is not assumed.

The lattice-valued interpolation development is on a separate branch; this change
does not overwrite it. Internal weak-type comparison material stays out of the
public Lean repository. No independently spawned referee report is claimed.
