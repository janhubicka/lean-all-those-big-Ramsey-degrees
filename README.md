# All those big Ramsey degrees — Lean

Companion to `janhubicka/All-those-big-Ramsey-degrees`, which is authoritative
for mathematical scope. Lean/Std only; no mathlib dependency. Run `lake build`,
then `lake env lean Checks.lean`.

## Interface index

| Module | Main interfaces |
| --- | --- |
| `Relational` | relational structures, induced embeddings, separate enumerations, ordinary embedding big Ramsey degrees |
| `FullTypes` | `FullType`, `SameFullType`, evaluation and restriction of full atomic diagrams |
| `TypeRespecting` | `Prefix`, `TailTuple`, `NTypeRespecting`, `MaximumArity`, `TypeRespecting`; identity/composition/monotonicity |
| `MetricInterpolation` | `clip`, bounds, fixed values, positivity, Lipschitz and pair-sum bounds; scalar `interpolation` |
| `GroupLabelTypes` | compatible profiles, anchor determination, restriction injectivity and coverage |
| `TwoColourTriangles` | exact small-amalgamation classification of 16 two-colour palettes |
| `TriangleRepair` | three finite repair laws; `Problem.step_preserves_fits`; `Problem.extension` for an arbitrary finite list of anchors |
| `FiniteQuotient` | `covers_of_capacity`: the finite-rank saturation argument for covered types |
| `ThreeColourTriangles` | 106 explicit repair tables; `SmallSAP`; `certified_classification`; `repair_or_exception`; six exceptional colour renamings and the obstruction to a repair table |

Full types retain all internal/unary/diagonal information and repeated relation
entries. Big Ramsey degrees count all embeddings. Enumeration is separate from
the language. Types of every size at most n are tested, including short tails.
`MaximumArity` requires a sharp bound (or value one for the empty language).
For realised full types, the combined naming of parameters and future vertices
must be injective; the `Prefix`/`TailTuple` application has that property.

## Scope of the new triangle result

`TriangleRepair.Problem.extension` constructs one rule on the whole type domain
which works at every anchor in an arbitrary finite list, preserving all pair
constraints and prescribed image values. It is not a search bounded by base size.
The manuscript derives the explicit `Problem` hypotheses from an actual full-type
amalgamation request. This final class-level bridge is not yet formalized.

The three-colour certificate uses the ordered triangle list
000,001,002,011,012,022,111,112,122,222. For 106 palettes it checks a complete
27-entry repair table, including constraints on two distinct vertices with the
same old type. The remaining six palettes are renamings of mask 169 and use the
finite-equivalence-quotient proof instead. The small-amalgamation tests are
actual one-point spans on up to three base vertices; the manuscript proves the
reduction from arbitrary bases. Finite certificates use kernel `decide`, not
`native_decide`. The search generator is not trusted by the Lean proof.

`FiniteQuotient.covers_of_capacity` proves an abstract counting implication.
Its interpretation via maximal numbers of inequivalent realisations and ordinary
amalgamation remains a written manuscript proof, not a hidden premise named TRAP.

## Validation

Foundations passed at b44a67b98744 (run 38271277558); metric scalar interpolation
at 36c600fa1ced (run 38279289894); group profiles and two-colour certificates at
424ea0ad09e6 (run 38295072697), on Lean v4.35.0-rc3. The new three modules are
submitted for CI. Build status is distinct from correspondence of Lean statements
with the manuscript. `Checks.lean` reports proof dependencies. No proof placeholder
or custom axiom is intended; CI rejects unchecked declarations.

## Remaining work

Encode coherent full-type maps, uniform continuations and the class-level TRAP
property. Connect the checked repair and capacity lemmas to those interfaces.
Formalize the finite-quotient interpretation of the exceptional palette. Exact
split equivalence, maximum-arity reduction and concrete metric endpoint geometry
also remain to be formalized. The general cycles-and-cliques theorem, with more
colours, asymmetric/unary data or larger clique obstructions, is not assumed.

Internal weak-type comparison material remains absent from this public repository.
No independently spawned referee verification is claimed.
