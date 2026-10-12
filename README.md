# All those big Ramsey degrees — Lean

Companion to `janhubicka/All-those-big-Ramsey-degrees`, which is authoritative
for mathematical scope. Lean/Std only. Run `lake build`, then
`lake env lean Checks.lean` and `lake env lean ChecksFullTypes.lean`.

## Interface index

| Module | Main interfaces |
| --- | --- |
| `Relational` | structures, induced embeddings, separate enumerations, ordinary embedding big Ramsey degrees |
| `FullTypes` | full atomic diagrams, evaluation, coordinate and base restriction |
| `TypeRespecting` | `Prefix`, `TailTuple`, `NTypeRespecting`, `MaximumArity`, `TypeRespecting`; identity/composition/monotonicity |
| `BinaryFullTypes` | `FullType.futureDiagram`, `FullType.binary_ext`: reconstruct a binary full type from singletons AND its internal future diagram |
| `FullTypeMaps` | `FullTypeMap`, `id`, `comp`, `onType_injective`, `future_preserved`, `binary_determined_by_one` |
| `TypeAmalgamation` | `Continuation`, `FutureTuple`, `Approximates`, `TypeRespectingMap`, `ClassTypeRespectingMap`, `ExtendsByLast`, `NTypeRespectingAmalgamation`, `TypeRespectingAmalgamation` |
| `IrreducibleCover` | relational `Irreducible`, actual induced embeddings, `range_in_one_side`, `Avoids`, `avoids_of_free_cover`; no size bound on the forbidden structure |
| `MetricInterpolation` | natural-number scalar clipping and `interpolation` |
| `GroupLabelTypes` | compatible profiles, anchor determination, restriction injectivity and covered types |
| `TwoColourTriangles` | exact small-amalgamation classification of two-colour palettes |
| `TriangleRepair` | `RepairSystem`, `step_anchor`, `uniform_choice` on arbitrary type sets and finite bases |
| `ThreeColourCertificates` | symmetric repair, obstruction, relabelling and exhaustive classification certificates |
| `DirectedTriangleRepair` | oriented triangle convention; `LocalLaws`, `AnchoredLaws`, `Problem.step_preserves_at`, `Problem.uniform_choice` |
| `DirectedTriangleCertificates` | all 128 oriented palettes; 16 small-AP classes; 15 local repairs; anchored repair for palette 37; `no_empty_rule`; `poset_triangle_iff` |

Full types include internal relations, unary/diagonal information and repeated
entries. Big Ramsey degrees count all embeddings. Enumerations are not relation
symbols; every tuple size at most n is tested. The maximum-arity convention is
sharp, with value one for the empty language.

## Full-type and continuation interfaces

`FullTypeMap n A B` retains an ordered base embedding and a total action on all
full types, including types outside any specified class. Its extension law is
an equivalence of relation values. Coherence is required for every increasing
coordinate injection, not just initial subtuples. Identity, composition,
component injectivity and preservation of the whole future diagram are proved.
In a binary language the one-type component determines every component; this
uses the extension law and does not discard internal future relations.

A `Continuation A` contains a finite base `A : RelStructure L (Fin a)` as the
exact initial segment. `mem_prefix` proves that there are no extra vertices in
that segment. `FutureTuple` lies entirely beyond it and is strictly increasing.
`future_evaluate_injective` verifies the distinctness and disjointness of all
names used by `Continuation.typeOf`; realised types are not merely diagrams
pulled back along a potentially non-injective map.

`Continuation.Approximates` records the base equality, the separation of future
vertices from the target base, and exact equality with the prescribed image
of every full type. `TypeRespectingMap` quantifies over unrestricted finite or
countable continuations. `ClassTypeRespectingMap` adds class-relative witnesses;
its argument K is evaluated on the finite/countable age closure of a finite
class. Both predicates and approximation satisfy checked identity and
composition laws.

`NTypeRespectingAmalgamation` is the manuscript's actual one-new-last-vertex
lifting property. Its commuting squares are equal on the entire structural
maps, not just the bases or valid types. One solution map is chosen outside all
continuation quantifiers. The unqualified predicate uses `MaximumArity.value - 1`.
These are now concrete definitions, not assumptions that a class satisfies them.

The manuscript proves a direct full-type free-amalgamation theorem with any
family of forbidden finite irreducibles, and binary invariance under
quantifier-free definitional expansions. The relational irreducible-cover step
is checked here; the complete class-level constructions are still written proofs.
In particular, no finite big Ramsey conclusion for an infinite forbidden family
is inferred from this amalgamation result.

## Directed and anchored repair

`T a b c` means labels 01=a, 12=b, 02=c. Pair reversal is an involution, not
an assumption of symmetry. `DirectedTriangleRepair.Problem` processes an
arbitrary finite list of anchors, preserving one root, every earlier constraint,
all possible future-pair relations (including repeated types), and prescribed
image values. This is not a bounded-base search.

The directed certificates use 0=forward, 1=backward, 2=absent. The seven triangle
orbits are transitive tournament, cyclic tournament, directed path, in-star,
out-star, single arc and empty. The 16 small-strong-AP palettes are
33,35,37,63,89,90,91,92,95,97,99,121,124,125,126,127. Fifteen have local repairs;
37 has anchored repairs for all 18 admissible labelled base triangles and
`no_empty_rule` excludes empty-source requests. Palette 121 encodes transitivity.
The manuscript proves the small-test-to-arbitrary-base implication.

All finite certificates use ordinary kernel `decide`, not `native_decide`.
The search generator is not part of the trusted proof. The bridge from these
constraint constructions to the now-defined class-level predicate is not yet
formalized, nor is the finite-quotient interpretation of the symmetric exception.

## Validation

Foundations passed at b44a67b98744, metric scalar interpolation at 36c600fa1ced,
group/two-colour interfaces at 424ea0ad09e6, and symmetric repair/certificates at
04b7a27d8003 (run 38299496216). Directed modules and their finite certificates
passed at d99467e1771a (run 38306671021).

The new relational full-type modules and the complete existing library passed
at `77a1478517f5592fcf1a23dc7ec266f24d0b3d28`, Actions run `38314435247`, job
`115027580808`, on Lean `v4.35.0-rc3`. The checked PR merge was
`c0b405a5f4714ad1f39295ea5cedf57df408410f`. All four new modules are imported by
the root library. Both proof-dependency reports passed with only standard Lean
axioms and no `sorryAx`. Earlier elaboration failures were corrected without
weakening the statements. The temporary duplicate workflow was removed; the
single workflow now checks both reports with `set -euo pipefail`.

## Remaining proofs

Implement binary one-type extension and insertion constructors, then instantiate
the new continuation predicates with the free-amalgamation, metric and triangle
constructions. Formalize canonical lifting/reduction for definitional expansions,
including the auxiliary composite needed when arbitrary expanded type maps are
noncanonical outside the class. The constructor extending a one-type map to all
finite sizes, exact splits, the general maximum-arity reduction, and concrete
metric endpoint geometry also remain to be formalized.

The general cycles-and-cliques implication is not assumed. The lattice-valued
development remains on its separate branch. Internal weak-type comparison
material stays out of this public repository. Mathematical reviews are
self-audits; no independently spawned referee report is claimed.
