# All those big Ramsey degrees — Lean

Companion formalization of `janhubicka/All-those-big-Ramsey-degrees`.
The manuscript is authoritative for mathematical scope. This is a Lean/Std-only
library with no mathlib dependency. Run `lake build`, then `lake env lean Checks.lean`.

## Interface index

| Module | Main interfaces |
| --- | --- |
| `Relational` | `Language`, `RelStructure`, `Embedding`, `Enumeration`, `EnumeratedStructure`, `OrderedEmbedding`, `BigRamseyBound`, `IsBigRamseyDegree`, `HasFiniteBigRamseyDegrees` |
| `FullTypes` | `FullType`, `typeOf`, `SameFullType`, `evaluate_reindex`, `evaluate_rebase`, restriction to coordinates and parameters |
| `TypeRespecting` | `Prefix`, `TailTuple`, `SameType`, `NTypeRespecting`, `MaximumArity`, `TypeRespecting`; identities, composition and downward monotonicity |
| `MetricInterpolation` | `clip`, `clip_bounds`, `clip_fixed`, `clip_pos`, `clip_lipschitz`, `clip_sum_lower`, `interpolation`: natural-number scalar core |
| `GroupLabelTypes` | `Compatible`, `eq_of_anchor`, `restrict_compatible`, `restriction_injective`, `typeMap_covers`, `same_profile_pair` |
| `TwoColourTriangles` | `Triangle`, `SmallSAP`, `Listed`, `classification`, `mixed_only_fails`: exact small-base palette classification |

Full types mean **full quantifier-free types**, including all internal relations,
unary information and repeated relation entries. Big Ramsey degrees count
embeddings. Enumeration is separate from the language. `NTypeRespecting n` tests
all tuple sizes at most `n`, including near the end of a finite structure.
`MaximumArity` requires positivity, the upper bound on every relation arity and
sharpness (or value one). Thus `TypeRespecting` cannot silently use an arbitrary
arity parameter. The empty-language convention is maximum value one.

`typeOf` and `SameFullType` are implemented by atomic relational diagrams.
For their interpretation as realised full types, the combined parameter and
future-vertex naming must be injective. The `Prefix`/`TailTuple` application has
this property. Arbitrary coordinate-map restriction remains available for more
general pulled-back relational diagrams.

## Validation and scope

Foundations at `b44a67b98744590825680904a5d8d53140dd7ffb` passed Lean
`v4.35.0-rc3` in Actions run `38271277558`. The metric scalar module at
`36c600fa1cedca9d00cc5b68a4932ddada42c080` passed build and dependency checks
in run `38279289894`, job `114912340613` (test merge `251addfb9be48c0031bbf5fc359732f6ee5779cb`).
Only standard Lean axioms occur. No proof placeholder or custom axiom is used.

The group-profile and palette modules are submitted for CI. The former proves
actual anchor determination and surjectivity from a restriction-section law,
with left cancellation explicitly assumed. It does not assume surjectivity or
TRAP. The latter checks actual one-point amalgamation requests over one- and
two-vertex bases and classifies their 16 palettes by ordinary kernel reduction,
not native evaluation. Neither module yet proves the class-level TRAP theorem.

## Remaining interfaces and proofs

Coherent full-type maps, their uniform continuation property and the manuscript
amalgamation property are not yet encoded. The exact-split equivalence,
maximum-arity reduction and covered-type lifting criterion have written proofs
but are not Lean proved. For metric amalgamation the concrete endpoint geometry
and all-continuations interpretation are still required; the present arithmetic
module uses ordinary natural-number addition, not arbitrary distance monoids.

For group-labelled structures, encode the finite relational language and prove
that compatible profiles are exactly valid full one-types. Then connect the
checked coverage lemma to the written covered-type lifting argument. Strong
amalgamation and cycle completion also retain written, not formalized, proofs.
For the seven two-colour classes, formalize their identifications with graphs,
ultrametrics and at-most-two equivalence classes. The current palette theorem
is a precise necessary finite condition, not a hidden assertion of TRAP.

No general upper-bound Ramsey theorem or unrestricted cycles-and-cliques
amalgamation theorem is assumed. Internal weak-type comparison material remains
absent from this public repository. Reviews are not independently spawned
referee reports.
