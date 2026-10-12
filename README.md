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
| `MetricInterpolation` | `clip`, `clip_bounds`, `clip_fixed`, `clip_pos`, `clip_lipschitz`, `clip_sum_lower`, `interpolation`: natural-number scalar core of the metric extension formula |

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
this property. Arbitrary coordinate-map restriction remains available as a
more general statement about pulled-back relational diagrams.

## Validation status

Foundational commit `b44a67b98744590825680904a5d8d53140dd7ffb` passed the complete
build and proof-dependency checks on Lean `v4.35.0-rc3` in Actions run `38271277558`.
CI rejects unchecked declarations in the library, and `Checks.lean` reports
proof dependencies. No custom axiom or proof placeholder is used.
Kernel checking proves the written Lean statements; it does not by itself
establish correspondence with every manuscript formulation.

The metric interpolation module at commit
`36c600fa1cedca9d00cc5b68a4932ddada42c080` passed the build and dependency
checks in Actions run `38279289894`, job `114912340613`, on Lean `v4.35.0-rc3`.
The CI checkout was the test merge `251addfb9be48c0031bbf5fc359732f6ee5779cb`.
Only the standard Lean axioms occur; no `sorryAx` was reported.
This proves an arithmetic implication with explicit premises, not the metric
type-amalgamation theorem. The manuscript supplies the written proofs that
geometric type bounds satisfy these premises. Instantiating them in Lean is
still required.

## Remaining interfaces and proofs

Finite coherent full-type maps, their uniform continuation property and the
manuscript's `n`-type-respecting amalgamation property are not yet encoded.
The exact-split equivalence and maximum-arity reduction have written manuscript
proofs but are not yet Lean proved. For metric amalgamation, next encode valid
one-point types, the lower and upper bounds for distances between two types,
restriction to a subbase, and the class-relative interpretation of interpolation.
The finite-distance-monoid version needs its own ordered-monoid scalar interface;
the present module uses ordinary addition on natural numbers only.

No general upper-bound Ramsey theorem or unrestricted cycles-and-cliques
amalgamation theorem is assumed. Internal manuscript comparison material remains
absent from this public repository.
