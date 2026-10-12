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

Commit `b44a67b98744590825680904a5d8d53140dd7ffb` passed the complete build and
proof-dependency checks on Lean `v4.35.0-rc3` in GitHub Actions run `38271277558`.
CI rejects unchecked declarations in the library, and `Checks.lean` reports
proof dependencies for the restriction and embedding-closure lemmas.
No `sorry` or custom axiom is used. Kernel checking proves the written Lean
statements; it does not by itself establish correspondence with every manuscript
formulation or prove the remaining mathematical results.

## Remaining interfaces and proofs

Finite coherent full-type maps, their uniform continuation property and the
manuscript's `n`-type-respecting amalgamation property are not yet encoded.
The exact-split equivalence and maximum-arity reduction have written manuscript
proofs but are not yet Lean proved. No general upper-bound Ramsey theorem or
unrestricted implication between alternative amalgamation properties is assumed.

Internal manuscript comparison material is deliberately absent from this public
repository. See the companion manuscript README for its internal source index.
