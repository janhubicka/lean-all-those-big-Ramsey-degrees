# All those big Ramsey degrees — Lean

Companion formalization of `janhubicka/All-those-big-Ramsey-degrees`.
The manuscript is authoritative for mathematical scope. The source presently uses
only Lean/Std; there is no mathlib dependency. Run `lake build`.

## Interface index

| Module | Main interfaces |
| --- | --- |
| `Relational` | `Language`, `RelStructure`, `Embedding`, `Enumeration`, `EnumeratedStructure`, `OrderedEmbedding`, `BigRamseyBound`, `IsBigRamseyDegree`, `HasFiniteBigRamseyDegrees` |
| `FullTypes` | `FullType`, `typeOf`, `SameFullType`, restriction to coordinates and parameters |
| `TypeRespecting` | `Prefix`, `TailTuple`, `SameType`, `NTypeRespecting`, `TypeRespecting`; identities, composition and downward monotonicity |

Full types mean **full quantifier-free types**, including all internal relations,
unary information and repeated relation entries. Big Ramsey degrees count
embeddings. Enumeration is separate from the language. `NTypeRespecting n` tests
all tuple sizes at most `n`, including near the end of a finite structure.
The parameter `r` in `TypeRespecting r` must be the maximum positive relation
arity; proving/packaging this arity hypothesis is a remaining interface task.

## Validation status and remaining work

Initial source is submitted to CI; a successful kernel build must be checked
before any declaration is described as verified. No `sorry` or custom axiom is
used. These foundations do not prove an upper-bound Ramsey theorem, and no
unrestricted implication between alternative amalgamation properties is assumed.

Remaining concrete interfaces: finite coherent full-type maps, their uniform
continuation property, and the manuscript's `n`-type-respecting amalgamation
property; exact-split equivalence and the maximum-arity reduction lemma.
Internal manuscript comparison material is deliberately not copied into this
public repository.
