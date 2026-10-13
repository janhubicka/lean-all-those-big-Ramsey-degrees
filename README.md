# All those big Ramsey degrees — Lean

Companion to `janhubicka/All-those-big-Ramsey-degrees`, which is authoritative
for mathematical scope. Lean/Std only. Run `lake build`, then
`lake env lean Checks.lean` and `lake env lean PartialTypesChecks.lean`.

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
| `CompletionTransport` | `PrefixSystem` tree-order laws; `CoherentCompletion.below_iff`, `compatible_iff`; `no_common_socle_completion`; `antichain_not_order_reflected_in_chain` |
| `OneTypeCompletion` | actual full diagrams: `neutral`, `neutral_base`, `neutral_extends`, `complete`, `complete_prescribed`, `complete_extends` |

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

## Partial types and coherent completion

The companion section distinguishes literal successor E-marked types from
partial diagrams with undetermined relations. Individual completability does
not imply a common-socle completion, even for two-distance ultrametrics.
The Boolean certificate `no_common_socle_completion` verifies the finite
obstruction. The class's TRAP proof remains a written mathematical argument.

`CoherentCompletion` records a map commuting with prefixes, a strictly increasing
level map, an erasure left inverse, and an independent map on socles with its
own erasure. The order and compatibility equivalences are derived, not fields
of the interface. `PrefixSystem` also proves reflexivity, antisymmetry,
transitivity and comparability of predecessors. These are useful structural
consequences of canonical insertion; constructing this interface from concrete
relational full-type maps and TRAP is NOT formalized here. Meet preservation,
arbitrary subtuple restriction and the locally finite iteration remain written
proofs.

The completion-transport module and complete library passed at
`c21d5a9063119a9cce047cf2dbad68158106f39c`, Actions run `38408635079`, job
`115334834029`. Both dependency reports and the rejection of unchecked
declarations passed. The first attempt lacked a Decidable instance for the
Boolean triangle predicate; adding that instance changed no statement.
This checkpoint verifies structural transport and the finite obstructions,
not an end-to-end theorem about relational type maps or arbitrary partial types.

## Concrete one-type prescriptions

`OneTypeCompletion` uses the existing `FullType` relational diagrams directly.
For a base A, a one-point extension B of A, and a full one-type p over A,
`neutral B p` keeps the entire base B and the entire old type p, and assigns
false to tuples meeting both the inserted vertex and the old future vertex.
Its restriction proofs include negative relations, loops and repeated entries.
`complete` replaces this default by the prescribed full type on any chosen
set S; its two main lemmas retain the prescription and every old relation.
These constructions are for full one-types, although their relational language
may have arbitrary arities.

The initial concrete module passed at
`472691bc5bef4ad394c294480bc34fc343ddbb33`, Actions run `38419931632`, job
`115374262354`, with test-merge checkout
`729c20b042a4e33408d7887a1b7f2dbc5a04bcd2`. The new endpoints use only standard
Lean axioms, without `sorryAx`. Deprecated conditional simplification names
were replaced; the cleaned code passed at
`cce6887cb32534178a67787b1223d9afd6e1986d`, Actions run `38421563336`.

This does not prove membership in any restricted class. The manuscript's
all-arity extension uses exact type-vertex supports in individual relation
tuples; a whole-type neutral fallback is not coherent for arbitrary larger
types. The coherent higher-type family, the unrestricted continuation proof,
the image-continuation recognition lemma, the finite no-age test and the
class-level TRAP theorem remain written proofs. Outside binary free amalgamation,
the prescribed domain still has to be the image of a known admissible F.
The generic raw partial-diagram completion claim is not assumed.

## Validation and remaining work

Foundations passed at b44a67b98744, metric scalar interpolation at 36c600fa1ced,
group/two-colour interfaces at 424ea0ad09e6. Symmetric arbitrary-base repair and
its certificates passed at 04b7a27d8003, Actions run 38299496216.

Both directed modules and the complete library passed at
`d99467e1771a5003592fd103cff863f4bed497c4`, Actions run `38306671021`, job
`115002522912`, on Lean `v4.35.0-rc3`. The checked PR merge was
`3a5164bc1a52413b29ce271147e5756a803afd88`. The consolidated `Checks.lean`
report covers the arbitrary-base anchored theorem, exhaustive palette
classification, local and anchored tables, empty-source obstruction and literal
poset transitivity. Only standard Lean axioms occur; no `sorryAx` is reported.
The finite certificate module compiled in 104 seconds. Earlier instance-size and
evaluation-order failures were repaired without weakening any finite claim.

Next formalize the exact full-type-map and class-relative continuation interfaces
and connect the checked constraint constructions to them. Exact splits, the
maximum-arity reduction and concrete metric endpoint geometry remain to be
formalized. The general cycles-and-cliques theorem, beyond the stated small-pair
triangle cases, is not assumed.

The lattice-valued interpolation development is on a separate branch; this change
does not overwrite it. Internal weak-type comparison material stays out of the
public Lean repository. No independently spawned referee report is claimed.
