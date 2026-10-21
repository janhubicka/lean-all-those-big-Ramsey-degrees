# All those big Ramsey degrees — Lean

Companion to `janhubicka/All-those-big-Ramsey-degrees`, which is authoritative
for mathematical scope. Lean/Std only. Run `lake build`, then
`lake env lean Checks.lean`, `lake env lean ChecksFullTypes.lean`, and
`lake env lean PartialTypesChecks.lean`.

## Interface index

| Module | Main interfaces |
| --- | --- |
| `Relational` | structures, induced embeddings, separate enumerations, ordinary embedding big Ramsey degrees |
| `ZeroTypePosetObstruction` | `basePrime_valid`, `continuation_valid`, `no_amalgam_of_poset_and_E`: kernel-checked nonamalgamation obstruction for successor-marked posets |
| `FullTypes` | full atomic diagrams, evaluation, coordinate and base restriction |
| `TypeRespecting` | `Prefix`, `TailTuple`, `NTypeRespecting`, `MaximumArity`, `TypeRespecting`; identity/composition/monotonicity |
| `BinaryFullTypes` | `FullType.futureDiagram`, `FullType.binary_ext`: reconstruct a binary full type from singletons AND its internal future diagram |
| `FullTypeMaps` | `FullTypeMap`, `id`, `comp`, `onType_injective`, `future_preserved`, `binary_determined_by_one` |
| `TypeAmalgamation` | `Continuation`, `FutureTuple`, `Approximates`, `TypeRespectingMap`, `ClassTypeRespectingMap`, `ExtendsByLast`, `NTypeRespectingAmalgamation`, `TypeRespectingAmalgamation` |
| `IrreducibleCover` | relational `Irreducible`, actual induced embeddings, `range_in_one_side`, `Avoids`, `avoids_of_free_cover`; no size bound on the forbidden structure |
| `ClosedMatching` | `mate`, `Edge`, `Closed`, `closure`, `BlockEmbedding`, `closure_natural`, `appendBlock`, `append_disjoint` |
| `MarkedFreeTransfer` | `GuardedAt`, `forbidden_future_is_prescribed`, `guarded_of_no_positive_off_image`: irreducible-copy obstruction for the binary free-marked TRAP construction |
| `MetricInterpolation` | natural-number scalar clipping and `interpolation` |
| `LatticeInterpolation` | `LatticeAdd`, `clip`, `clip_bounds`, `clip_fixed`, `clip_nonzero`, `clip_nonexpansive`, `clip_pair_bound`, `interpolation`: partially ordered scalar core |
| `GroupLabelTypes` | compatible profiles, anchor determination, restriction injectivity and covered types |
| `TwoColourTriangles` | exact small-amalgamation classification of two-colour palettes |
| `TriangleRepair` | `RepairSystem`, `step_anchor`, `uniform_choice` on arbitrary type sets and finite bases |
| `ThreeColourCertificates` | symmetric repair, obstruction, relabelling and exhaustive classification certificates |
| `DirectedTriangleRepair` | oriented triangle convention; `LocalLaws`, `AnchoredLaws`, `Problem.step_preserves_at`, `Problem.uniform_choice` |
| `DirectedTriangleCertificates` | all 128 oriented palettes; 16 small-AP classes; 15 local repairs; anchored repair for palette 37; `no_empty_rule`; `poset_triangle_iff` |
| `CompletionTransport` | `PrefixSystem` tree-order laws; `CoherentCompletion.below_iff`, `compatible_iff`; `no_common_socle_completion`; `antichain_not_order_reflected_in_chain` |
| `OneTypeCompletion` | actual full diagrams: `neutral`, `neutral_base`, `neutral_extends`, `complete`, `complete_prescribed`, `complete_extends` |
| `CanonicalSocle` | ordered finite-solution choice; `Scheme.complete_append_prefix`, `preserves_compatibility`, `decode_complete`, `reflects_prefix_of_faithful`, `visible_independent` |
| `SupportClosed` | `PairMarked`, `neutralise`, `Irreducible`, `lift_embedding`, `neutralise_omits_irreducible`, `neutralise_unique`, `neutralise_restrict` |

Full types include internal relations, unary/diagonal information and repeated
entries. The naming of parameters and future vertices is injective in the
`Prefix`/`TailTuple` application. Big Ramsey degrees count all embeddings.
Enumerations are not relation symbols; every tuple size at most n is tested.
The maximum-arity convention is sharp, with value one for the empty language.

## Transfer to successor-marked binary free amalgamation

The manuscript main theorem `thm:binary-free-marked-main` proves
prefix-TRAP for successor (E)-marked (0)-types whenever the reduct is a
binary relational free amalgamation age described by forbidden induced
irreducible structures. It needs no separate TRAP assumption on the
reduct. The proof reconstructs selected source vertices using isolated
spacers, restores the free-level relation, and compares the candidate
output with the class-admissible prescribed map on its image types.
Invalid syntactic singleton types retain the original candidate.

`MarkedFreeTransfer.forbidden_future_is_prescribed` checks a key
obstruction: a forbidden irreducible copy containing the inserted
vertex cannot contain an off-image future vertex when all positive
new relations to off-image vertices are forbidden.
This lemma is valid at arbitrary arity, but by itself does not show
that all *higher tuple* types lie in the image; that is why the main
transfer theorem is presently binary.

The complete class-level binary marked TRAP theorem and the
E-spacer construction are **written manuscript proofs** and have
not been packaged as a single Lean theorem yet. The guarded
forbidden-copy core and proof-dependency checks passed in run
38462339224 after fixing an independent check-file import order.
No `sorryAx` is used.

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
The search generator is not part of the trusted proof. The full-type-map interfaces are now defined, but their class-level
construction from the repair criteria and the finite-quotient interpretation of
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

## Pairwise E-support and irreducible completion

The full-type manuscript repairs the adapted partial-type definition in
arity >= 3: a determined atom must have **pairwise E-marked support**,
not only lower vertices below the free level of its maximum. Positive
tuples containing type vertices obey the same requirement on ordinary
base pairs. Otherwise a ternary relation can span two ordinary vertices
whose pair is not marked, and deleting undetermined binary relations can
create an induced irreducible forbidden structure.

`SupportClosed` proves the corresponding arbitrary-arity fact for
concrete `RelStructure` objects: if an irreducible forbidden F embeds
into the structure obtained by deleting positive tuples outside E-cliques,
that same map embeds F into the original structure. All negative and
repeated-coordinate atomic information is treated by induced embeddings.
The module also proves neutralisation uniqueness when supported diagrams
agree, and commutation with restrictions under injective maps.
The complete Lean build and both dependency reports passed at commit
`1fdc9e4093f517d9d8144457b669f0d54a36d883` in Actions run
`38434221232` (no `sorryAx`; standard Lean axioms only). The first CI
attempt built the module but the independent check file lacked its explicit
import; the import was added without modifying the theorem statements.


The intended application is canonical nodewise completion of individually
completable E-supported partial types in free amalgamation classes,
preserving socle compatibility and prefixes. This *does not* prove
a class-type-respecting continuation map for non-neutral prescriptions,
faithful recovery of E marks, or the general non-free TRAP transfer.
The corresponding manuscript theorem is a written proof; Lean checks
the central irreducibility argument and diagram operations, not the
complete partial-type syntax.

## Canonical socle recursion

For locally admissible socle steps, the manuscript constructs a finite,
nonempty set of TRAP solutions and selects the least by a fixed ordering
of atomic output tables. This selection is shared by every occurrence
of a marked socle. The visible composite after the step depends only on
the prescribed action on the image, not on values chosen outside it.

`CanonicalSocle` formalises the deterministic list recursion and proves
its prefix and same-socle compatibility preservation; the output agrees
on common source prefixes. It also proves that the visible composite
of two maps agreeing on an image is equal. An optional letterwise decoder
gives prefix reflection. **The decoder is an additional hypothesis**:
canonical choices alone can collapse distinct E-marked socles.
The manuscript isolates a finite simultaneous sibling-separation condition
sufficient for a faithful socle tree embedding and exact meets.

This Lean module does not formalise the local no-age test, the full
class-level TRAP property, or their construction from arbitrary partial
diagrams. It remains a separate structural component, not a representation
of the desired conclusion as an assumption. Commit
`1f0661ce93b502e11327874452054e5f2fc374ed` passed the full
build and dependency audits in Actions run `38428150366`;
the first attempt required correcting the final decoder rewrite.
No nonstandard axioms or sorry are used.

## Lattice-valued interpolation

`LatticeAdd` lists standard lattice and commutative monoid laws, with additive
translations preserving meets and joins. It assumes neither a linear order nor
an interpolation conclusion. The proved rule is
`clip lower upper original = meet (join lower original) upper`.
The pair-bound proof distributes addition over both meets; it never assumes
two arbitrary distance values are comparable. The positivity result separately
assumes that a meet of nonzero values is nonzero.

The manuscript instantiates this argument for finite lattice-valued metrics,
including distributive-lattice ultrametrics with meet-irreducible zero and any
finite number of bounded integer metrics on a common vertex set. Prescribed
type maps may mix coordinates. Metric endpoint geometry, the induced local
triangle repair, cycle completion and the relational TRAP interpretation are
written proofs, not yet Lean instantiations of this scalar module.

## Failure of the general K-to-partial-K TRAP transfer

The manuscript now proves an explicit full commuting TRAP square showing
that ordinary strict partial orders have TRAP but their literal
successor E-marked 0-type class fails **prefix-TRAP**. The latter class
is prefix-closed, not hereditary under arbitrary induced restrictions.
The square consists of K-class-admissible maps F and F', an unrestricted
candidate G0 with G0 F=F' on all syntactic full 1-types, and a B-continuation
D which cannot be extended over B'. The obstruction is z<a<x forcing
z<x, hence E(z,x) and E(b,x), contradicting D.

The new ZeroTypePosetObstruction module formally checks the two
three-point bases and proves that contradiction for an arbitrary
target position of x, so inserting filler vertices does not help.
The full class-level map F/F' construction is proved in the manuscript
and checked by the exhaustive Python regression, but it is NOT yet
formalised end-to-end in Lean. The negative conclusion is not
a proof of the purported positive transfer; that implication is false.

The complete library and all three dependency-check files passed at
commit `0a26c9d8d290004f043e0c9256238528e20e6941`,
GitHub Actions run `38448128338`, job `115471776369`.
The finite witnesses require no axioms, while
`no_amalgam_of_poset_and_E` uses only standard
`propext` and `Quot.sound`; no `sorryAx` occurs.
No independently spawned referee has signed off.

## Algebraicity and closure-relative block types

The matching-age example must not be used to refute closure-relative
TRAP: it fails the *unclosed* one-vertex TRAP because a base singleton
does not contain its unique mate. In the ordinary matching limit, the
finite closed subsets are unions of full two-vertex edges, and a
minimal nonempty closed extension adds a whole edge block.

`ClosedMatching` represents a finite closed matching by `Fin n × Bool`,
defines the mate involution, graph adjacency and the closure obtained
by adding partners, and proves closure preservation under embeddings
induced by injections of blocks. It also verifies that a singleton
vertex set is not closed, and that the newly appended block is
disjoint from every old block.

These are structural lemmas for the *closed age* of the matching
limit, not a class-level formalization of the new
closure-relative TRAP definition. The manuscript proves the
canonical block insertion: every valid type of k new complete
blocks over a closed base is a disjoint union of edges. General
Hrushovski strong/d-closed type interfaces require generated
closure restrictions, not vertex-only one-types. They are not
provided by this toy model.

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

Next connect the exact full-type-map and class-relative continuation interfaces
to the checked constraint constructions. Exact splits, the
maximum-arity reduction and concrete metric endpoint geometry remain to be
formalized. The general cycles-and-cliques theorem, beyond the stated small-pair
triangle cases, is not assumed.

Lattice-valued interpolation has been integrated; concrete metric endpoint
instantiations remain to be formalized. Internal weak-type comparison material stays out of the
public Lean repository. No independently spawned referee report is claimed.
