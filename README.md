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
