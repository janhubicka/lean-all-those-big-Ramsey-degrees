# Audit of *Big Ramsey degrees in the pseudotree*

Audit date: 2026-11-24. Manuscript supplied as `pseudotree_degrees(1).tex`.
Repository base: `2aac35dd2b7bc7eba00a9e9b07569d86cf99c136`.

## Verdict and scope

The mathematical audit found one false intermediate sentence, a definition
that needed greater precision, and several opportunities to shorten the
presentation. The false sentence is locally repairable: the subsequent
argument needs a correct leftmost-branch assertion, not the false assertion
about the lexicographically least chain member. Independent reviews of the
upper-bound fusion and lower-bound realization arguments found no further
mathematical obstruction. That is a mathematical audit judgment, not a claim
that each sentence of the original manuscript is correct as written. The
revised proof is supported by the end-to-end Lean theorems described below.

The Lean development now proves the concrete ternary model is the Fraïssé
limit of the independently defined class of finite binary meet-trees. It also
proves the full infinite-degree result for every finite substructure of this
model containing incomparable elements. The latter includes a finite
colouring invariant under changing the embedding with the same image, so it
really gives a result for copies, as in the manuscript.

The exact chain-degree theorem is now an **end-to-end Lean theorem for every
positive `n`**, in the repository's original `IsBigRamseyDegree` API:

```lean
theorem chain_degree (n : Nat) (hn : 0 < n) :
    IsBigRamseyDegree (RepoBridge.model (Fin n))
      (RepoBridge.model TernaryModel) (some (diaryCount true n 1))
```

This is `AllThoseBigRamsey.Pseudotree.chain_degree` in
`PseudotreeValidation/ChainDegrees.lean`. Its targeted source build completed
successfully with 3,453 dependency jobs. The final optional-package build
also passed, with 3,457 jobs. Its namespace-wide audit checked all 3,160
pseudotree declarations and found only `propext`, `Classical.choice` and
`Quot.sound`. Both `chain_degree` and the raw-diary-cardinality endpoint
`chain_degree_diaries` were checked explicitly. The Lean/Std root build,
all three pre-existing check files, and its separate audit of 1,304
pseudotree declarations also passed. Verification logs are retained under
`validation/pseudotree/verification/`.

The result uses the actual proved mixed ray-preserving Ramsey lemma,
restricted finite-tree canonization, identification of the generated sparse
set with the model, extraction from every sparse chain, realization in every
sparse self-copy, and uniqueness of realized diary types. None of these is
left as an assumed Ramsey or normalization premise in `chain_degree`.
`paperDiary_card` identifies its bound with the number of the manuscript's
independently defined finite-set diaries, for every size. Thus the first
values are

| `n` | 1 | 2 | 3 | 4 | 5 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Exact degree of `Cₙ` in Ψ₂ | 1 | 7 | 157 | 7,927 | 727,741 |

The general incomparable theorem also applies to any countable dense
homogeneous meet-tree with the stated second-branch property. This supplies
the mathematical argument for Ψω, but the development does **not** construct
and identify a separate concrete Ψω model. That is the remaining model scope
qualification; it is not a missing step in the exact Ψ₂ chain theorem.

## Corrections and proof simplifications

### 1. Correct the lexicographic claim in the sparse lemma

The original proof of the sparse-copy lemma calls
`v_* = max_preorder C` the lexicographically least member of `C`. This is false
when coding nodes are prefix-comparable. The construction itself gives

```
x₀ = 02
x₂ = 02122202
```

The first word is a proper prefix of the second, so ordinary lexicographic
order puts it first. In the pseudotree order, the second is larger. The Lean
regression `prefix_chain_regression` verifies this comparable pair directly
using the literal block-order definition.

The correct replacement is:

> Every member of `C` is either a prefix of `v_*`, or is prefix-incomparable
> with and lexicographically larger than `v_*`. Thus `v_*` determines the
> leftmost branch of the prefix closure of `C`.

Two facts give this assertion. The order-reversal clause of the ternary-model
lemma handles prefix-incomparable words. The sparse construction's earlier
observation that every proper extension of a coding node begins with `1`
rules out a chain member properly extending its maximum. This is precisely
what the compression proof uses. The revised manuscript explicitly cites
both facts.

The general order-reversal clause is separately proved for **all** literal
ternary words in `Pseudotree/WordLex.lean`, without any sparse-membership
assumption. `wordBelow_prefix_or_lex` states the prefix-or-reversal
dichotomy, and `wordBelow_prefix_incomparable_lex` is the exact clause printed
in the ternary-model lemma. The proof strips equal first letters and checks
the possible first disagreement; it uses only `propext` and `Quot.sound`.

### 2. Replace the long no-isolation argument by finite avoidance

For a fixed enumeration `t₀,t₁,…`, retain the definitions

\[
\lambda(a)=\min\{i:a\le t_i\},\qquad
p(a)=\lambda[D(a)].
\]

For a self-copy `S`, let `X` consist of profiles repeated at two comparable
points of `S`. Suppose `u<a` witnesses `s∈X`, and fix `N≥max s`. Choose

\[
x\in(u,a)_S\setminus\{a\wedge t_i:i\le N\}.
\]

This is possible because the interval is infinite and the forbidden set is
finite. Choose `z>x` in the other cone from `a`, and then choose `b>z` whose
profile is repeated. Thus `a∧b=x`.

If `x<q≤b` had `λ(q)=i≤N`, then `q≤t_i` and `a∧q=x`. The points `q` and
`a∧t_i` are comparable below `t_i`. Since `q` cannot lie below `a`, it follows
that `a∧t_i≤q`; the two inequalities then give `a∧t_i=x`, contradicting the
choice of `x`. Consequently all new labels in `p(b)` exceed `N`, and `p(b)`
properly end-extends `s`.

This removes the need to construct an entire family of branch intervals and
then prove they are pairwise incomparable. The proof is formalized as
`Profiles.System.repeated_endExtension`, and is used by the actual
infinite-degree theorem, not merely recorded as an abstract desired property.

### 3. Use the end-extension formulation of FIN directly

The proof only needs this elementary property of a nonempty family `X` of
finite subsets of the naturals: for each `s∈X` and each bound `N`, there is a
proper extension `t∈X` whose new elements all exceed `N`. The revised
oscillation lemma states this property directly, removing the unnecessary
topological reformulation from the preliminaries.

The oscillation lemma has a short constructive proof. Start with equal
coordinates and alternately end-extend one coordinate beyond the union of
both. Every step adds a nonempty block on the opposite side of the symmetric
difference and therefore adds exactly one oscillation. `Oscillation` proves
this with finite binary characteristic words; `FiniteOscillation` proves the
translation to actual `Finset ℕ`, including padding invariance and the fact
that inclusion implies oscillation at most one.

### 4. Unify the strong-embedding definitions

Use one strong-embedding definition for a nonempty prefix-closed domain `F`,
finite or infinite: a strictly increasing level map and preservation of each
edge's first letter. Add the single ray condition that padding after `0` and
`2` contains no `1`. There is no additional padding restriction after `1`.

The Lean `RayStrongMap` follows this local definition. In particular,
injectivity is a theorem, not a redundant field. Binary-ray preservation,
composition and the factorization of a fusion limit through every sufficiently
early stage are proved from these conditions.

The finite grafting lemma must retain its restriction: a prescribed *ternary*
map at the boundary is allowed only at the root or at a node whose incoming
edge is `1`. Otherwise a new root containing `1` could violate the binary
padding condition on the preceding edge. A prescribed binary map is harmless
at any boundary node. Deleting this distinction would make the lemma false.

### 5. Keep the one-ternary-factor restriction and stabilization

Ordinary strong subtrees need not preserve the manuscript's pseudotree rays.
Thus an ordinary Milliken theorem cannot simply be substituted for the
ray-preserving statement by changing its name.

The mixed lemma's preliminary fusion makes colours stable along binary
extensions. Dense-matrix Halpern–Läuchli can then choose the `1` extensions,
while the stabilized colour handles the `0` and `2` extensions. This separation
is a real mathematical step.

Allowing two ternary factors is false. Compare the positions of the last `1`
in the two coordinates, using `-1` if there is no `1`. Any synchronized
ray-preserving maps `f,g` give opposite colours to `(f(1),g(0))` and
`(f(0),g(1))`. `RayObstruction.two_ternary_obstruction` checks exactly this
counterexample; it actually needs only equal image-root lengths.

### 6. Make diary finiteness explicit, and keep all four events

The split clause now says **exactly** the two immediate successors labelled
`0` and `2`. This avoids leaving a third successor formally unexcluded.

If `a,b,c,d` count the four event types, then

\[
a=b-1,\qquad b+c=n,\qquad d\le a+b-1.
\]

The last inequality associates every type-(d) level with its preceding
type-(a) or type-(b) level, excluding the final type-(b) level. Hence

\[
h=a+b+c+d\le4n-3.
\]

This replaces the qualitative finiteness argument with an explicit bound.
The event-grammar formalization proves the bound and constructs a diary
attaining it for every positive size.

Type (d) is not removable definition baggage. It records a first change of
ray between retained critical levels. Such changes affect the pair types
already; omitting them loses some of the seven pair diaries. The restriction
against initial or consecutive type-(d) levels is also part of the counting
and normalization argument. Keeping the event while bundling an optional
type-(d) step after an eligible event gives a compact recursive grammar.

### 7. Make the external citations exact

The dense-matrix form is supported by Theorem 3.2 **and its proof** in
Todorčević, pp. 51–52; it is not the literal statement of Theorem 3.2 alone.
The oscillation reference is now marked “cf. Lemma 6.35”, with the elementary
end-extension proof supplied in full.

The inspected CDW version is arXiv:2503.22626v4 (18 August 2026). Its Theorem
1.8 gives finite upper bounds for chains; Definition 3.3 and Theorem 5.3 are
the cited diary definition and extraction theorem. The note's normalized
diary definition is stricter than their general formal definition. The
manuscript states this distinction explicitly. The new exact values for
larger chains are claims of the supplied note, not results imported from CDW.

### 8. Use the universal maximum-spine lemma

The relevant branch property does not require sparsity. For arbitrary words
in the concrete ternary model,

\[
w\preceq v,\qquad w=p\mathbin{\frown}1\mathbin{\frown}t
\quad\Longrightarrow\quad
p\mathbin{\frown}1\text{ is a prefix of }v.
\]

This follows directly from the block order: once the smaller point has
entered the cone through a `1`, every point above it stays in that cone.
`DiaryRecovery.one_prefix_of_le` proves it for the actual word model. If `v`
is the maximum of a finite chain, every `1` in every member therefore lies
on `v`'s branch. `DiaryRecovery.spine_of_maximum` packages this statement.

Use this universal lemma wherever the proof only needs control of `1`
positions. The stronger description in Section 1, including lexicographic
placement of other branches, still uses the sparse construction. Separating
these assertions shortens the normalization argument and makes its precise
dependence on sparsity visible.

### 9. Recover diary types with one normalization operation

For a nonempty finite chain of coding words `C`, with its actual maximum `v`,
define its essential levels to be coding-word lengths and first-disagreement
levels of two coding words. Between consecutive essential levels, retain the
first `1` on the branch of `v` when the interval begins with a binary letter.
Project every coding word onto these retained coordinates; call the resulting
coding set `ν(C)`. This is the finite operation in `DiaryNormalization`, not a
choice of a previously existing diary.

The recovery proof reduces to two independently proved identities:

\[
\nu(f[C])=\nu(C),\qquad \nu(C_D)=C_D,
\]

where `f` is any ray-preserving strong map and `C_D` is the coding set of any
raw diary `D`. In the first identity the distinguished maximum is transported
by `f`; its validity is guaranteed by order preservation. More strongly,
`DiaryRecovery.codes_image` proves the corresponding pointed normalization
identity for arbitrary finite word sets and arbitrary distinguished words,
with no chain or sparsity hypothesis.

For the second identity, every split is witnessed by two coding descendants,
and every leaf or coding continuation is a coding endpoint. These are
essential levels. A turn is neither an endpoint nor a fork. It immediately
follows a split or leaf, whose entire frontier has no outgoing `1`, whereas
the turn's `1`-child has a coding descendant. The universal maximum-spine
lemma forces the maximum through that `1`. Thus precisely the prescribed
turn is retained as well, and **every original diary level is retained**.
`DiaryRecovery.selected_source` proves that the selected set is the whole
range of original levels; `codes_source` and `nodes_source` give the two
identity statements.

It follows immediately that two ray-preserving realizations with the same
coding image have the same diary, even if their level maps differ. This is
`DiaryRecovery.coding_image_unique`; `embeddedChain_unique` is its exact
functional-chain version used by the degree theorem.

The lower-bound proof can consequently focus on producing a ray-preserving
realization of each diary in the given subcopy. There is no need to carry a
second compression-level reconstruction invariant through the realization
induction: the general recovery theorem supplies the type afterward. This
is a substantive simplification of both proof and bookkeeping.

### 10. Remove derived diary data from the main definition

The finite-set definition remains useful because it states the four local
rules independently of an execution procedure. Several further objects can
be derived once, rather than supplied as independent diary data:

| Data | Why it is determined |
| --- | --- |
| Underlying prefix tree | It is exactly the prefix closure of the coding set: `PaperDiary.nodes_iff_prefix_code`. |
| Critical node and event kind at a level | `PaperLevel.unique` proves uniqueness from the local child and coding rules. |
| Ordered active frontier | Sort the nodes at the given level lexicographically; the raw-to-grammar translation proves that these are the intended frontiers. |
| Distinguished maximum and its `1`-branch | The coding nodes form an actual finite chain. The maximum is unique, and the spine lemma derives the branch condition. |
| Event trace and grammar object | The all-size bijection `Diary.toPaper` recovers a unique grammar diary from the raw tree. |
| Height bound and finiteness | They follow from event accounting and the exact grammar count. |

In particular, `PaperDiary.codes_ext` proves that equality of coding sets
implies equality of the full raw diaries. One can retain a named prefix tree
for readability while defining it from the coding set. The optional turn
flag and the “original branch still live” state belong in the counting
grammar; readers need not carry them as additional data throughout the
geometric proofs. The turn event itself and the binary-versus-ternary
boundary distinction in Section 4 remain mathematically necessary.

### 11. Shorten the sparse geometry and lower realization

The FIFO construction's fairness has a precise useful form: a queued slot
acquires only binary letters before it is selected. For a word shorter than
that slot, appending such a tail changes neither order comparison. The
upper and lower children of a later-generated endpoint therefore provide a
new sparse point between it and any comparable older endpoint. This proves
density directly; the designated two upper children have meet equal to the
parent code and inhabit both cones. `SparseOrder` proves these statements,
and `SparseModel` uses the already checked finite-extension argument to
identify this exact generated set with Ψ₂.

Two reductions also make the lower realization easier to organize. First,
an interval contains a nonempty subinterval in one ambient ray: choose a
point of maximal ray depth below its upper endpoint. Its ray coordinates
form a countable dense order, hence a rational suborder by mathlib. Second,
a finite-prefix pigeonhole argument supplies a rational suborder sharing an
arbitrarily long prefix. Two distinct words of the same prefix colour cannot
share a prefix shorter than the requested length, so no separate treatment
of finitely many short words is needed.

`LowerSplit` gives the two suborders at a splitting prefix. `LowerTurn` finds
the opposite-cone continuation inside an arbitrary functional self-copy,
using meet preservation and two inhabited cones. The ambient self-copy need
not preserve word coordinates. These local operations discharge all four
raw diary transition rules in `LowerTransition.exists_step`; `LowerAssembly`
then completes the finite construction to a total ray map. The final
`LowerRealization` theorems have no assumed transition, extraction, or
unavoidability premise.

## What Lean proves

All names below have prefix `AllThoseBigRamsey.Pseudotree` unless indicated.
The standard-library modules live in `AllThoseBigRamsey/Pseudotree/`.
Mathlib/Milliken modules live in the optional package
`validation/pseudotree/PseudotreeValidation/`.

| Manuscript component | Checked content | Scope boundary |
| --- | --- | --- |
| Binary ray and ternary model | `binary_dense`, `binary_no_endpoints`, parser/printer inverses, explicit meet GLB, `BinaryRay.nonempty_orderIso_rat`, `wordBelow_iff_toBlocks_le`, `toBlocks_wordMeet` | Literal words are explicitly related to the block model; this is not an abstract order left uninstantiated. |
| Cones, closure and finite extensions | Exactly two cones; finite meet closure; finite iff finitely generated; every embedding into the concrete model extends across finite binary meet-tree extensions | The functional language really contains meet; the relational-only finite-generation lemma is not misused. |
| Model identification | `RayTree.isUltrahomogeneous`, `RayTree.age_eq_finiteBinaryClass`, `ternaryModel_isFraisseLimit`, `finiteBinaryClass_isFraisse`, `ternaryModel_unique` | The age is defined independently of the concrete model. No general Fraïssé existence theorem is assumed. |
| Infinite degree in Ψ₂ | `Incomparables.arbitrarily_many_copy_colours`, `Incomparables.no_finite_bound`, `RepoBridge.incomparable_degree_infinite` | Full finite-colour quantifiers for every actual finite structure in the age with incomparable elements; image invariance proves the copy version, and the final endpoint uses the repository's degree API. |
| General incomparable theorem | `GenericIncomparables.no_finite_bound_of_countable` and its image-invariant witness theorem | Uses ordinary structural assumptions on a countable dense homogeneous meet-tree with a second branch. These cover Ψω mathematically, but no separately named Ψω model is constructed. |
| Tree Ramsey input | `finiteIndexedProductHL`, `finiteDemandDenseMatrices`, `heterogeneousFiniteDemandDenseMatrices`, `WordTrees.rayConeDenseMatrices`, `WordTrees.rayConeStrongMapsHL` | Derived from actual proved `lean-milliken` theorems, with explicit conversion to letter-preserving maps on the manuscript's words. |
| Mixed Ramsey lemma | `Mixed.exists_rayStable_embedding`, `Mixed.mixed_product`, `Mixed.mixed_level_product` | Full unconditional finite-colour statement, including zero binary factors. The last endpoint colours only the actual level product. |
| Ray-map algebra and model embedding | Injectivity, binary extensions, composition, coherent limits, `RayStrongMap.fusion_factors`; `RayMapModel.act_wordBelow` preserves and reflects the literal order, `act_wordMeet` preserves the literal meet, and `embedding` gives an actual functional-language self-embedding; `RayEmbeddings.finite_completion` and `finite_boundary_grafting`; two-factor obstruction | The boundary grafting retains the necessary restriction on incoming `1` for prescribed full ternary maps. |
| Restricted finite-tree canonization | `RayMilliken.restricted_milliken`, `DiaryCanonization.simultaneous`, `DiaryCanonization.simultaneous_total` | Actual finite prefix trees with at most one incoming `1` per level; arbitrary finite colourings of their realizable finite ray embeddings. The proof includes local fibre homogenization, finite batching and fusion. |
| Sparse queue and model | Correct lengths and distinct codes; exact binary-tail fairness; frontier separation and critical children; meet closure; `Sparse.sparse_dense`, `Sparse.sparse_no_endpoints`, `Sparse.sparse_fork`; `SparseModel.isFraisseLimit`, `SparseModel.selfEmbedding_range` | The carrier is exactly the explicitly generated FIFO set. Its density, branching, homogeneity and identification with the full model are proved. |
| Diary enumeration and correspondence | `diaryEnum_complete`, `diaryEnum_nodup`, `diaryCount_first_five`, `Diary.chain_height_bound`, `longestDiary_levels`; `PaperDiary.represented`, `Diary.paper_axioms`, `Diary.toPaper_injective`, `Diary.toPaper_surjective`, `paperDiary_card` | Exact all-size bijection and count for the independent raw finite-set diary definition, whose axioms mention no grammar execution. |
| Literal diary geometry | Prefix closure, exactly `n` distinct coding nodes, at most one incoming `1` per level, original-branch and event-order restrictions; `PaperDiary.nodes_iff_prefix_code`, `codes_ext`, `chainEmbedding`, `chainEmbedding_range` | The codes form an actual finite chain in the verified model, with an exact functional embedding of `Fin n`. |
| Sparse extraction | `SparseNormalization.normalized_axioms`, `SparseNormalization.extraction`, `SparseExtraction.representation`, `SparseExtraction.sparse_copy_representation` | Every nonempty actual finite chain in the sparse set has a raw diary and a ray-preserving realization. The final equality is equality of functional chain embeddings. |
| Realization in every sparse self-copy | `LowerRealization.sparse_realization`, `sparse_chain_realization`, `sparse_self_copy_realization` | Every raw diary is realized inside every functional self-copy of the sparse model. The local transition assumptions are discharged by actual geometric proofs. |
| Normalization and recovery | `DiaryRecovery.one_prefix_of_le`, `spine_of_maximum`, `codes_image`, `codes_source`, `image_recovery`, `coding_image_unique`, `embeddedChain_unique` | Universal maximum-spine property, naturality under arbitrary ray maps, identity on raw diaries, and unique diary type for equal coding images. No assumed recovery conclusion. |
| Original repository API | `RepoBridge.bound_iff`, `RepoBridge.singleton_degree`, `RepoBridge.incomparable_degree_infinite` | Functional meet/order embeddings correspond to embeddings of the relational structure carrying order and the graph of meet. Palette bounds are preserved. |
| Exact chain degrees | `chain_upper_bound`, `chain_degree`, `chain_degree_diaries` in `ChainDegrees.lean` | Unconditional for every `n > 0`, using the repository's original `BigRamseyBound` and `IsBigRamseyDegree`. The degree is stated both as the recurrence value and as `Fintype.card (PaperDiary n)`. Both normalization inputs of `DegreeAssembly` are instantiated with the proved extraction and uniqueness theorems. |

The final chain theorem is a genuine least-degree statement, not just an
upper bound. Its upper bound canonizes all finitely many diary types and
uses sparse extraction to cover every chain in the resulting copy. Its
lower bound colours chains by their unique extracted diary. Every ambient
self-copy, after composition with the fixed sparse embedding, contains a
realization of every diary. Functional factorization transfers these
realizations back to the original self-copy, so any bounding palette must
contain all diary colours. `paperDiary_card` then gives the exact numerical
bound.

The copy/embedding convention is checked where it matters. A finite chain
has no nontrivial order automorphism, and
`chain_embedding_eq_of_range_eq` proves that its embedding is determined by
its image. For structures with incomparable points, which need not be rigid,
the negative colouring is separately proved invariant under equal ranges.
`RepoBridge.bound_iff` compares two embedding APIs; it does not assert an
unjustified general equality between copy and embedding degrees for
nonrigid structures.

The concrete negative theorem's palette estimate uses `|A|²` instead of the
manuscript's sharper `binom(|A|,2)`. The weaker finite bound suffices: for a
proposed degree `d`, use modulus `m=d|A|²+1`. Every residue appears on an
incomparable pair in every self-copy, each pair extends to an `A`-copy, and
each copy's colour is a set of at most `|A|²` residues. At most `d` such colours
could cover at most `d|A|²` residues, a contradiction. The witness colouring is
fixed before the self-copy is chosen.

## Why mathlib helps

The useful interfaces are the actual functional-language structures and
embeddings, substructure closure, finite generation, finite partial
equivalences/back-and-forth, ultrahomogeneity and Fraïssé-limit uniqueness.
`Order.iso_of_countable_dense` handles identification of the binary ray with
the rationals and of the interval suborders used in lower realization, once
their order laws and density are proved. See
[the detailed mathlib audit](Pseudotree-Mathlib.md) for exact declarations and
pinned source links.

At the pinned revision, general existence of Fraïssé limits is still listed
as TODO. This does not block the present proof: the concrete model is built
directly, its finite-extension property is proved, and mathlib's back-and-forth
and uniqueness theorems finish the identification.

A useful proof reduction emerged during this formalization. To extend from a
meet-closed subset `S` of a finite meet-tree, choose a minimal point `b`
outside `S`. For every `a∈S`, the meet `a∧b` is either `b` or is strictly
below `b` and hence already in `S`. Therefore `S∪{b}` is meet-closed. Induction
reduces arbitrary finite extension to the four explicit one-point cases.

## Reproducing validation

The outer package remains Lean/Std only. Run from the repository root:

```sh
lake build
lake env lean Checks.lean
lake env lean ChecksFullTypes.lean
lake env lean PartialTypesChecks.lean
lake env lean PseudotreeChecks.lean
```

The optional package uses the same Lean version, `v4.35.0-rc3`, and pins:

| Dependency | Commit |
| --- | --- |
| `lean-milliken` | `8bd32d6d607590319e5710cc0206c76ed8079b0d` |
| mathlib | `5bd58ac291422a21f412ae354c91e7d172255a2c` |
| `lean-ramsey-space-todorcevic` | `bb29d1f3f36ff37a35857247ca9fae581fa1fa43` |
| `lean-successors` | `1d3a69015c21315c4a0161c3ce38889d4dd5d68a` |

From `validation/pseudotree`:

```sh
lake update
lake exe cache get
# Optional memory-saving import changes: follow import-patches/README.md.
LEAN_NUM_THREADS=2 lake build PseudotreeValidation
lake env lean Checks.lean
```

For the complete exact chain theorem and its dependency closure alone, run:

```sh
lake build PseudotreeValidation.ChainDegrees
```

The final module imports `DegreeAssembly`, `SparseExtraction` and
`DiaryRecovery`. It instantiates `exact_degree_of_representations` with
`SparseExtraction.sparse_copy_representation` and
`DiaryRecovery.embeddedChain_unique`. The assembly module already uses
the actual simultaneous canonization and lower realization proofs;
these are not additional arguments required from the caller of
`chain_degree`.

The local validated build used the documented import-only patches in
`validation/pseudotree/import-patches/`. Two blanket `import Mathlib`
statements are narrowed and a previously implicit `Mathlib.Order.Sigma`
import is made explicit. Three upstream source files change; every theorem
statement, definition and proof body is unchanged. The supplied patches and
hash record make this difference inspectable. Dependency pins and original
upstream checkouts are not rewritten. The optional CI workflow applies this
same import-only variant.

The two new check files print important endpoint dependencies and inspect
the transitive axiom dependencies of every declaration in the pseudotree
namespace. The permitted set is exactly `propext`, `Classical.choice`, and
`Quot.sound`. No `sorryAx`, custom mathematical axiom, or native-decision
axiom is permitted. Source builds, not merely the existence of theorem names,
are the validation criterion.

The completed verification is recorded in
`validation/pseudotree/verification/`:

| Check | Result | Record |
| --- | --- | --- |
| Root package build and three existing check files | All passed | `root-results.json` and the corresponding root logs |
| Root pseudotree axiom audit | 1,304 declarations; only the three permitted standard axioms | `root-pseudotree-axioms.txt` |
| Full optional package build | Passed, 3,457 jobs | `optional-build.txt` |
| Optional pseudotree axiom audit | 3,160 declarations; only the three permitted standard axioms | `optional-axioms.txt` |
| Exact chain-degree endpoints | Both recurrence and raw-diary-cardinality statements use only the three permitted standard axioms | Explicit `chain_degree` and `chain_degree_diaries` entries in `optional-axioms.txt` |

## Independent finite checks

`validation/pseudotree/scripts/check_sparse.py` independently constructs the
first 50 sparse coding nodes and checks the diary extraction and all
ray-preserving edges for every chain of size at most four among them: 16,581
chains in total. It also computes the event recurrence.

`validation/pseudotree/scripts/enumerate_diaries.py` independently enumerates
literal legal event executions for sizes one through four. It finds
`1, 7, 157, 7927` different coding sets, with maximal heights `1, 5, 9, 13`.
The ordinary Lean kernel additionally checks the first five event-grammar
counts `1, 7, 157, 7927, 727741`, without `native_decide`.

These checks were useful for testing the normalization rules and for finding
the false lexicographic assertion. They are independent finite evidence. The
general canonization, unavoidability and exact big Ramsey degree statements
are supplied by the Lean proofs, not inferred from these searches.

## Final coverage and remaining model scope

All three formerly outstanding parts of the binary chain proof are now
closed: restricted finite-tree canonization; identification and diary
extraction for the actual sparse construction; and every-copy realization
with exact recovery of the realized type. The complete theorem
`chain_degree` has no parameters asserting any of those conclusions. Its
only mathematical inputs are the chain size and its positivity.

Together with `RepoBridge.incomparable_degree_infinite`, this establishes the
two cases of the manuscript's classification for nonempty finite
substructures of the concrete Ψ₂ model: finite chains have the exact diary
degree, and a finite structure containing an incomparable pair has no finite
degree. The separate `RepoBridge.singleton_degree` agrees with the `n = 1`
case of the general theorem.

For Ψω, `GenericIncomparables.no_finite_bound_of_countable` proves the result
under explicit structural hypotheses: countability, a nonempty dense
meet-semilattice with no maximal element, comparable predecessor sets, an
opposite branch above every point, compatible interpretation of order and
meet, and ultrahomogeneity. No profile-isolation or oscillation conclusion is
assumed. These hypotheses express the needed properties of Ψω, but a
concrete countably branching carrier, its age and its Fraïssé identification
have not been separately instantiated in this repository. The report
therefore distinguishes the full concrete Ψ₂ validation from this general
structural theorem.

## Primary mathematical sources checked

- [Chodounský–Dobrinen–Weinert, version 4](https://arxiv.org/html/2503.22626v4),
  especially Theorem 1.8, Definition 3.3 and Theorem 5.3.
- [Chodounský–Eskew–Weinert, version 2](https://arxiv.org/html/2503.18727v2),
  especially the oscillation/incomparable result, Theorem 10.
- [Todorčević, *Introduction to Ramsey Spaces*](https://www.cs.umd.edu/~gasarch/COURSES/752/S26/BOOKS/IntroRamseySpaces.pdf),
  Theorem 3.2 and its proof, and Lemma 6.35.
- [Pinned `lean-milliken` source](https://github.com/janhubicka/lean-milliken/tree/8bd32d6d607590319e5710cc0206c76ed8079b0d).
- [Pinned mathlib source](https://github.com/leanprover-community/mathlib4/tree/5bd58ac291422a21f412ae354c91e7d172255a2c).
