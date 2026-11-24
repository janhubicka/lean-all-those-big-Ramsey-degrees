# Pseudotree validation: mathlib reuse audit

Audited on 2026-11-24 against mathlib commit
`5bd58ac291422a21f412ae354c91e7d172255a2c`, pinned by the existing `lean-milliken`
project. The outer package remains independent of mathlib; the optional
`validation/pseudotree` package uses its already compatible Lean 4.35.0-rc3
and mathlib toolchain.

## Directly useful existing interfaces

| Manuscript need | Existing mathlib interface | What remains specific to this paper |
| --- | --- | --- |
| Structures in the language `{≤, ∧}` | `FirstOrder.Language`, `Language.Structure`, `Language.Embedding` in `Mathlib/ModelTheory/Basic.lean` | Define the binary order relation and binary meet function, and interpret them on the concrete model. |
| Actual meet-closed substructures | `Language.Substructure`, `.closure`, `.map`, `Embedding.equivRange` in `Mathlib/ModelTheory/Substructures.lean` | Prove that being closed under the one function symbol is exactly meet closure. The new adapter does this. |
| Extending the incomparable triple to a prescribed finite pattern | `IsUltrahomogeneous.extend_embedding` in `Mathlib/ModelTheory/Fraisse.lean` | Supply the triple embedding, finite generation, an embedding of the larger pattern, and ultrahomogeneity of the ambient pseudotree. |
| Back-and-forth from finite extension data | `Language.IsExtensionPair`, `Language.equiv_between_cg` in `Mathlib/ModelTheory/PartialEquiv.lean`; `isUltrahomogeneous_iff_IsExtensionPair` in `Fraisse.lean` | Prove the pseudotree's extension cases and the connection between finite and finitely generated substructures. |
| Identifying two already established limits | `IsFraisseLimit.nonempty_equiv` in `Fraisse.lean` | Establish the two `IsFraisseLimit` hypotheses; the theorem does not establish them automatically. |
| Rationality of a countable dense ray without endpoints | `Order.iso_of_countable_dense` in `Mathlib/Order/CountableDenseLinearOrder.lean` | Prove countability, density and absence of endpoints for the binary-word order or for the sparse ray being used. |
| Dense linear orders as Fraïssé limits | `Language.order.isFraisseLimit_of_countable_nonempty_dlo` in `Mathlib/ModelTheory/Order.lean` | Useful for the rays, not a theorem about meet-trees or their finite diagrams. |

### Important limits of the existing Fraïssé module

At the pinned revision, `Mathlib/ModelTheory/Fraisse.lean` explicitly lists
**“Show existence of Fraïssé limits”** under TODO. It defines Fraïssé classes and
limits and proves substantial age, extension, and uniqueness theorems. It does
not supply a general theorem constructing a limit from the Fraïssé class
axioms.

Moreover, mathlib's `age` is defined using **finitely generated** structures.
The manuscript uses finite meet-closed structures. In a meet-tree these notions
are compatible because a finite set has finite meet closure, but that lemma
must be supplied. `Structure.fg_iff_finite` in `FinitelyGenerated.lean` assumes
`L.IsRelational`; it cannot be used directly for the manuscript's language,
which contains a binary function.

No pseudotree-specific model or chain-diary theorem was found in the inspected
model-theory files. The generic tools remove common infrastructure work; they
do not replace the sparse-copy construction, diary normalization,
unavoidability, or ray-preserving Ramsey theorem.

## Checked model code added in this audit

`AllThoseBigRamsey/Pseudotree/Model.lean` gives a generic block representation
`RayTree α`, corresponding to splitting a ternary word at occurrences of `1`.
It proves, with explicit hypotheses on the ray order:

- reflexivity, antisymmetry and transitivity of the manuscript's block order;
- linear comparability of all predecessors of any one node;
- both lower-bound properties and the greatest-lower-bound property of the
  explicit meet formula;
- no least point when rays have no least point, and no greatest point;
- density of comparable intervals when rays are dense and have no least point;
- injectivity, order preservation/reflection and meet preservation for maps
  induced by embeddings of the ray order.

The optional `PseudotreeValidation/ModelMathlib.lean` uses these proofs to
install standard `PartialOrder`, `SemilatticeInf`, `NoMinOrder`, `NoMaxOrder`,
and `DenselyOrdered` instances. It defines the actual language `{≤, ∧}`, proves
both directions of the correspondence between meet-closed sets and
substructures, constructs functional embeddings induced by ray-order
embeddings, and connects the construction with the standard model-theoretic
interfaces.

The rest of the concrete model identification is now checked as well:

| File | Checked content |
| --- | --- |
| `AllThoseBigRamsey/Pseudotree/Words.lean` | The binary-word order is linear, dense and has no endpoints. Splitting and rejoining literal ternary words are inverse operations. The literal-word meet is their greatest lower bound. |
| `PseudotreeValidation/WordModelMathlib.lean` | `BinaryRay` has standard countable dense linear order instances; it is order-isomorphic to the rationals. `wordEquiv` identifies all literal ternary words with `RayTree BinaryRay`, preserving order and meet. |
| `PseudotreeValidation/Cones.lean` | A Boolean cone code characterizes when two strict successors have meet above the base point. Both codes occur, and there are exactly two upward cones. |
| `PseudotreeValidation/Closure.lean` | In a meet-tree, the closure of a set is exactly its set of pairwise meets. Finite sets have finite closure, and finitely generated substructures are finite. |
| `PseudotreeValidation/Insertions.lean` | Fresh insertion below a finite diagram, inside an empty old interval, above a maximal point, and into an unused cone, with the required meet equations. |
| `PseudotreeValidation/FiniteExtensions.lean` | Complete classification of admissible one-point extensions; extension of embeddings across arbitrary finite diagrams; universality for finite binary meet-trees; actual ultrahomogeneity by mathlib back-and-forth. |
| `PseudotreeValidation/FraisseModel.lean` | An intrinsic class of finite binary meet-trees, exact age equality, the native `IsFraisseLimit` theorem, Fraïssé class axioms as a consequence, and uniqueness up to a functional structure isomorphism. |
| `AllThoseBigRamsey/Pseudotree/SparseFair.lean` | Exact FIFO fairness with binary tails, including explicit selection times for all three children of each coding node. |
| `AllThoseBigRamsey/Pseudotree/SparseOrder.lean` | Both comparisons with an older word are unchanged by a binary tail beyond its end; the actual generated set is dense, has no endpoints and has two inhabited upper cones. |
| `PseudotreeValidation/GenericFiniteExtensions.lean` | The four target insertion cases and finite-extension/back-and-forth argument for any dense meet-tree without endpoints and with an inhabited opposite cone. |
| `PseudotreeValidation/SparseModel.lean` | The precise generated sparse set is a Fraïssé limit of `finiteBinaryClass`, isomorphic to the full model, and the exact range of a functional self-embedding. |

### Exact model-theoretic endpoints

`finiteBinaryClass` is defined independently of the coding model. A bundled
structure belongs to it precisely when it is finite and admits a compatible
meet-semilattice interpretation with linearly ordered predecessor sets and
at most two upward cones. Compatibility means that the actual language
symbols interpret the specified order and meet; it is not an extra structural
axiom about the model. `MeetsInterpreted` provides that interface for both the
canonical structures and mathlib's induced substructure instances.

The following signatures are Lean-checked (within
`AllThoseBigRamsey.Pseudotree`):

```lean
theorem RayTree.isFraisseLimit
    {α : Type u} [LinearOrder α] [NoMinOrder α] [NoMaxOrder α]
    [DenselyOrdered α] [Nonempty α] [Countable α] :
    language.IsFraisseLimit finiteBinaryClass (RayTree α)

theorem ternaryModel_isFraisseLimit :
    language.IsFraisseLimit finiteBinaryClass TernaryModel

theorem finiteBinaryClass_isFraisse :
    FirstOrder.Language.IsFraisse finiteBinaryClass.{0}

theorem ternaryModel_unique
    {M : Type} [language.Structure M] [Countable M]
    (hM : language.IsFraisseLimit finiteBinaryClass M) :
    Nonempty (TernaryModel ≃[language] M)
```

Here `TernaryModel` is `RayTree BinaryRay`. The checked equalities
`fromBlocks_toBlocks`, `toBlocks_fromBlocks`, `wordBelow_iff_toBlocks_le`, and
`toBlocks_wordMeet` connect this endpoint to the literal words and order in
the manuscript. Thus the model is not merely assumed to be the desired
pseudotree: the age and back-and-forth proofs establish the identification.

The finite-extension proof also exposes a useful simplification for the
English proof. Given a finite meet-tree and a meet-closed old substructure,
choose a minimal omitted point `b`. For every old `a`, either `b ∧ a` is old
or minimality forces `b ∧ a = b`. Hence adjoining `b` preserves meet closure.
Induction on the number of omitted points reduces arbitrary finite
extensions to the four checked one-point cases.

### Verification and proof dependencies

From the optional package, the targeted command

```sh
lake build PseudotreeValidation.FraisseModel
```

completed successfully on 2026-11-24 using the pinned toolchain. It checks the
entire model dependency chain above. `#print axioms` for
`RayTree.age_eq_finiteBinaryClass`, `RayTree.isUltrahomogeneous`,
`RayTree.isFraisseLimit`, `ternaryModel_isFraisseLimit`,
`ternaryModel_unique`, `finite_universal`, `extend_finite`,
`extend_finite_substructure`, `BinaryRay.nonempty_orderIso_rat`,
`closure_eq_pairwise_meets`, and `ternaryModel_two_cones` reports only
`propext`, `Classical.choice`, and `Quot.sound`. The direct word-meet transport
theorem `toBlocks_wordMeet` uses `propext` and `Quot.sound`. None uses
`sorryAx` or an added pseudotree, extension, or Fraïssé-existence axiom.

### Identification of the actual sparse construction

The sparse model is the literal subtype

```lean
abbrev SparseModel :=
  {s : TernaryModel // Sparse.InSparse (fromBlocks s)}
```

`Sparse.InSparse` is already proved equal to the range of the explicit FIFO
sequence `Sparse.code`; its meet closure is established from the origin of
each `1` in the generated words. The new geometric proof does not replace
this carrier by an abstract homogeneous structure.

The proof of density can be shortened substantially. A queued word acquires
only binary letters before being selected. If an older coding word is shorter
than the currently selected slot, appending any binary tail to that slot
changes neither comparison with the older code. The children `u000` and
`u222` therefore produce points strictly above and below `u02`, respectively,
with exactly its comparison profile relative to every older code. Between
two comparable codes, use the appropriate child of the later-generated
endpoint. The middle child `u021` and the upper child `u000` have meet `u02`,
so they inhabit both upper cones. This verifies density, no endpoints and
branching directly, without a separate invariant describing every open
interval in the frontier.

The generic finite-extension argument then proves the native statements:

```lean
theorem SparseModel.isFraisseLimit :
    language.IsFraisseLimit finiteBinaryClass SparseModel

theorem SparseModel.nonempty_equiv :
    Nonempty (TernaryModel ≃[language] SparseModel)

noncomputable def SparseModel.selfEmbedding :
    TernaryModel ↪[language] TernaryModel

theorem SparseModel.selfEmbedding_range :
    Set.range SparseModel.selfEmbedding =
      {s | Sparse.InSparse (fromBlocks s)}
```

`lake build PseudotreeValidation.SparseModel` completed successfully with
1,191 dependency jobs. The sparse Fraïssé theorem, isomorphism and exact-range
theorem use only `propext`, `Classical.choice` and `Quot.sound`. In particular,
the target's extension property, homogeneity and isomorphism are conclusions;
none is an assumption about the sparse construction.

### Scope beyond the model theorem

This closes the concrete model identification, the rational-ray facts, the
two-cone calculation, finite meet closure, the finite-extension and
ultrahomogeneity arguments, and the full identification of the actual sparse
copy. Separate optional modules now also prove the full mixed ray-preserving
product theorem, including stabilization, dense matrices, infinite boundary
grafting and fusion; its endpoint is `Mixed.mixed_product` with only a finite
colouring as input.

The subsequent validation now supplies the paper-specific ingredients as
well. `RayMilliken.restricted_milliken` and
`DiaryCanonization.simultaneous_total` prove the restricted finite-tree
canonization theorem and its simultaneous application to all raw diaries.
`SparseExtraction.sparse_copy_representation` extracts a literal diary from
every nonempty finite chain in the generated sparse copy.
`LowerRealization.sparse_self_copy_realization` realizes every raw diary in
every functional self-copy of that sparse model. These are proved from their
actual geometric and finite-tree hypotheses, without assuming a desired
canonization, extraction or realization conclusion.

The lower-bound geometry is usefully independent of diary enumeration.
`LowerGeometry` first finds a nonempty interval contained in one ambient ray
by choosing a maximal ray depth between its endpoints. Its induced countable
dense order is identified with the rationals using mathlib. A finite-prefix
pigeonhole argument gives a rational suborder whose words share an
arbitrarily long prefix; choosing two distinct points of the same prefix
colour automatically rules out a short prefix. `LowerSplit` and `LowerTurn`
provide the two branching operations. The latter works inside an arbitrary
functional self-copy, using meet preservation and the two inhabited cones;
the self-copy is not assumed to preserve the word coordinates. The four raw
level rules are then handled by `LowerStep` and `LowerTransition`, and
`LowerAssembly` completes the resulting finite ray map to a total map.

Recovery is expressed by a simpler invariant than a second bespoke
induction over compression levels. `DiaryNormalization` defines the retained
coordinates directly: coding endpoints, first disagreements, and the first
required `1` after a binary essential level. `DiaryRecoveryNaturality` proves
that the normalized coding set is unchanged by every ray-preserving strong
map. `DiaryRecovery.codes_source` proves that normalizing an already
canonical raw diary gives its original coding set, with no sparsity
hypothesis. Every nonturn level is an essential endpoint or fork. A turn
immediately follows a split or leaf, whose frontier has no outgoing `1`,
while its own `1`-child has a coding descendant below the actual chain
maximum. Thus every original level is retained.
`DiaryRecovery.coding_image_unique` and `embeddedChain_unique` then prove
uniqueness of the realized diary type, including equality of actual
functional-chain embeddings.

The final assembly is complete. `PseudotreeValidation/ChainDegrees.lean`
instantiates the proved degree assembly with the actual sparse extraction
and recovery endpoints. In namespace `AllThoseBigRamsey.Pseudotree`, it
proves the manuscript's exact positive-chain theorem directly in the
repository's original API:

```lean
theorem chain_degree_diaries (n : Nat) (hn : 0 < n) :
    IsBigRamseyDegree (RepoBridge.model (Fin n))
      (RepoBridge.model TernaryModel)
      (some (Fintype.card (PaperDiary n)))
```

`chain_degree` states the same result with `diaryCount true n 1` as the bound;
`paperDiary_card` proves these values equal for every size. The endpoint has
no assumed normalization, canonization or unavoidability premise. The final
optional build completed with 3,457 jobs, and its axiom audit checked all
3,160 pseudotree declarations. Both exact-degree endpoints use only
`propext`, `Classical.choice` and `Quot.sound`. Logs are retained in
`validation/pseudotree/verification/`.

The separate `RepoBridge.incomparable_degree_infinite` establishes the other
case for actual finite substructures of this concrete model. The general
incomparable theorem is also proved for countable dense homogeneous
meet-trees satisfying the stated second-branch property, but no separately
constructed and identified concrete Ψω carrier is supplied. This limitation
does not affect the completed concrete Ψ₂ classification.

## English proof audit relevant to the model

A genuine local error occurs in the original sparse-copy proof: the maximum
of a chain is claimed to be its lexicographically least element. This fails
when another coding node is its proper prefix. For example the sparse queue
produces `x₀ = 02` and `x₂ = 02122202`, and their two-element chain has maximum
`x₂` although ordinary lexicographic order puts `x₀` first. The required and
correct statement is that every chain member is either a prefix of its
maximum or is prefix-incomparable with and lexicographically larger than that
maximum. Thus the maximum determines the leftmost branch of the prefix
closure. The later compression proof uses this weaker, correct statement.

The assigned audit found no structural error in the subsequent lower-bound
construction. In particular, an interval below a fixed word meets only finitely
many rays, each convexly; its reduction to a rational subset of one ray is
valid. In a type-(c) or type-(d) step, meet closure makes the two cones in a
subcopy map into distinct ambient cones, justifying passage into the `v1`
cone.

The diary definition admits the explicit height bound `h ≤ 4n − 3` for `n ≥ 1`.
If `a,b,c,d` count the four event types, then `a = b − 1`, `b + c = n`, and
`d ≤ a + b − 1`. The last inequality pairs each type-(d) event with its
preceding split or terminal event and excludes the final terminal event.
This replaces a vague finiteness argument with a direct bound.

Independent finite checks of the sparse construction and diary extraction
found no failure on the 16,581 chains of sizes one to four among its first 50
points. Independent direct enumeration of the four event types gives
`1, 7, 157, 7927` diaries, with maximal heights `1, 5, 9, 13`. These are
computational checks, not proofs of the infinite Ramsey statements.

## Pinned source links

- [Fraïssé classes and limits](https://github.com/leanprover-community/mathlib4/blob/5bd58ac291422a21f412ae354c91e7d172255a2c/Mathlib/ModelTheory/Fraisse.lean)
- [Substructures](https://github.com/leanprover-community/mathlib4/blob/5bd58ac291422a21f412ae354c91e7d172255a2c/Mathlib/ModelTheory/Substructures.lean)
- [Partial equivalences and back-and-forth](https://github.com/leanprover-community/mathlib4/blob/5bd58ac291422a21f412ae354c91e7d172255a2c/Mathlib/ModelTheory/PartialEquiv.lean)
- [Countable dense linear orders](https://github.com/leanprover-community/mathlib4/blob/5bd58ac291422a21f412ae354c91e7d172255a2c/Mathlib/Order/CountableDenseLinearOrder.lean)
- [First-order order theories](https://github.com/leanprover-community/mathlib4/blob/5bd58ac291422a21f412ae354c91e7d172255a2c/Mathlib/ModelTheory/Order.lean)
- [Finite generation](https://github.com/leanprover-community/mathlib4/blob/5bd58ac291422a21f412ae354c91e7d172255a2c/Mathlib/ModelTheory/FinitelyGenerated.lean)
