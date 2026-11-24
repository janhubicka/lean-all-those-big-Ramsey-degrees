# Pseudotree validation with mathlib and lean-milliken

This optional package extends the Lean/Std core in the parent repository.
It proves the paper's exact big Ramsey degrees for every nonempty finite
chain in the concrete pseudotree, together with the infinite-degree theorem
for every finite substructure containing incomparable points. The concrete
model is proved to be the Fraïssé limit of finite binary meet-trees.

The development uses actual first-order structures in the language `{≤, ∧}`,
and actual proved Halpern–Läuchli theorems from `janhubicka/lean-milliken`.
The final degree statements use the parent repository's existing
`IsBigRamseyDegree` definition, via a proved equivalence with the relational
language that records both order and the graph of meet.

## Exact chain-degree endpoint

The following theorem is compiled without an extraction, realization,
canonization, or uniqueness hypothesis:

```lean
theorem chain_degree (n : Nat) (hn : 0 < n) :
    IsBigRamseyDegree
      (RepoBridge.model (Fin n))
      (RepoBridge.model TernaryModel)
      (some (diaryCount true n 1))
```

`chain_degree_diaries` gives the same exact degree as
`Fintype.card (PaperDiary n)`. The equality `paperDiary_card` proves that the
recurrence counts the manuscript's independently specified finite sets of
nodes and coding nodes. The first
five values are proved by `diaryCount_first_five`:

| Chain size | 1 | 2 | 3 | 4 | 5 |
| --- | ---: | ---: | ---: | ---: | ---: |
| Exact degree | 1 | 7 | 157 | 7,927 | 727,741 |

## Main proved interfaces

The main endpoints are:

- `ternaryModel_isFraisseLimit`: the explicit block/ternary-word model is the
  limit of the independently defined class of finite binary meet-trees.
- `Incomparables.arbitrarily_many_copy_colours`: a finite image-invariant
  colouring defeats every proposed finite degree for a finite structure in
  the model's age containing incomparable points.
- `GenericIncomparables.no_finite_bound_of_countable`: the same negative
  conclusion for countable dense homogeneous meet-trees with a second branch,
  stated using ordinary structural hypotheses.
- `WordTrees.rayConeDenseMatrices`: finite-colour dense-matrix HL for arbitrary
  finite demands in the manuscript's actual binary rays and ternary cones.
- `RayMapModel.embedding`: a ray-preserving strong map induces an actual
  functional-language self-embedding of the ternary model.
- `Mixed.mixed_product`: for any finite colouring of a product with any finite
  number of binary factors and one ternary factor, there are actual synchronized
  strong maps, ray-preserving on the ternary factor, making every selected level
  product monochromatic. Stabilization and both fusion constructions are proved.
- `Mixed.mixed_level_product`: the same theorem for a colouring whose domain is
  precisely the actual level product.
- `paperDiary_card`: the recurrence counts the independent raw finite-set diary
  definition; both directions of the grammar correspondence are proved.
- `RayMilliken.restricted_milliken`: the full finite-prefix-tree theorem, with
  at most one incoming `1` per level and no assumed canonization principle.
- `DiaryCanonization.simultaneous`: one common ray map canonizes the actual
  chain copies represented by all size-`n` literal diaries.
- `SparseModel.nonempty_equiv` and `selfEmbedding_range`: the generated sparse
  set is isomorphic to the full model and is exactly the range of a self-copy.
- `SparseExtraction.sparse_copy_representation`: every actual nonempty finite
  chain in that copy has a literal-diary representation by a finite ray map.
- `LowerRealization.sparse_chain_realization`: every diary has an actual ray
  realization in every self-copy contained in the sparse set.
- `DiaryRecovery.codes_image`: the explicit normalized coding set is invariant
  under every ray-preserving map, for an arbitrary finite coding set and
  distinguished word.
- `DiaryRecovery.codes_source`, `image_recovery`, and `embeddedChain_unique`:
  normalization is the identity on raw diaries and recovers the unique diary
  from any actual finite ray realization of its chain.
- `chain_upper_bound`, `chain_degree`, and `chain_degree_diaries`: the complete
  upper bound and exact minimal degree for every positive chain size, stated
  both by recurrence and as the raw diary cardinality in the repository's
  existing API.
- `RepoBridge.incomparable_degree_infinite` and `singleton_degree`: the negative
  theorem and the exact singleton degree, in that same API.

All names have prefix `AllThoseBigRamsey.Pseudotree`.
See [the audit](../../docs/Pseudotree-Audit.md) for the theorem-to-manuscript
correspondence, the corrections to the supplied text, and proof simplifications.

The generic incomparable theorem is also proved for any countable dense
homogeneous meet-tree satisfying its explicit branching assumptions. This
covers the intended infinitely branching pseudotree mathematically, but this
package does not construct a separately named `Ψω` model. The exact chain
endpoint above concerns the fully identified binary-branching model `Ψ₂`.

## Build

From this directory:

```sh
lake update
lake exe cache get
LEAN_NUM_THREADS=2 lake build PseudotreeValidation
lake env lean Checks.lean
```

The local validation used the optional
[import-only dependency patches](import-patches/README.md), which reduce the
memory cost of blanket `Mathlib` imports without changing any definition,
theorem or proof. Apply them after fetching dependencies and before the build
to reproduce that run. The CI workflow uses the same variant. Exact dependency
commits are recorded in `lake-manifest.json`; the compiler is Lean 4.35.0-rc3.

`Checks.lean` prints the upstream Ramsey theorem dependencies and major local
endpoints, and then audits all declarations in the pseudotree namespace
transitively. Its allowlist is `propext`, `Classical.choice`, and `Quot.sound`.

## Additional finite checks

```sh
python3 scripts/check_sparse.py
python3 scripts/enumerate_diaries.py
```

These independent finite calculations complement the Lean proofs. They do not
establish any infinite Ramsey statement.
