# Poset-diaries and fat trees — Lean validation

Dedicated branch `poset-diaries-fat-trees` of All those big Ramsey degrees.
The source is [poset-diaries-fat-trees.tex](https://github.com/janhubicka/All-those-big-Ramsey-degrees/blob/main/poset-diaries-fat-trees.tex), initially audited at `43c862790a9cea38717f1e59fa4230b325a1a19e`. All older source files remain in Git, but this branch's Lake target and CI are isolated.

## Build and review

Use Lean `v4.35.0-rc3`. Run `lake update` on a fresh checkout without a lockfile, `lake exe cache get`, then `lake build PosetDiariesFatTrees`.
The audit file also imports the relevant external theorem modules; first build those imports, e.g.
`lake build +SuccessorTree.ShapeFiniteRamsey +SuccessorTree.FatTree.BorelImage +RamseySpace.AbstractEllentuck +Mathlib.ModelTheory.Order`, then run `lake env lean PosetDiariesChecks.lean`.
CI uses a single job and cached mathlib; do not push per lemma. See [validation ledger](POSET-VALIDATION.md) for individual obligations, percentages and dependency risks.

## Interface index

| Module | Interface |
|---|---|
| `PosetDiariesFatTrees.WordDistance` | `Letter`, `LevelWord`, `delta`, `delta_self`, `delta_triangle`, `delta_zero_iff`, `Nonexpansive` |
| `PosetDiariesFatTrees.BoringExtension` | `extensionNat`, `extensionNat_agrees`, `extensionNat_nonexpansive`, `exists_nonexpansive_extension` |
| `PosetDiariesChecks.lean` | source and upstream declaration dependency audit |
| Planned WordOrder / Diaries | prefix, word partial order, compatibility, diary events, shape deletion |
| Planned RootedMonoid / Synchronisation | concrete `STree`, `SMTree`, lifting and rooted synchronisation |
| Planned TypeComplete / RootedAmalgamation | finite types, existence and hereditary completeness, bounding words |
| Planned CopySpace / Ramsey | concrete approximations, A1–A4, closedness, finite/Borel and Ellentuck endpoints |

## Reused libraries (pinned)

* mathlib `5bd58ac291422a21f412ae354c91e7d172255a2c`: `Mathlib.ModelTheory.Order`, `Fraisse`, `Basic`, `PartialEquiv`; use order embeddings for combinatorial posets, connect them to `Language.order` for age/homogeneity. No duplicate first-order language API.
* lean-successors `3f5cbbb7342ba884420199737c431d57e0748df8`: `LevelTree`, `STree`, `ShapeMap`, `SMTree`; `shapePreservingRamsey`, `FatTree.associatedMap_ofShapeMap`, `fatImageHomogeneous_of_BaireFibres`. The last needs the concrete Borel-to-Baire pullback.
* lean-ramsey-space-todorcevic `bb29d1f3f36ff37a35857247ca9fae581fa1fa43`: same revision as the successor dependency; `ApproximationSystem`, `Finitization`, `AbstractRamseySpace.ofPublishedAxioms`, `abstractEllentuck_textbook`.

Only exact-statement, successful kernel-checked and dependency-audited results receive a verified manuscript marker. A relative proof explicitly lists its premises. Initial code is implemented but has not yet been built; no local verification is claimed.
