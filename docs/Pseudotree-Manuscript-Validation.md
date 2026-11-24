# Manuscript validation markers

The revised pseudotree manuscript uses the EPPA III convention: a small green
**Lean ✓** links to a checked statement, and green **Lean rel.** links to a
checked general statement whose application requires the stated model
identification. Links are pinned to a public commit, rather than to `main`.
The TeX controls allow margin, inline, and marker-free output. The manuscript
itself is maintained separately from this repository.

## Statement map

Here `V/` abbreviates `validation/pseudotree/PseudotreeValidation/` and `S/`
abbreviates `AllThoseBigRamsey/Pseudotree/`. Paths and declaration names identify
the proofs independently of typeset numbering.

| Manuscript label | Status | Lean statements |
| --- | --- | --- |
| `lem:osc` | Verified | `V/FiniteOscillation.lean`: `FiniteOscillation.all_oscillations` |
| `thm:HL` | Verified, both clauses | `V/HeterogeneousMatrices.lean`: `heterogeneousFiniteDemandDenseMatrices`; `V/HeterogeneousStrongMaps.lean`: `WordTrees.rootedHeterogeneousWordStrongMapsHL` |
| `thm:incomp` | Relative for the combined binary/countably branching statement | `V/GenericIncomparables.lean`: `GenericIncomparables.no_finite_bound_of_countable`; the fully instantiated binary case is `V/RepoBridge.lean`: `RepoBridge.incomparable_degree_infinite` |
| `lem:ternary-model` | Verified | `V/FraisseModel.lean`: `ternaryModel_isFraisseLimit`, `ternaryModel_unique`; `S/WordLex.lean`: `wordBelow_prefix_incomparable_lex` |
| `lem:extend` | Verified, all three clauses | `V/RayMapEmbedding.lean`: `RayMapModel.embedding`; `S/RayEmbeddings.lean`: composition, normalized fusion and `fusion_factors`; `S/RayGrafting.lean`: `finite_boundary_grafting`; `S/RayExtension.lean`: `finite_completion` |
| `lem:mixed` | Verified | `V/MixedProduct.lean`: `Mixed.mixed_level_product` |
| `rem:sharp` | Verified counterexample | `S/RayObstruction.lean`: `RayEmbeddings.two_ternary_obstruction` |
| `lem:milliken` | Verified | `V/RayMilliken.lean`: `RayMilliken.restricted_milliken`; `V/RayMillikenBase.lean`: `local_iff_realizable` |
| `lem:sparse` | Verified | `V/SparseModel.lean`: `isFraisseLimit`, `selfEmbedding_range`; `V/SparseExtraction.lean`: `sparse_copy_representation` |
| `thm:exact` | Verified for every positive size | `V/ChainDegrees.lean`: `chain_degree_diaries` |
| `prop:count` | Verified recurrence, cardinality and values | `V/DiarySoundness.lean`: `paperDiary_card`; `S/DiaryCounts.lean`: `diaryCount_closed`, `diaryCount_open`, `diaryCount_first_five` |

The manuscript also links the universal one-prefix implication to
`V/SparseChainGeometry.lean`, `Sparse.wordBelow_one_prefix`, and the fact that
the coding set determines the diary to `V/DiaryRecoveryMaximum.lean`,
`PaperDiary.codes_ext`. Bare definitions are not labelled as proof results.

## Exact scope

The oscillation lemma now assumes arbitrary proper end-extensions directly.
Its former topological reformulation is not needed by the proof. The
preliminary fusion paragraph now uses the normalized rule that stage `j`
fixes all words of length less than `j`; this is precisely the protection
rule in the ray-map fusion theorem.

The Halpern–Läuchli dense-matrix theorem covers independent arbitrary finitely
branching rooted trees, and the word-map corollary preserves letters. The
finite-tree ray theorem includes a proved equivalence between local finite
embedding data and realizability; no extension hypothesis is left unproved.
The sparse-copy theorem concerns the actual generated FIFO set. The exact
degree endpoint uses the repository's original degree API and the cardinality
of independently specified raw diaries.

All binary pseudotree results are instantiated for the concrete ternary
model, with its Fraïssé identification proved. For the countably branching
pseudotree, the checked theorem assumes the structural properties of a
countable dense homogeneous meet-tree with the required second-branch
property. A separate concrete model and its identification with Ψω are not
formalized. This is why the combined infinite-degree statement carries the
relative marker.

## Validation of the marker supplement

The added general lexicographic theorem and both aggregate imports build on
Lean `v4.35.0-rc3`. The updated root audit checks 1,307 declarations; the
optional mathlib/Milliken audit checks 3,163. Both allow only `propext`,
`Classical.choice` and `Quot.sound`; the three new public lexicographic
statements use only `propext` and `Quot.sound`.

The follow-up commands and logs are in
`validation/pseudotree/verification/manuscript-markers/`. The earlier
validation record remains a historical snapshot of the original complete
chain-degree validation.
