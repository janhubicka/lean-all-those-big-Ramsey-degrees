import PseudotreeValidation
import Lean

-- The two substantive tree Ramsey inputs are imported with proofs.
#print axioms Milliken.GeneralTree.generalProductHL_unconditional
#print axioms Milliken.GeneralTree.heterogeneousHDHL_unconditional

-- Finite-colour density, arbitrary finite demands, and actual word factors.
#print axioms AllThoseBigRamsey.Pseudotree.finiteColourSparseHL
#print axioms AllThoseBigRamsey.Pseudotree.finiteColourFixedBase
#print axioms AllThoseBigRamsey.Pseudotree.finiteColourDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.finiteDemandDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.finiteIndexedProductHL
#print axioms AllThoseBigRamsey.Pseudotree.heterogeneousFiniteDemandDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.level_eq_length
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.binary_place_range
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.ternary_place_range
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.wordFiniteDemandDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.binaryTernaryFiniteDemandDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.rayConeDenseMatrices
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.wordStrongProductHL
#print axioms AllThoseBigRamsey.Pseudotree.WordTrees.rayConeStrongMapsHL
#print axioms AllThoseBigRamsey.Pseudotree.Mixed.exists_rayStable_embedding
#print axioms AllThoseBigRamsey.Pseudotree.Mixed.mixed_product
#print axioms AllThoseBigRamsey.Pseudotree.Mixed.mixed_level_product
#print axioms AllThoseBigRamsey.Pseudotree.RayMilliken.restricted_milliken
#print axioms AllThoseBigRamsey.Pseudotree.DiaryCanonization.simultaneous
#print axioms AllThoseBigRamsey.Pseudotree.PaperDiary.represented
#print axioms AllThoseBigRamsey.Pseudotree.Diary.paper_axioms
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toPaper_injective
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toPaper_surjective
#print axioms AllThoseBigRamsey.Pseudotree.paperDiary_card

-- Identification of the literal ternary model and its finite extensions.
#print axioms AllThoseBigRamsey.Pseudotree.BinaryRay.nonempty_orderIso_rat
#print axioms AllThoseBigRamsey.Pseudotree.wordEquiv
#print axioms AllThoseBigRamsey.Pseudotree.wordBelow_iff_toBlocks_le
#print axioms AllThoseBigRamsey.Pseudotree.toBlocks_wordMeet
#print axioms AllThoseBigRamsey.Pseudotree.wordBelow_prefix_incomparable_lex
#print axioms AllThoseBigRamsey.Pseudotree.ternaryModel_two_cones
#print axioms AllThoseBigRamsey.Pseudotree.extend_finite
#print axioms AllThoseBigRamsey.Pseudotree.finite_universal
#print axioms AllThoseBigRamsey.Pseudotree.RayTree.isUltrahomogeneous
#print axioms AllThoseBigRamsey.Pseudotree.RayTree.age_eq_finiteBinaryClass
#print axioms AllThoseBigRamsey.Pseudotree.ternaryModel_isFraisseLimit
#print axioms AllThoseBigRamsey.Pseudotree.ternaryModel_unique
#print axioms AllThoseBigRamsey.Pseudotree.RayMapModel.embedding
#print axioms AllThoseBigRamsey.Pseudotree.RayMapModel.embedding_apply_word

-- The actual sparse model, normalization, and realization in every subcopy.
#print axioms AllThoseBigRamsey.Pseudotree.SparseModel.isFraisseLimit
#print axioms AllThoseBigRamsey.Pseudotree.SparseModel.selfEmbedding_range
#print axioms AllThoseBigRamsey.Pseudotree.SparseNormalization.normalized_axioms
#print axioms AllThoseBigRamsey.Pseudotree.SparseNormalization.extraction
#print axioms AllThoseBigRamsey.Pseudotree.SparseExtraction.sparse_copy_representation
#print axioms AllThoseBigRamsey.Pseudotree.LowerRealization.sparse_chain_realization
#print axioms AllThoseBigRamsey.Pseudotree.DiaryRecovery.codes_source
#print axioms AllThoseBigRamsey.Pseudotree.DiaryRecovery.image_recovery
#print axioms AllThoseBigRamsey.Pseudotree.DiaryRecovery.embeddedChain_unique

-- The incomparable-pair argument and transfer to every finite such structure.
#print axioms AllThoseBigRamsey.Pseudotree.Incomparables.every_oscillation
#print axioms AllThoseBigRamsey.Pseudotree.Incomparables.every_pairColour
#print axioms AllThoseBigRamsey.Pseudotree.Incomparables.extend_incomparable_pair
#print axioms AllThoseBigRamsey.Pseudotree.Incomparables.arbitrarily_many_copy_colours
#print axioms AllThoseBigRamsey.Pseudotree.Incomparables.no_finite_bound
#print axioms AllThoseBigRamsey.Pseudotree.GenericIncomparables.arbitrarily_many_copy_colours
#print axioms AllThoseBigRamsey.Pseudotree.GenericIncomparables.no_finite_bound_of_countable

-- Endpoints in the original repository API, with no representation,
-- canonization, realization, or diary uniqueness assumptions remaining.
#print axioms AllThoseBigRamsey.Pseudotree.RepoBridge.bound_iff
#print axioms AllThoseBigRamsey.Pseudotree.RepoBridge.incomparable_degree_infinite
#print axioms AllThoseBigRamsey.Pseudotree.RepoBridge.singleton_degree
#print axioms AllThoseBigRamsey.Pseudotree.chain_upper_bound
#print axioms AllThoseBigRamsey.Pseudotree.chain_degree
#print axioms AllThoseBigRamsey.Pseudotree.chain_degree_diaries

-- Check all declarations in the manuscript namespace, with transitive
-- dependency collection through mathlib and the tree Ramsey libraries.
run_cmd do
  let env ← Lean.getEnv
  let allowed : List Lean.Name := [`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    if `AllThoseBigRamsey.Pseudotree |>.isPrefixOf name then
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      checked := checked + 1
  Lean.logInfo m!"Audited {checked} pseudotree declarations: only standard axioms."
