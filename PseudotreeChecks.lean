import AllThoseBigRamsey.Pseudotree
import Lean

/-! Proof-dependency checks for the pseudotree Lean/Std core.
The optional mathlib/Milliken package has its own `Checks.lean`.
-/

#print axioms AllThoseBigRamsey.Pseudotree.wordBelow_trans
#print axioms AllThoseBigRamsey.Pseudotree.word_predecessors_comparable
#print axioms AllThoseBigRamsey.Pseudotree.wordBelow_meet_iff
#print axioms AllThoseBigRamsey.Pseudotree.binary_no_endpoints
#print axioms AllThoseBigRamsey.Pseudotree.binary_dense
#print axioms AllThoseBigRamsey.Pseudotree.parse_print
#print axioms AllThoseBigRamsey.Pseudotree.print_parse
#print axioms AllThoseBigRamsey.Pseudotree.prefix_chain_regression
#print axioms AllThoseBigRamsey.Pseudotree.Oscillation.all_oscillations
#print axioms AllThoseBigRamsey.Pseudotree.Oscillation.oscillation_le_one_of_subset
#print axioms AllThoseBigRamsey.Pseudotree.residue_cover_bound
#print axioms AllThoseBigRamsey.Pseudotree.exact_degree_of_types
#print axioms AllThoseBigRamsey.Pseudotree.Diary.chain_height_bound
#print axioms AllThoseBigRamsey.Pseudotree.longestDiary_levels
#print axioms AllThoseBigRamsey.Pseudotree.diaryEnum_complete
#print axioms AllThoseBigRamsey.Pseudotree.diaryEnum_nodup
#print axioms AllThoseBigRamsey.Pseudotree.diary_cardinality
#print axioms AllThoseBigRamsey.Pseudotree.diaryCount_first_five
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toTree_prefix_closed
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toTree_coding_count
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toTree_one_per_level
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toTree_nodes_iff_prefix_code
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toTree_one_original
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toTree_codes_increasing
#print axioms AllThoseBigRamsey.Pseudotree.literalCodes_distinct_first_three
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toTree_codes_ext_injective
#print axioms AllThoseBigRamsey.Pseudotree.literalCodes_nodup
#print axioms AllThoseBigRamsey.Pseudotree.literalCodes_length
#print axioms AllThoseBigRamsey.Pseudotree.diary_of_events_unique
#print axioms AllThoseBigRamsey.Pseudotree.Diary.toLiteral_surjective
#print axioms AllThoseBigRamsey.Pseudotree.literalDiary_cardinality
#print axioms AllThoseBigRamsey.Pseudotree.RayEmbeddings.RayStrongMap.injective
#print axioms AllThoseBigRamsey.Pseudotree.RayEmbeddings.RayStrongMap.comp
#print axioms AllThoseBigRamsey.Pseudotree.RayEmbeddings.RayStrongMap.fusion_factors
#print axioms AllThoseBigRamsey.Pseudotree.RayEmbeddings.two_ternary_obstruction
#print axioms AllThoseBigRamsey.Pseudotree.RayMapModel.act_wordBelow
#print axioms AllThoseBigRamsey.Pseudotree.RayMapModel.act_wordMeet
#print axioms AllThoseBigRamsey.Pseudotree.RayMapModel.act_injective
#print axioms AllThoseBigRamsey.Pseudotree.RayEmbeddings.finite_completion
#print axioms AllThoseBigRamsey.Pseudotree.RayEmbeddings.finite_boundary_grafting
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.stage_lengths
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.stage_origins
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.code_length
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.code_injective
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.every_active_eventually_coded
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.sparse_meet_closed
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.code_meet
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.queued_binary_code
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.child_binary_code
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.active_nodup
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.code_prefix_one
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.sparse_dense
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.sparse_no_endpoints
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.sparse_fork
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.inTree_iff_active_prefix
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.inTree_one_parent
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.critical_children
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.inSparse_at_level
#print axioms AllThoseBigRamsey.Pseudotree.Sparse.fork_unique

-- Audit all declarations in the new namespace, including their transitive
-- imported dependencies, rather than only the named endpoints above.
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
