import PseudotreeValidation.DegreeAssembly
import PseudotreeValidation.SparseExtraction
import PseudotreeValidation.DiaryRecovery

/-! The paper's chain-degree endpoints in the repository's original API. -/

namespace AllThoseBigRamsey.Pseudotree

/-- The complete positive upper bound for every nonempty finite chain. -/
theorem chain_upper_bound (n : Nat) (hn : 0 < n) :
    BigRamseyBound (RepoBridge.model (Fin n)) (RepoBridge.model TernaryModel)
      (diaryCount true n 1) :=
  (RepoBridge.bound_iff (Fin n) _).mpr
    (DegreeAssembly.chain_bound_of_representations
      (fun e => SparseExtraction.sparse_copy_representation hn e))

/-- The exact big Ramsey degree of every nonempty finite chain is the number
of literal chain diaries in the manuscript. Both the upper bound and its
minimality use the repository's original definition of big Ramsey degree. -/
theorem chain_degree (n : Nat) (hn : 0 < n) :
    IsBigRamseyDegree (RepoBridge.model (Fin n)) (RepoBridge.model TernaryModel)
      (some (diaryCount true n 1)) :=
  DegreeAssembly.exact_degree_of_representations hn
    (fun e => SparseExtraction.sparse_copy_representation hn e)
    (fun D E d e h => DiaryRecovery.embeddedChain_unique D E d e h)

/-- The same exact degree stated as the cardinality of the independently
defined finite-set diaries, matching the manuscript's notation `Dₙ`. -/
theorem chain_degree_diaries (n : Nat) (hn : 0 < n) :
    IsBigRamseyDegree (RepoBridge.model (Fin n)) (RepoBridge.model TernaryModel)
      (some (Fintype.card (PaperDiary n))) := by
  rw [paperDiary_card]
  exact chain_degree n hn

end AllThoseBigRamsey.Pseudotree
