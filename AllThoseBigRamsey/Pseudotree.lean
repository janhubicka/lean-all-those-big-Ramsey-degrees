import AllThoseBigRamsey.Pseudotree.Model
import AllThoseBigRamsey.Pseudotree.Words
import AllThoseBigRamsey.Pseudotree.Oscillation
import AllThoseBigRamsey.Pseudotree.DegreeTransfer
import AllThoseBigRamsey.Pseudotree.DiaryCounts
import AllThoseBigRamsey.Pseudotree.DiaryTrees
import AllThoseBigRamsey.Pseudotree.DiaryInjective
import AllThoseBigRamsey.Pseudotree.DiaryComplete
import AllThoseBigRamsey.Pseudotree.DiaryLiteral
import AllThoseBigRamsey.Pseudotree.RayEmbeddings
import AllThoseBigRamsey.Pseudotree.RayObstruction
import AllThoseBigRamsey.Pseudotree.RayMapModel
import AllThoseBigRamsey.Pseudotree.RayExtension
import AllThoseBigRamsey.Pseudotree.RayGrafting
import AllThoseBigRamsey.Pseudotree.Sparse
import AllThoseBigRamsey.Pseudotree.SparseMeet
import AllThoseBigRamsey.Pseudotree.SparseFair
import AllThoseBigRamsey.Pseudotree.SparseShape
import AllThoseBigRamsey.Pseudotree.SparseOrder
import AllThoseBigRamsey.Pseudotree.SparseTree
import AllThoseBigRamsey.Pseudotree.SparseFrontier

/-!
# Pseudotree audit: Lean/Std core

This module exports the checked structural and combinatorial parts of the
pseudotree manuscript. The optional package `validation/pseudotree` adds
mathlib model theory and the proved Halpern–Läuchli theorem from `lean-milliken`.
See `docs/Pseudotree-Audit.md` for the exact coverage and remaining obligations.
-/
