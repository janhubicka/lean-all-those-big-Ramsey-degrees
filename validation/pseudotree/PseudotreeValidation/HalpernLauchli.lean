import PseudotreeValidation.DenseMatrices

/-!
# Existing Halpern–Läuchli inputs for the pseudotree note

This module imports the proved theorem from `lean-milliken`; it does not
postulate another tree Ramsey theorem. The result below permits the finite index sets of binary rays used in
the stabilization argument. The imported companion module proves the
finite-colour dense-level-matrix formulation from the existing binary HL
proof, with an explicit arbitrarily-high supporting level.

These are ordinary tree-theorem inputs. The ray-preserving mixed product
lemma, its fusion argument, and the diary upper bound remain separate
application-specific statements, and are not asserted by this module.
-/

namespace AllThoseBigRamsey.Pseudotree

open Milliken Milliken.GeneralTree

/-- The checked finite-colour product theorem, reindexed by any finite type.
The factors must share their selected ambient-level function. -/
theorem finiteIndexedProductHL
    (U : AmbientTree) (I : Type) [Fintype I]
    (colors : ℕ) [NeZero colors]
    (P : I → StrongSubtree U) (L : ℕ → ℕ)
    (hP : ∀ i, (P i).levels = L)
    (colour : (I → U) → Fin colors) :
    ∃ c : Fin colors, ∃ M : ℕ → ℕ,
      ∃ F : I → StrongSubtree U,
        StrictMono M ∧
        (∀ i, (F i).Refines (P i) ∧ (F i).levels = M) ∧
        ∀ k (x : I → U),
          (∀ i, x i ∈ (F i).sourceLevel k) → colour x = c := by
  classical
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let P' : Fin (Fintype.card I) → StrongSubtree U := fun i => P (e i)
  let colour' : (Fin (Fintype.card I) → U) → Fin colors :=
    fun x => colour (fun i => x (e.symm i))
  obtain ⟨c, M, F, hM, hF, hmono⟩ :=
    generalProductHL_unconditional U
      (Fintype.card I) colors P' L (fun i => hP (e i)) colour'
  refine ⟨c, M, (fun i => F (e.symm i)), hM, ?_, ?_⟩
  · intro i
    obtain ⟨href, hlevels⟩ := hF (e.symm i)
    exact ⟨by simpa only [P', e.apply_symm_apply] using href, hlevels⟩
  · intro k x hx
    have hnodes : ∀ i, x (e i) ∈ (F i).sourceLevel k := by
      intro i
      simpa only [e.symm_apply_apply] using hx (e i)
    have h := hmono k (fun i => x (e i)) hnodes
    change colour (fun i => x (e (e.symm i))) = c at h
    simpa only [e.apply_symm_apply] using h

end AllThoseBigRamsey.Pseudotree
