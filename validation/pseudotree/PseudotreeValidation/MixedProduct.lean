import PseudotreeValidation.MixedDenseFinish

/-! The mixed theorem for colourings defined only on the actual level product. -/

namespace AllThoseBigRamsey.Pseudotree.Mixed

/-- A tuple in the actual level product: its coordinates have one common
length, and all but the last coordinate are binary words. -/
abbrev LevelTuple (m : ℕ) := {x : Tuple m // ∃ n, AdmissibleAt m n x}

def Embedding.onLevelTuple {m : ℕ} (F : Embedding m) (x : LevelTuple m) : LevelTuple m :=
  ⟨F.applyTuple x.val, by
    obtain ⟨n, hx⟩ := x.property
    exact ⟨F.level n, F.admissible_image hx⟩⟩

/-- No arbitrary off-domain colouring values are needed in the public
statement. The proof extends the colouring outside the level product by a
fixed colour, then restricts the checked mixed theorem back to its domain. -/
theorem mixed_level_product {m n : ℕ} (colour : LevelTuple m → Fin (n + 1)) :
    ∃ c : Fin (n + 1), ∃ F : Embedding m,
      ∀ x : LevelTuple m, colour (F.onLevelTuple x) = c := by
  classical
  let lift (x : Tuple m) : Fin (n + 1) :=
    if hx : ∃ k, AdmissibleAt m k x then colour ⟨x, hx⟩ else 0
  obtain ⟨c, F, hF⟩ := mixed_product lift
  refine ⟨c, F, ?_⟩
  intro x
  obtain ⟨k, hx⟩ := x.property
  have h := hF k x.val hx
  have hvalid : ∃ k, AdmissibleAt m k (F.applyTuple x.val) := (F.onLevelTuple x).property
  change lift (F.applyTuple x.val) = c at h
  simpa only [lift, dite_eq_left hvalid, Embedding.onLevelTuple] using h

end AllThoseBigRamsey.Pseudotree.Mixed
