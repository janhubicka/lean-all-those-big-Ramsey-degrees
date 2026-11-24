import PseudotreeValidation.MixedDense
import PseudotreeValidation.MixedExtension
import PseudotreeValidation.MixedStabilization

/-!
# The mixed ray-preserving product theorem

The selected matrix handles the incoming `1` edges of the ternary factor.
Its other edges use binary padding, where the already proved stabilization
transfers the colour from the preceding level. Finite-prefix completion and
coherent fusion assemble the actual synchronized monochromatic maps.
-/

namespace AllThoseBigRamsey.Pseudotree.Mixed

open RayEmbeddings

/-- One matrix successor extends the actual finite monochromatic embedding.
The stability argument is used only for the two binary ternary-factor edges. -/
theorem good_successor {m : ℕ} {κ : Type} {colour : Tuple m → κ}
    {base : Tuple m} {c : κ} {r : ℕ} {F : Embedding m}
    (hstable : RayStable colour) (hF : Good colour base c r F)
    (N : NextLevel colour c F r) :
    ∃ G : Embedding m, Good colour base c (r + 1) G ∧ FixesThrough F G r := by
  obtain ⟨G, hfix, hnext, hnewlevel, holdlevel⟩ :=
    extend_level F r N.level N.gt N.next N.length N.step
  refine ⟨G, ⟨?_, ?_⟩, hfix⟩
  · intro i
    rw [hfix i [] (by simp)]
    exact hF.1 i
  · intro k hk x hx
    by_cases hkr : k ≤ r
    · have heq : G.applyTuple x = F.applyTuple x := by
        funext i
        exact hfix i (x i) (by rw [hx.1]; exact hkr)
      change colour (G.applyTuple x) = c
      rw [heq]
      exact hF.2 k hkr x hx
    · have hk' : k = r + 1 := by omega
      subst k
      have hne (i : Fin (m + 1)) : x i ≠ [] := by
        intro h
        have hlen := hx.1 i
        simp [h] at hlen
      let parent : Tuple m := fun i => (x i).take r
      let letter (i : Fin (m + 1)) : Fin 3 := (x i).getLast (hne i)
      have hparent : AdmissibleAt m r parent := admissible_take hx (Nat.le_succ r)
      have hsplit (i : Fin (m + 1)) : parent i ++ [letter i] = x i := by
        change (x i).take r ++ [(x i).getLast (hne i)] = x i
        rw [List.take_eq_dropLast (hx.1 i).symm]
        exact List.dropLast_append_getLast (hne i)
      have hmap (i : Fin (m + 1)) :
          (G.maps i).map (x i) = N.next i (parent i) (letter i) := by
        calc
          (G.maps i).map (x i) = (G.maps i).map (parent i ++ [letter i]) :=
            congrArg (G.maps i).map (hsplit i).symm
          _ = N.next i (parent i) (letter i) := hnext i _ _ (hparent.1 i)
      by_cases ha : letter (Fin.last m) = 1
      · apply N.monochrome (G.applyTuple x)
        intro i
        change (G.maps i).map (x i) ∈ N.matrix i
        rw [hmap]
        apply N.selected i _ _ (hparent.1 i)
        by_cases hi : i = Fin.last m
        · simpa [NeedsMatrix, hi] using ha
        · simpa only [NeedsMatrix, hi, ↓reduceIte, hsplit] using hx.2 i hi
      · have hnot : ¬NeedsMatrix (Fin.last m) (parent (Fin.last m)) (letter (Fin.last m)) := by
          simpa only [NeedsMatrix, ↓reduceIte] using ha
        have hlast : (G.applyTuple x (Fin.last m)) =
            (F.maps (Fin.last m)).map (parent (Fin.last m)) ++ letter (Fin.last m) ::
              List.replicate (N.level - F.level r - 1) 0 := by
          change (G.maps (Fin.last m)).map (x (Fin.last m)) = _
          rw [hmap, N.unselected _ _ _ (hparent.1 _) hnot]
        have hlenparent : ((F.maps (Fin.last m)).map (parent (Fin.last m))).length =
            F.level r := by rw [F.length_map, hparent.1]
        have hb : Binary ((G.applyTuple x (Fin.last m)).drop (F.level r)) := by
          rw [hlast, List.drop_left' hlenparent]
          apply (binary_cons _ _).mpr
          refine ⟨ha, ?_⟩
          intro a hmem
          have heq : a = 0 := List.eq_of_mem_replicate hmem
          subst a
          decide
        have hy : AdmissibleAt m N.level (G.applyTuple x) := by
          simpa only [hnewlevel] using G.admissible_image hx
        have hcolour := hstable (F.level r) N.level N.gt.le (G.applyTuple x) hy hb
        have htruncate :
            (fun i => (G.applyTuple x i).take (F.level r)) = F.applyTuple parent := by
          funext i
          have h := G.map_take i (x i) r (by rw [hx.1]; omega)
          rw [holdlevel r (Nat.le_refl _)] at h
          change (G.maps i).map (parent i) = _ at h
          rw [hfix i (parent i) (hparent.1 i).le] at h
          exact h.symm
        change colour (G.applyTuple x) = c
        rw [hcolour, htruncate]
        exact hF.2 r (Nat.le_refl _) parent hparent

/-- The entire dense-matrix construction after stabilization, with all
successive extensions supplied by the proved matrix theorem. -/
theorem monochromatic_of_rayStable {m n : ℕ} (colour : Tuple m → Fin (n + 1))
    (hstable : RayStable colour) :
    ∃ c : Fin (n + 1), ∃ F : Embedding m, Monochromatic colour F c := by
  obtain ⟨base, c, hD⟩ := exists_denseInput m n colour
  obtain ⟨F, hF⟩ := monochromatic_of_successive_steps colour c
    (Good colour base c) (dense_initial hD)
    (by
      intro r F hF
      obtain ⟨N⟩ := exists_nextLevel hD hF
      exact good_successor hstable hF N)
    (fun _ _ h => h.2)
  exact ⟨c, F, hF⟩

/-- The manuscript's mixed product theorem: any number of binary factors
and one ternary factor have synchronized monochromatic strong maps, with
the ternary map preserving every pseudotree ray. -/
theorem mixed_product {m n : ℕ} (colour : Tuple m → Fin (n + 1)) :
    ∃ c : Fin (n + 1), ∃ F : Embedding m, Monochromatic colour F c := by
  obtain ⟨S, hS⟩ := exists_rayStable_embedding colour
  obtain ⟨c, G, hG⟩ := monochromatic_of_rayStable (induced colour S) hS
  exact ⟨c, S.comp G, hG⟩

end AllThoseBigRamsey.Pseudotree.Mixed
